//===- AddressSanitizer.cpp - memory error detector -----------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file is a part of AddressSanitizer, an address sanity checker.
// Details of the algorithm:
//  https://github.com/google/sanitizers/wiki/AddressSanitizerAlgorithm
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Instrumentation/FastAddressSanitizer.h"
#include "llvm/ADT/ArrayRef.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/ADT/Triple.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Analysis/BasicAliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/BinaryFormat/MachO.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Attributes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Comdat.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InlineAsm.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/Verifier.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"
#include "llvm/MC/MCSectionMachO.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ASanStackFrameLayout.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/LoopSimplify.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Support/LowLevelTypeImpl.h"
#include "llvm/CodeGen/Analysis.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <limits>
#include <memory>
#include <sstream>
#include <string>
#include <tuple>


using namespace llvm;

#define DEBUG_TYPE "fastasan"
#define INVALID_OFFSET (-0xFFFFFFFLL)

static const uint64_t kDefaultShadowScale = 3;
static const uint64_t kDefaultShadowOffset32 = 1ULL << 29;
static const uint64_t kDefaultShadowOffset64 = 1ULL << 44;
static const uint64_t kDynamicShadowSentinel =
    std::numeric_limits<uint64_t>::max();
static const uint64_t kSmallX86_64ShadowOffsetBase = 0x7FFFFFFF;  // < 2G.
static const uint64_t kSmallX86_64ShadowOffsetAlignMask = ~0xFFFULL;
static const uint64_t kLinuxKasan_ShadowOffset64 = 0xdffffc0000000000;
static const uint64_t kPPC64_ShadowOffset64 = 1ULL << 44;
static const uint64_t kSystemZ_ShadowOffset64 = 1ULL << 52;
static const uint64_t kMIPS32_ShadowOffset32 = 0x0aaa0000;
static const uint64_t kMIPS64_ShadowOffset64 = 1ULL << 37;
static const uint64_t kAArch64_ShadowOffset64 = 1ULL << 36;
static const uint64_t kFreeBSD_ShadowOffset32 = 1ULL << 30;
static const uint64_t kFreeBSD_ShadowOffset64 = 1ULL << 46;
static const uint64_t kNetBSD_ShadowOffset32 = 1ULL << 30;
static const uint64_t kNetBSD_ShadowOffset64 = 1ULL << 46;
static const uint64_t kNetBSDKasan_ShadowOffset64 = 0xdfff900000000000;
static const uint64_t kPS4CPU_ShadowOffset64 = 1ULL << 40;
static const uint64_t kWindowsShadowOffset32 = 3ULL << 28;
static const uint64_t kEmscriptenShadowOffset = 0;

static const uint64_t kMyriadShadowScale = 5;
static const uint64_t kMyriadMemoryOffset32 = 0x80000000ULL;
static const uint64_t kMyriadMemorySize32 = 0x20000000ULL;
static const uint64_t kMyriadTagShift = 29;
static const uint64_t kMyriadDDRTag = 4;
static const uint64_t kMyriadCacheBitMask32 = 0x40000000ULL;

// The shadow memory space is dynamically allocated.
static const uint64_t kWindowsShadowOffset64 = kDynamicShadowSentinel;

static const size_t kMinStackMallocSize = 1 << 6;   // 64B
static const size_t kMaxStackMallocSize = 1 << 16;  // 64K
static const uintptr_t kCurrentStackFrameMagic = 0x41B58AB3;
static const uintptr_t kRetiredStackFrameMagic = 0x45E0360E;

static const char *const kAsanModuleCtorName = "asan.module_ctor";
static const char *const kAsanModuleDtorName = "asan.module_dtor";
static const uint64_t kAsanCtorAndDtorPriority = 1;
// On Emscripten, the system needs more than one priorities for constructors.
static const uint64_t kAsanEmscriptenCtorAndDtorPriority = 50;
static const char *const kAsanReportErrorTemplate = "__asan_report_";
static const char *const kAsanRegisterGlobalsName = "__asan_register_globals";
static const char *const kAsanUnregisterGlobalsName =
    "__asan_unregister_globals";
static const char *const kAsanRegisterImageGlobalsName =
  "__asan_register_image_globals";
static const char *const kAsanUnregisterImageGlobalsName =
  "__asan_unregister_image_globals";
static const char *const kAsanRegisterElfGlobalsName =
  "__asan_register_elf_globals";
static const char *const kAsanUnregisterElfGlobalsName =
  "__asan_unregister_elf_globals";
static const char *const kAsanPoisonGlobalsName = "__asan_before_dynamic_init";
static const char *const kAsanUnpoisonGlobalsName = "__asan_after_dynamic_init";
static const char *const kAsanInitName = "__asan_init";
static const char *const kAsanVersionCheckNamePrefix =
    "__asan_version_mismatch_check_v";
static const char *const kAsanPtrCmp = "__sanitizer_ptr_cmp";
static const char *const kAsanPtrSub = "__sanitizer_ptr_sub";
static const char *const kAsanHandleNoReturnName = "__asan_handle_no_return";
static const int kMaxAsanStackMallocSizeClass = 10;
static const char *const kAsanStackMallocNameTemplate = "__asan_stack_malloc_";
static const char *const kAsanStackFreeNameTemplate = "__asan_stack_free_";
static const char *const kAsanGenPrefix = "___asan_gen_";
static const char *const kODRGenPrefix = "__odr_asan_gen_";
static const char *const kSanCovGenPrefix = "__sancov_gen_";
static const char *const kAsanSetShadowPrefix = "__asan_set_shadow_";
static const char *const kAsanPoisonStackMemoryName =
    "__asan_poison_stack_memory";
static const char *const kAsanUnpoisonStackMemoryName =
    "__asan_unpoison_stack_memory";

// ASan version script has __asan_* wildcard. Triple underscore prevents a
// linker (gold) warning about attempting to export a local symbol.
static const char *const kAsanGlobalsRegisteredFlagName =
    "___asan_globals_registered";

static const char *const kAsanOptionDetectUseAfterReturn =
    "__asan_option_detect_stack_use_after_return";

static const char *const kAsanShadowMemoryDynamicAddress =
    "__asan_shadow_memory_dynamic_address";

static const char *const kAsanAllocaPoison = "__asan_alloca_poison";
static const char *const kAsanAllocasUnpoison = "__asan_allocas_unpoison";

// Accesses sizes are powers of two: 1, 2, 4, 8, 16.
static const size_t kNumberOfAccessSizes = 5;

static const unsigned kAllocaRzSize = 32;

// Command-line flags.

static cl::opt<bool> ClEnableKasan(
    "fasan-kernel", cl::desc("Enable KernelAddressSanitizer instrumentation"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClRecover(
    "fasan-recover",
    cl::desc("Enable recovery mode (continue-after-error)."),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClInsertVersionCheck(
    "fasan-guard-against-version-mismatch",
    cl::desc("Guard against compiler/runtime version mismatch."),
    cl::Hidden, cl::init(true));

// This flag may need to be replaced with -f[no-]fasan-reads.
static cl::opt<bool> ClInstrumentReads("fasan-instrument-reads",
                                       cl::desc("instrument read instructions"),
                                       cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentWrites(
    "fasan-instrument-writes", cl::desc("instrument write instructions"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClInstrumentAtomics(
    "fasan-instrument-atomics",
    cl::desc("instrument atomic instructions (rmw, cmpxchg)"), cl::Hidden,
    cl::init(true));

static cl::opt<bool> ClAlwaysSlowPath(
    "fasan-always-slow-path",
    cl::desc("use instrumentation with slow path for all accesses"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClForceDynamicShadow(
    "fasan-force-dynamic-shadow",
    cl::desc("Load shadow address into a local variable for each function"),
    cl::Hidden, cl::init(false));

static cl::opt<bool>
    ClWithIfunc("fasan-with-ifunc",
                cl::desc("Access dynamic shadow through an ifunc global on "
                         "platforms that support this"),
                cl::Hidden, cl::init(true));

static cl::opt<bool> ClWithIfuncSuppressRemat(
    "fasan-with-ifunc-suppress-remat",
    cl::desc("Suppress rematerialization of dynamic shadow address by passing "
             "it through inline asm in prologue."),
    cl::Hidden, cl::init(true));

// This flag limits the number of instructions to be instrumented
// in any given BB. Normally, this should be set to unlimited (INT_MAX),
// but due to http://llvm.org/bugs/show_bug.cgi?id=12652 we temporary
// set it to 10000.
static cl::opt<int> ClMaxInsnsToInstrumentPerBB(
    "fasan-max-ins-per-bb", cl::init(10000),
    cl::desc("maximal number of instructions to instrument in any given BB"),
    cl::Hidden);

// This flag may need to be replaced with -f[no]fasan-stack.
static cl::opt<bool> ClStack("fasan-stack", cl::desc("Handle stack memory"),
                             cl::Hidden, cl::init(true));
static cl::opt<uint32_t> ClMaxInlinePoisoningSize(
    "fasan-max-inline-poisoning-size",
    cl::desc(
        "Inline shadow poisoning for blocks up to the given size in bytes."),
    cl::Hidden, cl::init(64));

static cl::opt<bool> ClUseAfterReturn("fasan-use-after-return",
                                      cl::desc("Check stack-use-after-return"),
                                      cl::Hidden, cl::init(true));

static cl::opt<bool> ClRedzoneByvalArgs("fasan-redzone-byval-args",
                                        cl::desc("Create redzones for byval "
                                                 "arguments (extra copy "
                                                 "required)"), cl::Hidden,
                                        cl::init(true));

static cl::opt<bool> ClUseAfterScope("fasan-use-after-scope",
                                     cl::desc("Check stack-use-after-scope"),
                                     cl::Hidden, cl::init(false));

// This flag may need to be replaced with -f[no]fasan-globals.
static cl::opt<bool> ClGlobals("fasan-globals",
                               cl::desc("Handle global objects"), cl::Hidden,
                               cl::init(true));

static cl::opt<bool> ClInitializers("fasan-initialization-order",
                                    cl::desc("Handle C++ initializer order"),
                                    cl::Hidden, cl::init(true));

static cl::opt<bool> ClInvalidPointerPairs(
    "fasan-detect-invalid-pointer-pair",
    cl::desc("Instrument <, <=, >, >=, - with pointer operands"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClInvalidPointerCmp(
    "fasan-detect-invalid-pointer-cmp",
    cl::desc("Instrument <, <=, >, >= with pointer operands"), cl::Hidden,
    cl::init(false));

static cl::opt<bool> ClInvalidPointerSub(
    "fasan-detect-invalid-pointer-sub",
    cl::desc("Instrument - operations with pointer operands"), cl::Hidden,
    cl::init(false));

static cl::opt<unsigned> ClRealignStack(
    "fasan-realign-stack",
    cl::desc("Realign stack to the value of this flag (power of two)"),
    cl::Hidden, cl::init(32));

static cl::opt<int> ClInstrumentationWithCallsThreshold(
    "fasan-instrumentation-with-call-threshold",
    cl::desc(
        "If the function being instrumented contains more than "
        "this number of memory accesses, use callbacks instead of "
        "inline checks (-1 means never use callbacks)."),
    cl::Hidden, cl::init(7000));

static cl::opt<std::string> ClMemoryAccessCallbackPrefix(
    "fasan-memory-access-callback-prefix",
    cl::desc("Prefix for memory access callbacks"), cl::Hidden,
    cl::init("__asan_"));

static cl::opt<bool>
    ClInstrumentDynamicAllocas("fasan-instrument-dynamic-allocas",
                               cl::desc("instrument dynamic allocas"),
                               cl::Hidden, cl::init(true));

static cl::opt<bool> ClSkipPromotableAllocas(
    "fasan-skip-promotable-allocas",
    cl::desc("Do not instrument promotable allocas"), cl::Hidden,
    cl::init(true));

// These flags allow to change the shadow mapping.
// The shadow mapping looks like
//    Shadow = (Mem >> scale) + offset

static cl::opt<int> ClMappingScale("fasan-mapping-scale",
                                   cl::desc("scale of asan shadow mapping"),
                                   cl::Hidden, cl::init(0));

static cl::opt<uint64_t>
    ClMappingOffset("fasan-mapping-offset",
                    cl::desc("offset of asan shadow mapping [EXPERIMENTAL]"),
                    cl::Hidden, cl::init(0));

// Optimization flags. Not user visible, used mostly for testing
// and benchmarking the tool.

static cl::opt<bool> ClOpt("fasan-opt", cl::desc("Optimize instrumentation"),
                           cl::Hidden, cl::init(true));

static cl::opt<bool> ClOptSameTemp(
    "fasan-opt-same-temp", cl::desc("Instrument the same temp just once"),
    cl::Hidden, cl::init(true));

static cl::opt<bool> ClOptGlobals("fasan-opt-globals",
                                  cl::desc("Don't instrument scalar globals"),
                                  cl::Hidden, cl::init(true));

static cl::opt<bool> ClOptStack(
    "fasan-opt-stack", cl::desc("Don't instrument scalar stack variables"),
    cl::Hidden, cl::init(false));

static cl::opt<bool> ClDynamicAllocaStack(
    "fasan-stack-dynamic-alloca",
    cl::desc("Use dynamic alloca to represent stack variables"), cl::Hidden,
    cl::init(true));

static cl::opt<uint32_t> ClForceExperiment(
    "fasan-force-experiment",
    cl::desc("Force optimization experiment (for testing)"), cl::Hidden,
    cl::init(0));

static cl::opt<bool>
    ClUsePrivateAlias("fasan-use-private-alias",
                      cl::desc("Use private aliases for global variables"),
                      cl::Hidden, cl::init(false));

static cl::opt<bool>
    ClUseOdrIndicator("fasan-use-odr-indicator",
                      cl::desc("Use odr indicators to improve ODR reporting"),
                      cl::Hidden, cl::init(false));

static cl::opt<bool>
    ClUseGlobalsGC("fasan-globals-live-support",
                   cl::desc("Use linker features to support dead "
                            "code stripping of globals"),
                   cl::Hidden, cl::init(true));

// This is on by default even though there is a bug in gold:
// https://sourceware.org/bugzilla/show_bug.cgi?id=19002
static cl::opt<bool>
    ClWithComdat("fasan-with-comdat",
                 cl::desc("Place ASan constructors in comdat sections"),
                 cl::Hidden, cl::init(true));

// Debug flags.

static cl::opt<int> ClDebug("fasan-debug", cl::desc("debug"), cl::Hidden,
                            cl::init(0));

static cl::opt<int> ClDebugStack("fasan-debug-stack", cl::desc("debug stack"),
                                 cl::Hidden, cl::init(0));

static cl::opt<std::string> ClDebugFunc("fasan-debug-func", cl::Hidden,
                                        cl::desc("Debug func"));

static cl::opt<int> ClDebugMin("fasan-debug-min", cl::desc("Debug min inst"),
                               cl::Hidden, cl::init(-1));

static cl::opt<int> ClDebugMax("fasan-debug-max", cl::desc("Debug max inst"),
                               cl::Hidden, cl::init(-1));

STATISTIC(NumInstrumentedReads, "Number of instrumented reads");
STATISTIC(NumInstrumentedWrites, "Number of instrumented writes");
STATISTIC(NumOptimizedAccessesToGlobalVar,
          "Number of optimized accesses to global vars");
STATISTIC(NumOptimizedAccessesToStackVar,
          "Number of optimized accesses to stack vars");

namespace {

/// This struct defines the shadow mapping using the rule:
///   shadow = (mem >> Scale) ADD-or-OR Offset.
/// If InGlobal is true, then
///   extern char __asan_shadow[];
///   shadow = (mem >> Scale) + &__asan_shadow
struct ShadowMapping {
  int Scale;
  uint64_t Offset;
  bool OrShadowOffset;
  bool InGlobal;
};

} // end anonymous namespace

static ShadowMapping getShadowMapping(Triple &TargetTriple, int LongSize,
                                      bool IsKasan) {
  bool IsAndroid = TargetTriple.isAndroid();
  bool IsIOS = TargetTriple.isiOS() || TargetTriple.isWatchOS();
  bool IsFreeBSD = TargetTriple.isOSFreeBSD();
  bool IsNetBSD = TargetTriple.isOSNetBSD();
  bool IsPS4CPU = TargetTriple.isPS4CPU();
  bool IsLinux = TargetTriple.isOSLinux();
  bool IsPPC64 = TargetTriple.getArch() == Triple::ppc64 ||
                 TargetTriple.getArch() == Triple::ppc64le;
  bool IsSystemZ = TargetTriple.getArch() == Triple::systemz;
  bool IsX86_64 = TargetTriple.getArch() == Triple::x86_64;
  bool IsMIPS32 = TargetTriple.isMIPS32();
  bool IsMIPS64 = TargetTriple.isMIPS64();
  bool IsArmOrThumb = TargetTriple.isARM() || TargetTriple.isThumb();
  bool IsAArch64 = TargetTriple.getArch() == Triple::aarch64;
  bool IsWindows = TargetTriple.isOSWindows();
  bool IsFuchsia = TargetTriple.isOSFuchsia();
  bool IsMyriad = TargetTriple.getVendor() == llvm::Triple::Myriad;
  bool IsEmscripten = TargetTriple.isOSEmscripten();

  ShadowMapping Mapping;

  Mapping.Scale = IsMyriad ? kMyriadShadowScale : kDefaultShadowScale;
  if (ClMappingScale.getNumOccurrences() > 0) {
    Mapping.Scale = ClMappingScale;
  }

  if (LongSize == 32) {
    if (IsAndroid)
      Mapping.Offset = kDynamicShadowSentinel;
    else if (IsMIPS32)
      Mapping.Offset = kMIPS32_ShadowOffset32;
    else if (IsFreeBSD)
      Mapping.Offset = kFreeBSD_ShadowOffset32;
    else if (IsNetBSD)
      Mapping.Offset = kNetBSD_ShadowOffset32;
    else if (IsIOS)
      Mapping.Offset = kDynamicShadowSentinel;
    else if (IsWindows)
      Mapping.Offset = kWindowsShadowOffset32;
    else if (IsEmscripten)
      Mapping.Offset = kEmscriptenShadowOffset;
    else if (IsMyriad) {
      uint64_t ShadowOffset = (kMyriadMemoryOffset32 + kMyriadMemorySize32 -
                               (kMyriadMemorySize32 >> Mapping.Scale));
      Mapping.Offset = ShadowOffset - (kMyriadMemoryOffset32 >> Mapping.Scale);
    }
    else
      Mapping.Offset = kDefaultShadowOffset32;
  } else {  // LongSize == 64
    // Fuchsia is always PIE, which means that the beginning of the address
    // space is always available.
    if (IsFuchsia)
      Mapping.Offset = 0;
    else if (IsPPC64)
      Mapping.Offset = kPPC64_ShadowOffset64;
    else if (IsSystemZ)
      Mapping.Offset = kSystemZ_ShadowOffset64;
    else if (IsFreeBSD && !IsMIPS64)
      Mapping.Offset = kFreeBSD_ShadowOffset64;
    else if (IsNetBSD) {
      if (IsKasan)
        Mapping.Offset = kNetBSDKasan_ShadowOffset64;
      else
        Mapping.Offset = kNetBSD_ShadowOffset64;
    } else if (IsPS4CPU)
      Mapping.Offset = kPS4CPU_ShadowOffset64;
    else if (IsLinux && IsX86_64) {
      if (IsKasan)
        Mapping.Offset = kLinuxKasan_ShadowOffset64;
      else
        Mapping.Offset = (kSmallX86_64ShadowOffsetBase &
                          (kSmallX86_64ShadowOffsetAlignMask << Mapping.Scale));
    } else if (IsWindows && IsX86_64) {
      Mapping.Offset = kWindowsShadowOffset64;
    } else if (IsMIPS64)
      Mapping.Offset = kMIPS64_ShadowOffset64;
    else if (IsIOS)
      Mapping.Offset = kDynamicShadowSentinel;
    else if (IsAArch64)
      Mapping.Offset = kAArch64_ShadowOffset64;
    else
      Mapping.Offset = kDefaultShadowOffset64;
  }

  if (ClForceDynamicShadow) {
    Mapping.Offset = kDynamicShadowSentinel;
  }

  if (ClMappingOffset.getNumOccurrences() > 0) {
    Mapping.Offset = ClMappingOffset;
  }

  // OR-ing shadow offset if more efficient (at least on x86) if the offset
  // is a power of two, but on ppc64 we have to use add since the shadow
  // offset is not necessary 1/8-th of the address space.  On SystemZ,
  // we could OR the constant in a single instruction, but it's more
  // efficient to load it once and use indexed addressing.
  Mapping.OrShadowOffset = !IsAArch64 && !IsPPC64 && !IsSystemZ && !IsPS4CPU &&
                           !(Mapping.Offset & (Mapping.Offset - 1)) &&
                           Mapping.Offset != kDynamicShadowSentinel;
  bool IsAndroidWithIfuncSupport =
      IsAndroid && !TargetTriple.isAndroidVersionLT(21);
  Mapping.InGlobal = ClWithIfunc && IsAndroidWithIfuncSupport && IsArmOrThumb;

  return Mapping;
}

static size_t RedzoneSizeForScale(int MappingScale) {
  // Redzone used for stack and globals is at least 32 bytes.
  // For scales 6 and 7, the redzone has to be 64 and 128 bytes respectively.
  return std::max(32U, 1U << MappingScale);
}

static uint64_t GetCtorAndDtorPriority(Triple &TargetTriple) {
  if (TargetTriple.isOSEmscripten()) {
    return kAsanEmscriptenCtorAndDtorPriority;
  } else {
    return kAsanCtorAndDtorPriority;
  }
}

namespace {

/// Module analysis for getting various metadata about the module.
class ASanFastGlobalsMetadataWrapperPass : public ModulePass {
public:
  static char ID;

  ASanFastGlobalsMetadataWrapperPass() : ModulePass(ID) {
    initializeASanFastGlobalsMetadataWrapperPassPass(
        *PassRegistry::getPassRegistry());
  }

  bool runOnModule(Module &M) override {
    GlobalsMD = FastGlobalsMetadata(M);
    return false;
  }

  StringRef getPassName() const override {
    return "ASanFastGlobalsMetadataWrapperPass";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }

  FastGlobalsMetadata &getGlobalsMD() { return GlobalsMD; }

private:
  FastGlobalsMetadata GlobalsMD;
};

char ASanFastGlobalsMetadataWrapperPass::ID = 0;

/// AddressSanitizer: instrument the code in module to find memory bugs.
struct FastAddressSanitizer {
  FastAddressSanitizer(Module &M, const FastGlobalsMetadata *GlobalsMD,
                       bool CompileKernel = false, bool Recover = false,
                       bool UseAfterScope = false)
      : UseAfterScope(UseAfterScope || ClUseAfterScope), GlobalsMD(*GlobalsMD) {
    this->Recover = ClRecover.getNumOccurrences() > 0 ? ClRecover : Recover;
    this->CompileKernel =
        ClEnableKasan.getNumOccurrences() > 0 ? ClEnableKasan : CompileKernel;

    C = &(M.getContext());
    LongSize = M.getDataLayout().getPointerSizeInBits();
    IntptrTy = Type::getIntNTy(*C, LongSize);
		Int32Ty = Type::getInt32Ty(*C);
		Int64Ty = Type::getInt64Ty(*C);
		Int8Ty = Type::getInt8Ty(*C);
		Int8PtrTy = Type::getInt8PtrTy(*C);
		Int32PtrTy = Type::getInt32PtrTy(*C);
		Int64PtrTy = Type::getInt64PtrTy(*C);
    TargetTriple = Triple(M.getTargetTriple());

    Mapping = getShadowMapping(TargetTriple, LongSize, this->CompileKernel);
  }

  uint64_t getAllocaSizeInBytes(const AllocaInst &AI) const {
    uint64_t ArraySize = 1;
    if (AI.isArrayAllocation()) {
      const ConstantInt *CI = dyn_cast<ConstantInt>(AI.getArraySize());
      assert(CI && "non-constant array size");
      ArraySize = CI->getZExtValue();
    }
    Type *Ty = AI.getAllocatedType();
    uint64_t SizeInBytes =
        AI.getModule()->getDataLayout().getTypeAllocSize(Ty);
    return SizeInBytes * ArraySize;
  }

  /// Check if we want (and can) handle this alloca.
  bool isInterestingAlloca(const AllocaInst &AI);

  /// If it is an interesting memory access, return the PointerOperand
  /// and set IsWrite/Alignment. Otherwise return nullptr.
  /// MaybeMask is an output parameter for the mask Value, if we're looking at a
  /// masked load/store.
  Value *isInterestingMemoryAccess(Instruction *I, bool *IsWrite,
                                   uint64_t *TypeSize, unsigned *Alignment,
                                   Value **MaybeMask = nullptr);

  void instrumentMop(ObjectSizeOffsetVisitor &ObjSizeVis, Instruction *I,
                     bool UseCalls, const DataLayout &DL);
  void instrumentPointerComparisonOrSubtraction(Instruction *I);
  void instrumentAddress(Instruction *OrigIns, Instruction *InsertBefore,
                         Value *Addr, uint32_t TypeSize, bool IsWrite,
                         Value *SizeArgument, bool UseCalls, uint32_t Exp);
  void instrumentUnusualSizeOrAlignment(Instruction *I,
                                        Instruction *InsertBefore, Value *Addr,
                                        uint32_t TypeSize, bool IsWrite,
                                        Value *SizeArgument, bool UseCalls,
                                        uint32_t Exp);
  Value *createSlowPathCmp(IRBuilder<> &IRB, Value *AddrLong,
                           Value *ShadowValue, uint32_t TypeSize);
  Instruction *generateCrashCode(Instruction *InsertBefore, Value *Addr,
                                 bool IsWrite, size_t AccessSizeIndex,
                                 Value *SizeArgument, uint32_t Exp);
  void instrumentMemIntrinsic(MemIntrinsic *MI);
  Value *memToShadow(Value *Shadow, IRBuilder<> &IRB);
	void createInteriorFn(Function *F);
  bool instrumentFunction(Function &F, const TargetLibraryInfo *TLI, AAResults *AA, AssumptionCache *AC);
  bool instrumentFunctionNew(Function &F, const TargetLibraryInfo *TLI, AAResults *AA, AssumptionCache *AC);
	void recordAllUnsafeAccesses(Function &F, DenseSet<Value*> &UnsafeUses,
		DenseMap<Value*, uint64_t> &UnsafePointers, DenseSet<CallBase*> &CallSites,
		DenseSet<ReturnInst*> &RetSites, DenseSet<StoreInst*> &Stores,
		DenseSet<AllocaInst*> &UnsafeAllocas,
		DenseSet<Instruction*> &ICmpOrSub,
		DenseSet<Instruction*> &IntToPtr,
		DenseSet<Instruction*> &PtrToInt,
		DenseSet<Instruction*> &RestorePoints,
		DenseSet<Value*> &InteriorPointersSet,
		DenseSet<Instruction*> &GEPs,
		DenseSet<Value*> &LargerThanBase,
		DenseSet<CallInst*> &MemCalls,
		DenseSet<Instruction*> &FnPtrs,
		const TargetLibraryInfo *TLI
		);
	void patchDynamicAlloca(Function &F, AllocaInst *AI, Value *StackBase, int &RecordIndex);
	void patchStaticAlloca(Function &F, AllocaInst *AI, Value *StackBase, int &RecordIndex);
	//Value* getInterior(Function &F, Instruction *I, Value *V);
	void addBoundsCheck(Function &F, Value *Base, Value *Ptr, 
		Value *Size, Value *TySize, DenseSet<Value*> &UnsafeUses, int &callsites,
		bool MayNull);
	void addBoundsCheckWithLen(Function &F, Value *Base, Value *Ptr,
		Value *TySize,
		int &callsites, DenseSet<Value*> &GetLengths,
		DenseSet<Value*> &GetLengthsCond,
		DenseMap<Value*, Value*> &LenToBaseMap, DenseMap<Value*, Value*> &LoopUsages,
		DenseSet<Value*> &CondLoop
		);

	void addBoundsCheckWithLenAtUseHelper(Function &F, 
			Value *Base, Value *Ptr, Value *TySize, Instruction* InstPtr,
			int &callsites, Value *Limit);

	void addBoundsCheckWithLenAtUse(Function &F, 
			Value *Base, Value *Ptr, Value *TySize,
			DenseSet<Value*> &UnsafeUses,
			int &callsites, 
			DenseMap<Value*, Value*> &PtrUseToLenMap);

	bool isSafeAlloca(const AllocaInst *AllocaPtr, const TargetLibraryInfo *TLI);
  bool maybeInsertAsanInitAtFunctionEntry(Function &F);
  void maybeInsertDynamicShadowAtFunctionEntry(Function &F);
  void markEscapedLocalAllocas(Function &F);

private:
  friend struct FunctionStackPoisoner;

  void initializeCallbacks(Module &M);

  bool LooksLikeCodeInBug11395(Instruction *I);
  bool GlobalIsLinkerInitialized(GlobalVariable *G);
  bool isSafeAccess(ObjectSizeOffsetVisitor &ObjSizeVis, Value *Addr,
                    uint64_t TypeSize) const;

	//uint64_t getKnownObjSize(Value *V, const DataLayout &DL, bool &Static, const TargetLibraryInfo *TLI);
	Value *getLimit(Function &F, const Value *V, const DataLayout &DL, const TargetLibraryInfo *TLI);
	Value *getLimitSafe(Function &F, const Value *V, const DataLayout &DL, const TargetLibraryInfo *TLI);
	Value* getStaticBaseSize(Function &F, const Value *V1, const DataLayout &DL, const TargetLibraryInfo *TLI);
	void insertChecksForMemCalls(Function &F,
		DenseMap<Value*, Value*> &PtrToBaseMap,
		DenseMap<Value*, Value*> &BaseToLenMap,
		DenseMap<Value*, Value*> &LenToBaseMap,
		DenseMap<Value*, Value*> &PtrUseToLenMap,
		DenseSet<Value*> &GetLengths,
		CallInst *CI, Value *Ptr, Value *Len,
		const TargetLibraryInfo *TLI, bool After);

  /// Helper to cleanup per-function state.
  struct FunctionStateRAII {
    FastAddressSanitizer *Pass;

    FunctionStateRAII(FastAddressSanitizer *Pass) : Pass(Pass) {
      assert(Pass->ProcessedAllocas.empty() &&
             "last pass forgot to clear cache");
      assert(!Pass->LocalDynamicShadow);
    }

    ~FunctionStateRAII() {
      Pass->LocalDynamicShadow = nullptr;
      Pass->ProcessedAllocas.clear();
    }
  };

  LLVMContext *C;
  Triple TargetTriple;
  int LongSize;
  bool CompileKernel;
  bool Recover;
  bool UseAfterScope;
  Type *IntptrTy;
	Type *Int32Ty;
	Type *Int64Ty;
	Type *Int8Ty;
	Type *Int8PtrTy;
	Type *Int32PtrTy;
	Type *Int64PtrTy;
  ShadowMapping Mapping;
  FunctionCallee AsanHandleNoReturnFunc;
  FunctionCallee AsanPtrCmpFunction, AsanPtrSubFunction;
  Constant *AsanShadowGlobal;

  // These arrays is indexed by AccessIsWrite, Experiment and log2(AccessSize).
  FunctionCallee AsanErrorCallback[2][2][kNumberOfAccessSizes];
  FunctionCallee AsanMemoryAccessCallback[2][2][kNumberOfAccessSizes];

  // These arrays is indexed by AccessIsWrite and Experiment.
  FunctionCallee AsanErrorCallbackSized[2][2];
  FunctionCallee AsanMemoryAccessCallbackSized[2][2];

  FunctionCallee AsanMemmove, AsanMemcpy, AsanMemset;
  InlineAsm *EmptyAsm;
  Value *LocalDynamicShadow = nullptr;
  const FastGlobalsMetadata &GlobalsMD;
  DenseMap<const AllocaInst *, bool> ProcessedAllocas;
};

class FastAddressSanitizerLegacyPass : public FunctionPass {
public:
  static char ID;

  explicit FastAddressSanitizerLegacyPass(bool CompileKernel = false,
                                      bool Recover = false,
                                      bool UseAfterScope = false)
      : FunctionPass(ID), CompileKernel(CompileKernel), Recover(Recover),
        UseAfterScope(UseAfterScope) {
    initializeFastAddressSanitizerLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  StringRef getPassName() const override {
    return "FastAddressSanitizerFunctionPass";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ASanFastGlobalsMetadataWrapperPass>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
		AU.addRequiredTransitive<AAResultsWrapperPass>();
		AU.addRequired<AssumptionCacheTracker>();
  }

  bool runOnFunction(Function &F) override {
    FastGlobalsMetadata &GlobalsMD =
        getAnalysis<ASanFastGlobalsMetadataWrapperPass>().getGlobalsMD();
    const TargetLibraryInfo *TLI =
        &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
    FastAddressSanitizer ASan(*F.getParent(), &GlobalsMD, CompileKernel, Recover,
                          UseAfterScope);
		AAResults *AA = &getAnalysis<AAResultsWrapperPass>().getAAResults();
		auto &ACT = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
    return ASan.instrumentFunction(F, TLI, AA, &ACT);
  }

private:
  bool CompileKernel;
  bool Recover;
  bool UseAfterScope;
};

class ModuleFastAddressSanitizer {
public:
  ModuleFastAddressSanitizer(Module &M, const FastGlobalsMetadata *GlobalsMD,
                         bool CompileKernel = false, bool Recover = false,
                         bool UseGlobalsGC = true, bool UseOdrIndicator = false)
      : GlobalsMD(*GlobalsMD), UseGlobalsGC(UseGlobalsGC && ClUseGlobalsGC),
        // Enable aliases as they should have no downside with ODR indicators.
        UsePrivateAlias(UseOdrIndicator || ClUsePrivateAlias),
        UseOdrIndicator(UseOdrIndicator || ClUseOdrIndicator),
        // Not a typo: ClWithComdat is almost completely pointless without
        // ClUseGlobalsGC (because then it only works on modules without
        // globals, which are rare); it is a prerequisite for ClUseGlobalsGC;
        // and both suffer from gold PR19002 for which UseGlobalsGC constructor
        // argument is designed as workaround. Therefore, disable both
        // ClWithComdat and ClUseGlobalsGC unless the frontend says it's ok to
        // do globals-gc.
        UseCtorComdat(UseGlobalsGC && ClWithComdat) {
    this->Recover = ClRecover.getNumOccurrences() > 0 ? ClRecover : Recover;
    this->CompileKernel =
        ClEnableKasan.getNumOccurrences() > 0 ? ClEnableKasan : CompileKernel;

    C = &(M.getContext());
    int LongSize = M.getDataLayout().getPointerSizeInBits();
    IntptrTy = Type::getIntNTy(*C, LongSize);
    TargetTriple = Triple(M.getTargetTriple());
    Mapping = getShadowMapping(TargetTriple, LongSize, this->CompileKernel);
  }

  bool instrumentModule(Module &);
  bool instrumentModuleNew(Module &);

private:
  void initializeCallbacks(Module &M);

  bool InstrumentGlobals(IRBuilder<> &IRB, Module &M, bool *CtorComdat);
  void InstrumentGlobalsCOFF(IRBuilder<> &IRB, Module &M,
                             ArrayRef<GlobalVariable *> ExtendedGlobals,
                             ArrayRef<Constant *> MetadataInitializers);
  void InstrumentGlobalsELF(IRBuilder<> &IRB, Module &M,
                            ArrayRef<GlobalVariable *> ExtendedGlobals,
                            ArrayRef<Constant *> MetadataInitializers,
                            const std::string &UniqueModuleId);
  void InstrumentGlobalsMachO(IRBuilder<> &IRB, Module &M,
                              ArrayRef<GlobalVariable *> ExtendedGlobals,
                              ArrayRef<Constant *> MetadataInitializers);
  void
  InstrumentGlobalsWithMetadataArray(IRBuilder<> &IRB, Module &M,
                                     ArrayRef<GlobalVariable *> ExtendedGlobals,
                                     ArrayRef<Constant *> MetadataInitializers);

  GlobalVariable *CreateMetadataGlobal(Module &M, Constant *Initializer,
                                       StringRef OriginalName);
  void SetComdatForGlobalMetadata(GlobalVariable *G, GlobalVariable *Metadata,
                                  StringRef InternalSuffix);
  IRBuilder<> CreateAsanModuleDtor(Module &M);

  bool ShouldInstrumentGlobal(GlobalVariable *G);
  bool ShouldUseMachOGlobalsSection() const;
  StringRef getGlobalMetadataSection() const;
  void poisonOneInitializer(Function &GlobalInit, GlobalValue *ModuleName);
  void createInitializerPoisonCalls(Module &M, GlobalValue *ModuleName);
  size_t MinRedzoneSizeForGlobal() const {
    return RedzoneSizeForScale(Mapping.Scale);
  }
  int GetAsanVersion(const Module &M) const;

  const FastGlobalsMetadata &GlobalsMD;
  bool CompileKernel;
  bool Recover;
  bool UseGlobalsGC;
  bool UsePrivateAlias;
  bool UseOdrIndicator;
  bool UseCtorComdat;
  Type *IntptrTy;
  LLVMContext *C;
  Triple TargetTriple;
  ShadowMapping Mapping;
  FunctionCallee AsanPoisonGlobals;
  FunctionCallee AsanUnpoisonGlobals;
  FunctionCallee AsanRegisterGlobals;
  FunctionCallee AsanUnregisterGlobals;
  FunctionCallee AsanRegisterImageGlobals;
  FunctionCallee AsanUnregisterImageGlobals;
  FunctionCallee AsanRegisterElfGlobals;
  FunctionCallee AsanUnregisterElfGlobals;

  Function *AsanCtorFunction = nullptr;
  Function *AsanDtorFunction = nullptr;
};

class ModuleFastAddressSanitizerLegacyPass : public ModulePass {
public:
  static char ID;

  explicit ModuleFastAddressSanitizerLegacyPass(bool CompileKernel = false,
                                            bool Recover = false,
                                            bool UseGlobalGC = true,
                                            bool UseOdrIndicator = false)
      : ModulePass(ID), CompileKernel(CompileKernel), Recover(Recover),
        UseGlobalGC(UseGlobalGC), UseOdrIndicator(UseOdrIndicator) {
    initializeModuleFastAddressSanitizerLegacyPassPass(
        *PassRegistry::getPassRegistry());
  }

  StringRef getPassName() const override { return "ModuleFastAddressSanitizer"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ASanFastGlobalsMetadataWrapperPass>();
  }

  bool runOnModule(Module &M) override {
    FastGlobalsMetadata &GlobalsMD =
        getAnalysis<ASanFastGlobalsMetadataWrapperPass>().getGlobalsMD();
    ModuleFastAddressSanitizer ASanModule(M, &GlobalsMD, CompileKernel, Recover,
                                      UseGlobalGC, UseOdrIndicator);
    return ASanModule.instrumentModule(M);
  }

private:
  bool CompileKernel;
  bool Recover;
  bool UseGlobalGC;
  bool UseOdrIndicator;
};

// Stack poisoning does not play well with exception handling.
// When an exception is thrown, we essentially bypass the code
// that unpoisones the stack. This is why the run-time library has
// to intercept __cxa_throw (as well as longjmp, etc) and unpoison the entire
// stack in the interceptor. This however does not work inside the
// actual function which catches the exception. Most likely because the
// compiler hoists the load of the shadow value somewhere too high.
// This causes asan to report a non-existing bug on 453.povray.
// It sounds like an LLVM bug.
struct FunctionStackPoisoner : public InstVisitor<FunctionStackPoisoner> {
  Function &F;
  FastAddressSanitizer &ASan;
  DIBuilder DIB;
  LLVMContext *C;
  Type *IntptrTy;
  Type *IntptrPtrTy;
  ShadowMapping Mapping;

  SmallVector<AllocaInst *, 16> AllocaVec;
  SmallVector<AllocaInst *, 16> StaticAllocasToMoveUp;
  SmallVector<Instruction *, 8> RetVec;
  unsigned StackAlignment;

  FunctionCallee AsanStackMallocFunc[kMaxAsanStackMallocSizeClass + 1],
      AsanStackFreeFunc[kMaxAsanStackMallocSizeClass + 1];
  FunctionCallee AsanSetShadowFunc[0x100] = {};
  FunctionCallee AsanPoisonStackMemoryFunc, AsanUnpoisonStackMemoryFunc;
  FunctionCallee AsanAllocaPoisonFunc, AsanAllocasUnpoisonFunc;

  // Stores a place and arguments of poisoning/unpoisoning call for alloca.
  struct AllocaPoisonCall {
    IntrinsicInst *InsBefore;
    AllocaInst *AI;
    uint64_t Size;
    bool DoPoison;
  };
  SmallVector<AllocaPoisonCall, 8> DynamicAllocaPoisonCallVec;
  SmallVector<AllocaPoisonCall, 8> StaticAllocaPoisonCallVec;
  bool HasUntracedLifetimeIntrinsic = false;

  SmallVector<AllocaInst *, 1> DynamicAllocaVec;
  SmallVector<IntrinsicInst *, 1> StackRestoreVec;
  AllocaInst *DynamicAllocaLayout = nullptr;
  IntrinsicInst *LocalEscapeCall = nullptr;

  // Maps Value to an AllocaInst from which the Value is originated.
  using AllocaForValueMapTy = DenseMap<Value *, AllocaInst *>;
  AllocaForValueMapTy AllocaForValue;

  bool HasNonEmptyInlineAsm = false;
  bool HasReturnsTwiceCall = false;
  std::unique_ptr<CallInst> EmptyInlineAsm;

  FunctionStackPoisoner(Function &F, FastAddressSanitizer &ASan)
      : F(F), ASan(ASan), DIB(*F.getParent(), /*AllowUnresolved*/ false),
        C(ASan.C), IntptrTy(ASan.IntptrTy),
        IntptrPtrTy(PointerType::get(IntptrTy, 0)), Mapping(ASan.Mapping),
        StackAlignment(1 << Mapping.Scale),
        EmptyInlineAsm(CallInst::Create(ASan.EmptyAsm)) {}

  bool runOnFunction() {
    if (!ClStack) return false;

    if (ClRedzoneByvalArgs)
      copyArgsPassedByValToAllocas();

    // Collect alloca, ret, lifetime instructions etc.
    for (BasicBlock *BB : depth_first(&F.getEntryBlock())) visit(*BB);

    if (AllocaVec.empty() && DynamicAllocaVec.empty()) return false;

    initializeCallbacks(*F.getParent());

    if (HasUntracedLifetimeIntrinsic) {
      // If there are lifetime intrinsics which couldn't be traced back to an
      // alloca, we may not know exactly when a variable enters scope, and
      // therefore should "fail safe" by not poisoning them.
      StaticAllocaPoisonCallVec.clear();
      DynamicAllocaPoisonCallVec.clear();
    }

    processDynamicAllocas();
    processStaticAllocas();

    if (ClDebugStack) {
      LLVM_DEBUG(dbgs() << F);
    }
    return true;
  }

  // Arguments marked with the "byval" attribute are implicitly copied without
  // using an alloca instruction.  To produce redzones for those arguments, we
  // copy them a second time into memory allocated with an alloca instruction.
  void copyArgsPassedByValToAllocas();

  // Finds all Alloca instructions and puts
  // poisoned red zones around all of them.
  // Then unpoison everything back before the function returns.
  void processStaticAllocas();
  void processDynamicAllocas();

  void createDynamicAllocasInitStorage();

  // ----------------------- Visitors.
  /// Collect all Ret instructions.
  void visitReturnInst(ReturnInst &RI) { RetVec.push_back(&RI); }

  /// Collect all Resume instructions.
  void visitResumeInst(ResumeInst &RI) { RetVec.push_back(&RI); }

  /// Collect all CatchReturnInst instructions.
  void visitCleanupReturnInst(CleanupReturnInst &CRI) { RetVec.push_back(&CRI); }

  void unpoisonDynamicAllocasBeforeInst(Instruction *InstBefore,
                                        Value *SavedStack) {
    IRBuilder<> IRB(InstBefore);
    Value *DynamicAreaPtr = IRB.CreatePtrToInt(SavedStack, IntptrTy);
    // When we insert _asan_allocas_unpoison before @llvm.stackrestore, we
    // need to adjust extracted SP to compute the address of the most recent
    // alloca. We have a special @llvm.get.dynamic.area.offset intrinsic for
    // this purpose.
    if (!isa<ReturnInst>(InstBefore)) {
      Function *DynamicAreaOffsetFunc = Intrinsic::getDeclaration(
          InstBefore->getModule(), Intrinsic::get_dynamic_area_offset,
          {IntptrTy});

      Value *DynamicAreaOffset = IRB.CreateCall(DynamicAreaOffsetFunc, {});

      DynamicAreaPtr = IRB.CreateAdd(IRB.CreatePtrToInt(SavedStack, IntptrTy),
                                     DynamicAreaOffset);
    }

    IRB.CreateCall(
        AsanAllocasUnpoisonFunc,
        {IRB.CreateLoad(IntptrTy, DynamicAllocaLayout), DynamicAreaPtr});
  }

  // Unpoison dynamic allocas redzones.
  void unpoisonDynamicAllocas() {
    for (auto &Ret : RetVec)
      unpoisonDynamicAllocasBeforeInst(Ret, DynamicAllocaLayout);

    for (auto &StackRestoreInst : StackRestoreVec)
      unpoisonDynamicAllocasBeforeInst(StackRestoreInst,
                                       StackRestoreInst->getOperand(0));
  }

  // Deploy and poison redzones around dynamic alloca call. To do this, we
  // should replace this call with another one with changed parameters and
  // replace all its uses with new address, so
  //   addr = alloca type, old_size, align
  // is replaced by
  //   new_size = (old_size + additional_size) * sizeof(type)
  //   tmp = alloca i8, new_size, max(align, 32)
  //   addr = tmp + 32 (first 32 bytes are for the left redzone).
  // Additional_size is added to make new memory allocation contain not only
  // requested memory, but also left, partial and right redzones.
  void handleDynamicAllocaCall(AllocaInst *AI);

  /// Collect Alloca instructions we want (and can) handle.
  void visitAllocaInst(AllocaInst &AI) {
    if (!ASan.isInterestingAlloca(AI)) {
      if (AI.isStaticAlloca()) {
        // Skip over allocas that are present *before* the first instrumented
        // alloca, we don't want to move those around.
        if (AllocaVec.empty())
          return;

        StaticAllocasToMoveUp.push_back(&AI);
      }
      return;
    }

    StackAlignment = std::max(StackAlignment, AI.getAlignment());
    if (!AI.isStaticAlloca())
      DynamicAllocaVec.push_back(&AI);
    else
      AllocaVec.push_back(&AI);
  }

  /// Collect lifetime intrinsic calls to check for use-after-scope
  /// errors.
  void visitIntrinsicInst(IntrinsicInst &II) {
    Intrinsic::ID ID = II.getIntrinsicID();
    if (ID == Intrinsic::stackrestore) StackRestoreVec.push_back(&II);
    if (ID == Intrinsic::localescape) LocalEscapeCall = &II;
    if (!ASan.UseAfterScope)
      return;
    if (!II.isLifetimeStartOrEnd())
      return;
    // Found lifetime intrinsic, add ASan instrumentation if necessary.
    auto *Size = cast<ConstantInt>(II.getArgOperand(0));
    // If size argument is undefined, don't do anything.
    if (Size->isMinusOne()) return;
    // Check that size doesn't saturate uint64_t and can
    // be stored in IntptrTy.
    const uint64_t SizeValue = Size->getValue().getLimitedValue();
    if (SizeValue == ~0ULL ||
        !ConstantInt::isValueValidForType(IntptrTy, SizeValue))
      return;
    // Find alloca instruction that corresponds to llvm.lifetime argument.
    AllocaInst *AI =
        llvm::findAllocaForValue(II.getArgOperand(1), AllocaForValue);
    if (!AI) {
      HasUntracedLifetimeIntrinsic = true;
      return;
    }
    // We're interested only in allocas we can handle.
    if (!ASan.isInterestingAlloca(*AI))
      return;
    bool DoPoison = (ID == Intrinsic::lifetime_end);
    AllocaPoisonCall APC = {&II, AI, SizeValue, DoPoison};
    if (AI->isStaticAlloca())
      StaticAllocaPoisonCallVec.push_back(APC);
    else if (ClInstrumentDynamicAllocas)
      DynamicAllocaPoisonCallVec.push_back(APC);
  }

  void visitCallSite(CallSite CS) {
    Instruction *I = CS.getInstruction();
    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      HasNonEmptyInlineAsm |= CI->isInlineAsm() &&
                              !CI->isIdenticalTo(EmptyInlineAsm.get()) &&
                              I != ASan.LocalDynamicShadow;
      HasReturnsTwiceCall |= CI->canReturnTwice();
    }
  }

  // ---------------------- Helpers.
  void initializeCallbacks(Module &M);

  // Copies bytes from ShadowBytes into shadow memory for indexes where
  // ShadowMask is not zero. If ShadowMask[i] is zero, we assume that
  // ShadowBytes[i] is constantly zero and doesn't need to be overwritten.
  void copyToShadow(ArrayRef<uint8_t> ShadowMask, ArrayRef<uint8_t> ShadowBytes,
                    IRBuilder<> &IRB, Value *ShadowBase);
  void copyToShadow(ArrayRef<uint8_t> ShadowMask, ArrayRef<uint8_t> ShadowBytes,
                    size_t Begin, size_t End, IRBuilder<> &IRB,
                    Value *ShadowBase);
  void copyToShadowInline(ArrayRef<uint8_t> ShadowMask,
                          ArrayRef<uint8_t> ShadowBytes, size_t Begin,
                          size_t End, IRBuilder<> &IRB, Value *ShadowBase);

  void poisonAlloca(Value *V, uint64_t Size, IRBuilder<> &IRB, bool DoPoison);

  Value *createAllocaForLayout(IRBuilder<> &IRB, const ASanStackFrameLayout &L,
                               bool Dynamic);
  PHINode *createPHI(IRBuilder<> &IRB, Value *Cond, Value *ValueIfTrue,
                     Instruction *ThenTerm, Value *ValueIfFalse);
};

} // end anonymous namespace

void FastLocationMetadata::parse(MDNode *MDN) {
  assert(MDN->getNumOperands() == 3);
  MDString *DIFilename = cast<MDString>(MDN->getOperand(0));
  Filename = DIFilename->getString();
  LineNo = mdconst::extract<ConstantInt>(MDN->getOperand(1))->getLimitedValue();
  ColumnNo =
      mdconst::extract<ConstantInt>(MDN->getOperand(2))->getLimitedValue();
}

// FIXME: It would be cleaner to instead attach relevant metadata to the globals
// we want to sanitize instead and reading this metadata on each pass over a
// function instead of reading module level metadata at first.
FastGlobalsMetadata::FastGlobalsMetadata(Module &M) {
  NamedMDNode *Globals = M.getNamedMetadata("llvm.asan.globals");
  if (!Globals)
    return;
  for (auto MDN : Globals->operands()) {
    // Metadata node contains the global and the fields of "Entry".
    assert(MDN->getNumOperands() == 5);
    auto *V = mdconst::extract_or_null<Constant>(MDN->getOperand(0));
    // The optimizer may optimize away a global entirely.
    if (!V)
      continue;
    auto *StrippedV = V->stripPointerCasts();
    auto *GV = dyn_cast<GlobalVariable>(StrippedV);
    if (!GV)
      continue;
    // We can already have an entry for GV if it was merged with another
    // global.
    Entry &E = Entries[GV];
    if (auto *Loc = cast_or_null<MDNode>(MDN->getOperand(1)))
      E.SourceLoc.parse(Loc);
    if (auto *Name = cast_or_null<MDString>(MDN->getOperand(2)))
      E.Name = Name->getString();
    ConstantInt *IsDynInit = mdconst::extract<ConstantInt>(MDN->getOperand(3));
    E.IsDynInit |= IsDynInit->isOne();
    ConstantInt *IsBlacklisted =
        mdconst::extract<ConstantInt>(MDN->getOperand(4));
    E.IsBlacklisted |= IsBlacklisted->isOne();
  }
}

AnalysisKey ASanFastGlobalsMetadataAnalysis::Key;

FastGlobalsMetadata ASanFastGlobalsMetadataAnalysis::run(Module &M,
                                                 ModuleAnalysisManager &AM) {
  return FastGlobalsMetadata(M);
}

FastAddressSanitizerPass::FastAddressSanitizerPass(bool CompileKernel, bool Recover,
                                           bool UseAfterScope)
    : CompileKernel(CompileKernel), Recover(Recover),
      UseAfterScope(UseAfterScope) {}

PreservedAnalyses FastAddressSanitizerPass::run(Function &F,
                                            AnalysisManager<Function> &AM) {
  auto &MAMProxy = AM.getResult<ModuleAnalysisManagerFunctionProxy>(F);
  auto &MAM = MAMProxy.getManager();
  Module &M = *F.getParent();
  if (auto *R = MAM.getCachedResult<ASanFastGlobalsMetadataAnalysis>(M)) {
    const TargetLibraryInfo *TLI = &AM.getResult<TargetLibraryAnalysis>(F);
		auto *AA = &AM.getResult<AAManager>(F);

    FastAddressSanitizer Sanitizer(M, R, CompileKernel, Recover, UseAfterScope);
		auto &AC = AM.getResult<AssumptionAnalysis>(F);
    if (Sanitizer.instrumentFunction(F, TLI, AA, &AC))
      return PreservedAnalyses::none();
    return PreservedAnalyses::all();
  }

  report_fatal_error(
      "The ASanFastGlobalsMetadataAnalysis is required to run before "
      "FastAddressSanitizer can run");
  return PreservedAnalyses::all();
}

ModuleFastAddressSanitizerPass::ModuleFastAddressSanitizerPass(bool CompileKernel,
                                                       bool Recover,
                                                       bool UseGlobalGC,
                                                       bool UseOdrIndicator)
    : CompileKernel(CompileKernel), Recover(Recover), UseGlobalGC(UseGlobalGC),
      UseOdrIndicator(UseOdrIndicator) {}

PreservedAnalyses ModuleFastAddressSanitizerPass::run(Module &M,
                                                  AnalysisManager<Module> &AM) {
  FastGlobalsMetadata &GlobalsMD = AM.getResult<ASanFastGlobalsMetadataAnalysis>(M);
  ModuleFastAddressSanitizer Sanitizer(M, &GlobalsMD, CompileKernel, Recover,
                                   UseGlobalGC, UseOdrIndicator);
  if (Sanitizer.instrumentModule(M))
    return PreservedAnalyses::none();
  return PreservedAnalyses::all();
}

INITIALIZE_PASS(ASanFastGlobalsMetadataWrapperPass, "fasan-globals-md",
                "Read metadata to mark which globals should be instrumented "
                "when running ASan.",
                false, true)

char FastAddressSanitizerLegacyPass::ID = 0;

INITIALIZE_PASS_BEGIN(
    FastAddressSanitizerLegacyPass, "asan",
    "FastAddressSanitizer: detects use-after-free and out-of-bounds bugs.", false,
    false)
INITIALIZE_PASS_DEPENDENCY(ASanFastGlobalsMetadataWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(AAResultsWrapperPass)
INITIALIZE_PASS_END(
    FastAddressSanitizerLegacyPass, "asan",
    "FastAddressSanitizer: detects use-after-free and out-of-bounds bugs.", false,
    false)

FunctionPass *llvm::createFastAddressSanitizerFunctionPass(bool CompileKernel,
                                                       bool Recover,
                                                       bool UseAfterScope) {
  assert(!CompileKernel || Recover);
  return new FastAddressSanitizerLegacyPass(CompileKernel, Recover, UseAfterScope);
}

char ModuleFastAddressSanitizerLegacyPass::ID = 0;

INITIALIZE_PASS(
    ModuleFastAddressSanitizerLegacyPass, "fasan-module",
    "FastAddressSanitizer: detects use-after-free and out-of-bounds bugs."
    "ModulePass",
    false, false)

ModulePass *llvm::createModuleFastAddressSanitizerLegacyPassPass(
    bool CompileKernel, bool Recover, bool UseGlobalsGC, bool UseOdrIndicator) {
  assert(!CompileKernel || Recover);
  return new ModuleFastAddressSanitizerLegacyPass(CompileKernel, Recover,
                                              UseGlobalsGC, UseOdrIndicator);
}

static size_t TypeSizeToSizeIndex(uint32_t TypeSize) {
  size_t Res = countTrailingZeros(TypeSize / 8);
  assert(Res < kNumberOfAccessSizes);
  return Res;
}

/// Create a global describing a source location.
static GlobalVariable *createPrivateGlobalForSourceLoc(Module &M,
                                                       FastLocationMetadata MD) {
  Constant *LocData[] = {
      createPrivateGlobalForString(M, MD.Filename, true, kAsanGenPrefix),
      ConstantInt::get(Type::getInt32Ty(M.getContext()), MD.LineNo),
      ConstantInt::get(Type::getInt32Ty(M.getContext()), MD.ColumnNo),
  };
  auto LocStruct = ConstantStruct::getAnon(LocData);
  auto GV = new GlobalVariable(M, LocStruct->getType(), true,
                               GlobalValue::PrivateLinkage, LocStruct,
                               kAsanGenPrefix);
  GV->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
  return GV;
}

/// Check if \p G has been created by a trusted compiler pass.
static bool GlobalWasGeneratedByCompiler(GlobalVariable *G) {
  // Do not instrument @llvm.global_ctors, @llvm.used, etc.
  if (G->getName().startswith("llvm."))
    return true;

  // Do not instrument asan globals.
  if (G->getName().startswith(kAsanGenPrefix) ||
      G->getName().startswith(kSanCovGenPrefix) ||
      G->getName().startswith(kODRGenPrefix))
    return true;

  // Do not instrument gcov counter arrays.
  if (G->getName() == "__llvm_gcov_ctr")
    return true;

  return false;
}

Value *FastAddressSanitizer::memToShadow(Value *Shadow, IRBuilder<> &IRB) {
  // Shadow >> scale
  Shadow = IRB.CreateLShr(Shadow, Mapping.Scale);
  if (Mapping.Offset == 0) return Shadow;
  // (Shadow >> scale) | offset
  Value *ShadowBase;
  if (LocalDynamicShadow)
    ShadowBase = LocalDynamicShadow;
  else
    ShadowBase = ConstantInt::get(IntptrTy, Mapping.Offset);
  if (Mapping.OrShadowOffset)
    return IRB.CreateOr(Shadow, ShadowBase);
  else
    return IRB.CreateAdd(Shadow, ShadowBase);
}

// Instrument memset/memmove/memcpy
void FastAddressSanitizer::instrumentMemIntrinsic(MemIntrinsic *MI) {
  IRBuilder<> IRB(MI);
  if (isa<MemTransferInst>(MI)) {
    IRB.CreateCall(
        isa<MemMoveInst>(MI) ? AsanMemmove : AsanMemcpy,
        {IRB.CreatePointerCast(MI->getOperand(0), IRB.getInt8PtrTy()),
         IRB.CreatePointerCast(MI->getOperand(1), IRB.getInt8PtrTy()),
         IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)});
  } else if (isa<MemSetInst>(MI)) {
    IRB.CreateCall(
        AsanMemset,
        {IRB.CreatePointerCast(MI->getOperand(0), IRB.getInt8PtrTy()),
         IRB.CreateIntCast(MI->getOperand(1), IRB.getInt32Ty(), false),
         IRB.CreateIntCast(MI->getOperand(2), IntptrTy, false)});
  }
  MI->eraseFromParent();
}

/// Check if we want (and can) handle this alloca.
bool FastAddressSanitizer::isInterestingAlloca(const AllocaInst &AI) {
#if 0
  auto PreviouslySeenAllocaInfo = ProcessedAllocas.find(&AI);

  if (PreviouslySeenAllocaInfo != ProcessedAllocas.end())
    return PreviouslySeenAllocaInfo->getSecond();
#endif
  bool IsInteresting =
      (AI.getAllocatedType()->isSized() &&
       // alloca() may be called with 0 size, ignore it.
       ((!AI.isStaticAlloca()) || getAllocaSizeInBytes(AI) > 0) &&
       // We are only interested in allocas not promotable to registers.
       // Promotable allocas are common under -O0.
       (!ClSkipPromotableAllocas || !isAllocaPromotable(&AI)) &&
       // inalloca allocas are not treated as static, and we don't want
       // dynamic alloca instrumentation for them as well.
       !AI.isUsedWithInAlloca() &&
       // swifterror allocas are register promoted by ISel
       !AI.isSwiftError());

//  ProcessedAllocas[&AI] = IsInteresting;
  return IsInteresting;
}

Value *FastAddressSanitizer::isInterestingMemoryAccess(Instruction *I,
                                                   bool *IsWrite,
                                                   uint64_t *TypeSize,
                                                   unsigned *Alignment,
                                                   Value **MaybeMask) {
  // Skip memory accesses inserted by another instrumentation.
  //if (I->hasMetadata("nosanitize")) return nullptr;

  // Do not instrument the load fetching the dynamic shadow address.
  //if (LocalDynamicShadow == I)
    //return nullptr;

  Value *PtrOperand = nullptr;
  const DataLayout &DL = I->getModule()->getDataLayout();
  if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
    if (!ClInstrumentReads) return nullptr;
    *IsWrite = false;
    *TypeSize = DL.getTypeStoreSizeInBits(LI->getType());
    *Alignment = LI->getAlignment();
    PtrOperand = LI->getPointerOperand();
			//errs() << "li " << *PtrOperand << "\n";
  } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
    if (!ClInstrumentWrites) return nullptr;
    *IsWrite = true;
    *TypeSize = DL.getTypeStoreSizeInBits(SI->getValueOperand()->getType());
    *Alignment = SI->getAlignment();
    PtrOperand = SI->getPointerOperand();
			//errs() << "si " << *PtrOperand << "\n";
  } else if (AtomicRMWInst *RMW = dyn_cast<AtomicRMWInst>(I)) {
    if (!ClInstrumentAtomics) return nullptr;
    *IsWrite = true;
    *TypeSize = DL.getTypeStoreSizeInBits(RMW->getValOperand()->getType());
    *Alignment = 0;
    PtrOperand = RMW->getPointerOperand();
			//errs() << "rmw " << *PtrOperand << "\n";
  } else if (AtomicCmpXchgInst *XCHG = dyn_cast<AtomicCmpXchgInst>(I)) {
    if (!ClInstrumentAtomics) return nullptr;
    *IsWrite = true;
    *TypeSize = DL.getTypeStoreSizeInBits(XCHG->getCompareOperand()->getType());
    *Alignment = 0;
    PtrOperand = XCHG->getPointerOperand();
			//errs() << "xchg " << *PtrOperand << "\n";
  } else if (auto CI = dyn_cast<CallInst>(I)) {
    auto *F = dyn_cast<Function>(CI->getCalledValue());
    if (F && (F->getName().startswith("llvm.masked.load.") ||
              F->getName().startswith("llvm.masked.store."))) {
      unsigned OpOffset = 0;
      if (F->getName().startswith("llvm.masked.store.")) {
        if (!ClInstrumentWrites)
          return nullptr;
        // Masked store has an initial operand for the value.
        OpOffset = 1;
        *IsWrite = true;
      } else {
        if (!ClInstrumentReads)
          return nullptr;
        *IsWrite = false;
      }

      auto BasePtr = CI->getOperand(0 + OpOffset);
      auto Ty = cast<PointerType>(BasePtr->getType())->getElementType();
      *TypeSize = DL.getTypeStoreSizeInBits(Ty);
      if (auto AlignmentConstant =
              dyn_cast<ConstantInt>(CI->getOperand(1 + OpOffset)))
        *Alignment = (unsigned)AlignmentConstant->getZExtValue();
      else
        *Alignment = 1; // No alignment guarantees. We probably got Undef
      if (MaybeMask)
        *MaybeMask = CI->getOperand(2 + OpOffset);
      PtrOperand = BasePtr;
			//errs() << "masked load " << *PtrOperand << "\n";
    }
  }

  if (PtrOperand) {
    // Do not instrument acesses from different address spaces; we cannot deal
    // with them.
    Type *PtrTy = cast<PointerType>(PtrOperand->getType()->getScalarType());
    if (PtrTy->getPointerAddressSpace() != 0)
      return nullptr;

    // Ignore swifterror addresses.
    // swifterror memory addresses are mem2reg promoted by instruction
    // selection. As such they cannot have regular uses like an instrumentation
    // function and it makes no sense to track them as memory.
    if (PtrOperand->isSwiftError())
      return nullptr;
  }

  // Treat memory accesses to promotable allocas as non-interesting since they
  // will not cause memory violations. This greatly speeds up the instrumented
  // executable at -O0.
  if (ClSkipPromotableAllocas)
    if (auto AI = dyn_cast_or_null<AllocaInst>(PtrOperand))
      return isInterestingAlloca(*AI) ? AI : nullptr;

  return PtrOperand;
}

static bool isPointerOperand(Value *V) {
  return V->getType()->isPointerTy() || isa<PtrToIntInst>(V);
}

// This is a rough heuristic; it may cause both false positives and
// false negatives. The proper implementation requires cooperation with
// the frontend.
static bool isInterestingPointerComparison(Instruction *I) {
  if (ICmpInst *Cmp = dyn_cast<ICmpInst>(I)) {
    if (!Cmp->isRelational())
      return false;
  } else {
    return false;
  }
  return isPointerOperand(I->getOperand(0)) &&
         isPointerOperand(I->getOperand(1));
}

// This is a rough heuristic; it may cause both false positives and
// false negatives. The proper implementation requires cooperation with
// the frontend.
static bool isInterestingPointerSubtraction(Instruction *I) {
  if (BinaryOperator *BO = dyn_cast<BinaryOperator>(I)) {
    if (BO->getOpcode() != Instruction::Sub)
      return false;
  } else {
    return false;
  }
  return isPointerOperand(I->getOperand(0)) &&
         isPointerOperand(I->getOperand(1));
}

bool FastAddressSanitizer::GlobalIsLinkerInitialized(GlobalVariable *G) {
  // If a global variable does not have dynamic initialization we don't
  // have to instrument it.  However, if a global does not have initializer
  // at all, we assume it has dynamic initializer (in other TU).
  //
  // FIXME: Metadata should be attched directly to the global directly instead
  // of being added to llvm.asan.globals.
  return G->hasInitializer() && !GlobalsMD.get(G).IsDynInit;
}

void FastAddressSanitizer::instrumentPointerComparisonOrSubtraction(
    Instruction *I) {
  IRBuilder<> IRB(I);
  FunctionCallee F = isa<ICmpInst>(I) ? AsanPtrCmpFunction : AsanPtrSubFunction;
  Value *Param[2] = {I->getOperand(0), I->getOperand(1)};
  for (Value *&i : Param) {
    if (i->getType()->isPointerTy())
      i = IRB.CreatePointerCast(i, IntptrTy);
  }
  IRB.CreateCall(F, Param);
}

static void doInstrumentAddress(FastAddressSanitizer *Pass, Instruction *I,
                                Instruction *InsertBefore, Value *Addr,
                                unsigned Alignment, unsigned Granularity,
                                uint32_t TypeSize, bool IsWrite,
                                Value *SizeArgument, bool UseCalls,
                                uint32_t Exp) {
  // Instrument a 1-, 2-, 4-, 8-, or 16- byte access with one check
  // if the data is properly aligned.
  if ((TypeSize == 8 || TypeSize == 16 || TypeSize == 32 || TypeSize == 64 ||
       TypeSize == 128) &&
      (Alignment >= Granularity || Alignment == 0 || Alignment >= TypeSize / 8))
    return Pass->instrumentAddress(I, InsertBefore, Addr, TypeSize, IsWrite,
                                   nullptr, UseCalls, Exp);
  Pass->instrumentUnusualSizeOrAlignment(I, InsertBefore, Addr, TypeSize,
                                         IsWrite, nullptr, UseCalls, Exp);
}

static void instrumentMaskedLoadOrStore(FastAddressSanitizer *Pass,
                                        const DataLayout &DL, Type *IntptrTy,
                                        Value *Mask, Instruction *I,
                                        Value *Addr, unsigned Alignment,
                                        unsigned Granularity, uint32_t TypeSize,
                                        bool IsWrite, Value *SizeArgument,
                                        bool UseCalls, uint32_t Exp) {
  auto *VTy = cast<PointerType>(Addr->getType())->getElementType();
  uint64_t ElemTypeSize = DL.getTypeStoreSizeInBits(VTy->getScalarType());
  unsigned Num = VTy->getVectorNumElements();
  auto Zero = ConstantInt::get(IntptrTy, 0);
  for (unsigned Idx = 0; Idx < Num; ++Idx) {
    Value *InstrumentedAddress = nullptr;
    Instruction *InsertBefore = I;
    if (auto *Vector = dyn_cast<ConstantVector>(Mask)) {
      // dyn_cast as we might get UndefValue
      if (auto *Masked = dyn_cast<ConstantInt>(Vector->getOperand(Idx))) {
        if (Masked->isZero())
          // Mask is constant false, so no instrumentation needed.
          continue;
        // If we have a true or undef value, fall through to doInstrumentAddress
        // with InsertBefore == I
      }
    } else {
      IRBuilder<> IRB(I);
      Value *MaskElem = IRB.CreateExtractElement(Mask, Idx);
      Instruction *ThenTerm = SplitBlockAndInsertIfThen(MaskElem, I, false);
      InsertBefore = ThenTerm;
    }

    IRBuilder<> IRB(InsertBefore);
    InstrumentedAddress =
        IRB.CreateGEP(VTy, Addr, {Zero, ConstantInt::get(IntptrTy, Idx)});
    doInstrumentAddress(Pass, I, InsertBefore, InstrumentedAddress, Alignment,
                        Granularity, ElemTypeSize, IsWrite, SizeArgument,
                        UseCalls, Exp);
  }
}

void FastAddressSanitizer::instrumentMop(ObjectSizeOffsetVisitor &ObjSizeVis,
                                     Instruction *I, bool UseCalls,
                                     const DataLayout &DL) {
  bool IsWrite = false;
  unsigned Alignment = 0;
  uint64_t TypeSize = 0;
  Value *MaybeMask = nullptr;
  Value *Addr =
      isInterestingMemoryAccess(I, &IsWrite, &TypeSize, &Alignment, &MaybeMask);
  assert(Addr);

  // Optimization experiments.
  // The experiments can be used to evaluate potential optimizations that remove
  // instrumentation (assess false negatives). Instead of completely removing
  // some instrumentation, you set Exp to a non-zero value (mask of optimization
  // experiments that want to remove instrumentation of this instruction).
  // If Exp is non-zero, this pass will emit special calls into runtime
  // (e.g. __asan_report_exp_load1 instead of __asan_report_load1). These calls
  // make runtime terminate the program in a special way (with a different
  // exit status). Then you run the new compiler on a buggy corpus, collect
  // the special terminations (ideally, you don't see them at all -- no false
  // negatives) and make the decision on the optimization.
  uint32_t Exp = ClForceExperiment;

  if (ClOpt && ClOptGlobals) {
    // If initialization order checking is disabled, a simple access to a
    // dynamically initialized global is always valid.
    GlobalVariable *G = dyn_cast<GlobalVariable>(GetUnderlyingObject(Addr, DL));
    if (G && (!ClInitializers || GlobalIsLinkerInitialized(G)) &&
        isSafeAccess(ObjSizeVis, Addr, TypeSize)) {
      NumOptimizedAccessesToGlobalVar++;
      return;
    }
  }

  if (ClOpt && ClOptStack) {
    // A direct inbounds access to a stack variable is always valid.
    if (isa<AllocaInst>(GetUnderlyingObject(Addr, DL)) &&
        isSafeAccess(ObjSizeVis, Addr, TypeSize)) {
      NumOptimizedAccessesToStackVar++;
      return;
    }
  }

  if (IsWrite)
    NumInstrumentedWrites++;
  else
    NumInstrumentedReads++;

  unsigned Granularity = 1 << Mapping.Scale;
  if (MaybeMask) {
    instrumentMaskedLoadOrStore(this, DL, IntptrTy, MaybeMask, I, Addr,
                                Alignment, Granularity, TypeSize, IsWrite,
                                nullptr, UseCalls, Exp);
  } else {
    doInstrumentAddress(this, I, I, Addr, Alignment, Granularity, TypeSize,
                        IsWrite, nullptr, UseCalls, Exp);
  }
}

Instruction *FastAddressSanitizer::generateCrashCode(Instruction *InsertBefore,
                                                 Value *Addr, bool IsWrite,
                                                 size_t AccessSizeIndex,
                                                 Value *SizeArgument,
                                                 uint32_t Exp) {
  IRBuilder<> IRB(InsertBefore);
  Value *ExpVal = Exp == 0 ? nullptr : ConstantInt::get(IRB.getInt32Ty(), Exp);
  CallInst *Call = nullptr;
  if (SizeArgument) {
    if (Exp == 0)
      Call = IRB.CreateCall(AsanErrorCallbackSized[IsWrite][0],
                            {Addr, SizeArgument});
    else
      Call = IRB.CreateCall(AsanErrorCallbackSized[IsWrite][1],
                            {Addr, SizeArgument, ExpVal});
  } else {
    if (Exp == 0)
      Call =
          IRB.CreateCall(AsanErrorCallback[IsWrite][0][AccessSizeIndex], Addr);
    else
      Call = IRB.CreateCall(AsanErrorCallback[IsWrite][1][AccessSizeIndex],
                            {Addr, ExpVal});
  }

  // We don't do Call->setDoesNotReturn() because the BB already has
  // UnreachableInst at the end.
  // This EmptyAsm is required to avoid callback merge.
  IRB.CreateCall(EmptyAsm, {});
  return Call;
}

Value *FastAddressSanitizer::createSlowPathCmp(IRBuilder<> &IRB, Value *AddrLong,
                                           Value *ShadowValue,
                                           uint32_t TypeSize) {
  size_t Granularity = static_cast<size_t>(1) << Mapping.Scale;
  // Addr & (Granularity - 1)
  Value *LastAccessedByte =
      IRB.CreateAnd(AddrLong, ConstantInt::get(IntptrTy, Granularity - 1));
  // (Addr & (Granularity - 1)) + size - 1
  if (TypeSize / 8 > 1)
    LastAccessedByte = IRB.CreateAdd(
        LastAccessedByte, ConstantInt::get(IntptrTy, TypeSize / 8 - 1));
  // (uint8_t) ((Addr & (Granularity-1)) + size - 1)
  LastAccessedByte =
      IRB.CreateIntCast(LastAccessedByte, ShadowValue->getType(), false);
  // ((uint8_t) ((Addr & (Granularity-1)) + size - 1)) >= ShadowValue
  return IRB.CreateICmpSGE(LastAccessedByte, ShadowValue);
}

void FastAddressSanitizer::instrumentAddress(Instruction *OrigIns,
                                         Instruction *InsertBefore, Value *Addr,
                                         uint32_t TypeSize, bool IsWrite,
                                         Value *SizeArgument, bool UseCalls,
                                         uint32_t Exp) {
  bool IsMyriad = TargetTriple.getVendor() == llvm::Triple::Myriad;

  IRBuilder<> IRB(InsertBefore);
  Value *AddrLong = IRB.CreatePointerCast(Addr, IntptrTy);
  size_t AccessSizeIndex = TypeSizeToSizeIndex(TypeSize);

  if (UseCalls) {
    if (Exp == 0)
      IRB.CreateCall(AsanMemoryAccessCallback[IsWrite][0][AccessSizeIndex],
                     AddrLong);
    else
      IRB.CreateCall(AsanMemoryAccessCallback[IsWrite][1][AccessSizeIndex],
                     {AddrLong, ConstantInt::get(IRB.getInt32Ty(), Exp)});
    return;
  }

  if (IsMyriad) {
    // Strip the cache bit and do range check.
    // AddrLong &= ~kMyriadCacheBitMask32
    AddrLong = IRB.CreateAnd(AddrLong, ~kMyriadCacheBitMask32);
    // Tag = AddrLong >> kMyriadTagShift
    Value *Tag = IRB.CreateLShr(AddrLong, kMyriadTagShift);
    // Tag == kMyriadDDRTag
    Value *TagCheck =
        IRB.CreateICmpEQ(Tag, ConstantInt::get(IntptrTy, kMyriadDDRTag));

    Instruction *TagCheckTerm =
        SplitBlockAndInsertIfThen(TagCheck, InsertBefore, false,
                                  MDBuilder(*C).createBranchWeights(1, 100000));
    assert(cast<BranchInst>(TagCheckTerm)->isUnconditional());
    IRB.SetInsertPoint(TagCheckTerm);
    InsertBefore = TagCheckTerm;
  }

  Type *ShadowTy =
      IntegerType::get(*C, std::max(8U, TypeSize >> Mapping.Scale));
  Type *ShadowPtrTy = PointerType::get(ShadowTy, 0);
  Value *ShadowPtr = memToShadow(AddrLong, IRB);
  Value *CmpVal = Constant::getNullValue(ShadowTy);
  Value *ShadowValue =
      IRB.CreateLoad(ShadowTy, IRB.CreateIntToPtr(ShadowPtr, ShadowPtrTy));

  Value *Cmp = IRB.CreateICmpNE(ShadowValue, CmpVal);
  size_t Granularity = 1ULL << Mapping.Scale;
  Instruction *CrashTerm = nullptr;

  if (ClAlwaysSlowPath || (TypeSize < 8 * Granularity)) {
    // We use branch weights for the slow path check, to indicate that the slow
    // path is rarely taken. This seems to be the case for SPEC benchmarks.
    Instruction *CheckTerm = SplitBlockAndInsertIfThen(
        Cmp, InsertBefore, false, MDBuilder(*C).createBranchWeights(1, 100000));
    assert(cast<BranchInst>(CheckTerm)->isUnconditional());
    BasicBlock *NextBB = CheckTerm->getSuccessor(0);
    IRB.SetInsertPoint(CheckTerm);
    Value *Cmp2 = createSlowPathCmp(IRB, AddrLong, ShadowValue, TypeSize);
    if (Recover) {
      CrashTerm = SplitBlockAndInsertIfThen(Cmp2, CheckTerm, false);
    } else {
      BasicBlock *CrashBlock =
        BasicBlock::Create(*C, "", NextBB->getParent(), NextBB);
      CrashTerm = new UnreachableInst(*C, CrashBlock);
      BranchInst *NewTerm = BranchInst::Create(CrashBlock, NextBB, Cmp2);
      ReplaceInstWithInst(CheckTerm, NewTerm);
    }
  } else {
    CrashTerm = SplitBlockAndInsertIfThen(Cmp, InsertBefore, !Recover);
  }

  Instruction *Crash = generateCrashCode(CrashTerm, AddrLong, IsWrite,
                                         AccessSizeIndex, SizeArgument, Exp);
  Crash->setDebugLoc(OrigIns->getDebugLoc());
}

// Instrument unusual size or unusual alignment.
// We can not do it with a single check, so we do 1-byte check for the first
// and the last bytes. We call __asan_report_*_n(addr, real_size) to be able
// to report the actual access size.
void FastAddressSanitizer::instrumentUnusualSizeOrAlignment(
    Instruction *I, Instruction *InsertBefore, Value *Addr, uint32_t TypeSize,
    bool IsWrite, Value *SizeArgument, bool UseCalls, uint32_t Exp) {
  IRBuilder<> IRB(InsertBefore);
  Value *Size = ConstantInt::get(IntptrTy, TypeSize / 8);
  Value *AddrLong = IRB.CreatePointerCast(Addr, IntptrTy);
  if (UseCalls) {
    if (Exp == 0)
      IRB.CreateCall(AsanMemoryAccessCallbackSized[IsWrite][0],
                     {AddrLong, Size});
    else
      IRB.CreateCall(AsanMemoryAccessCallbackSized[IsWrite][1],
                     {AddrLong, Size, ConstantInt::get(IRB.getInt32Ty(), Exp)});
  } else {
    Value *LastByte = IRB.CreateIntToPtr(
        IRB.CreateAdd(AddrLong, ConstantInt::get(IntptrTy, TypeSize / 8 - 1)),
        Addr->getType());
    instrumentAddress(I, InsertBefore, Addr, 8, IsWrite, Size, false, Exp);
    instrumentAddress(I, InsertBefore, LastByte, 8, IsWrite, Size, false, Exp);
  }
}

void ModuleFastAddressSanitizer::poisonOneInitializer(Function &GlobalInit,
                                                  GlobalValue *ModuleName) {
  // Set up the arguments to our poison/unpoison functions.
  IRBuilder<> IRB(&GlobalInit.front(),
                  GlobalInit.front().getFirstInsertionPt());

  // Add a call to poison all external globals before the given function starts.
  Value *ModuleNameAddr = ConstantExpr::getPointerCast(ModuleName, IntptrTy);
  IRB.CreateCall(AsanPoisonGlobals, ModuleNameAddr);

  // Add calls to unpoison all globals before each return instruction.
  for (auto &BB : GlobalInit.getBasicBlockList())
    if (ReturnInst *RI = dyn_cast<ReturnInst>(BB.getTerminator()))
      CallInst::Create(AsanUnpoisonGlobals, "", RI);
}

void ModuleFastAddressSanitizer::createInitializerPoisonCalls(
    Module &M, GlobalValue *ModuleName) {
  GlobalVariable *GV = M.getGlobalVariable("llvm.global_ctors");
  if (!GV)
    return;

  ConstantArray *CA = dyn_cast<ConstantArray>(GV->getInitializer());
  if (!CA)
    return;

  for (Use &OP : CA->operands()) {
    if (isa<ConstantAggregateZero>(OP)) continue;
    ConstantStruct *CS = cast<ConstantStruct>(OP);

    // Must have a function or null ptr.
    if (Function *F = dyn_cast<Function>(CS->getOperand(1))) {
      if (F->getName() == kAsanModuleCtorName) continue;
      auto *Priority = cast<ConstantInt>(CS->getOperand(0));
      // Don't instrument CTORs that will run before asan.module_ctor.
      if (Priority->getLimitedValue() <= GetCtorAndDtorPriority(TargetTriple))
        continue;
      poisonOneInitializer(*F, ModuleName);
    }
  }
}

bool ModuleFastAddressSanitizer::ShouldInstrumentGlobal(GlobalVariable *G) {
  Type *Ty = G->getValueType();
  LLVM_DEBUG(dbgs() << "GLOBAL: " << *G << "\n");

  // FIXME: Metadata should be attched directly to the global directly instead
  // of being added to llvm.asan.globals.
  if (GlobalsMD.get(G).IsBlacklisted) return false;
  if (!Ty->isSized()) return false;
  if (!G->hasInitializer()) return false;
  // Only instrument globals of default address spaces
  if (G->getAddressSpace()) return false;
  if (GlobalWasGeneratedByCompiler(G)) return false; // Our own globals.
  // Two problems with thread-locals:
  //   - The address of the main thread's copy can't be computed at link-time.
  //   - Need to poison all copies, not just the main thread's one.
  if (G->isThreadLocal()) return false;
  // For now, just ignore this Global if the alignment is large.
  if (G->getAlignment() > MinRedzoneSizeForGlobal()) return false;

  // For non-COFF targets, only instrument globals known to be defined by this
  // TU.
  // FIXME: We can instrument comdat globals on ELF if we are using the
  // GC-friendly metadata scheme.
  if (!TargetTriple.isOSBinFormatCOFF()) {
    if (!G->hasExactDefinition() || G->hasComdat())
      return false;
  } else {
    // On COFF, don't instrument non-ODR linkages.
    if (G->isInterposable())
      return false;
  }

  // If a comdat is present, it must have a selection kind that implies ODR
  // semantics: no duplicates, any, or exact match.
  if (Comdat *C = G->getComdat()) {
    switch (C->getSelectionKind()) {
    case Comdat::Any:
    case Comdat::ExactMatch:
    case Comdat::NoDuplicates:
      break;
    case Comdat::Largest:
    case Comdat::SameSize:
      return false;
    }
  }

  if (G->hasSection()) {
    StringRef Section = G->getSection();

    // Globals from llvm.metadata aren't emitted, do not instrument them.
    if (Section == "llvm.metadata") return false;
    // Do not instrument globals from special LLVM sections.
    if (Section.find("__llvm") != StringRef::npos || Section.find("__LLVM") != StringRef::npos) return false;

    // Do not instrument function pointers to initialization and termination
    // routines: dynamic linker will not properly handle redzones.
    if (Section.startswith(".preinit_array") ||
        Section.startswith(".init_array") ||
        Section.startswith(".fini_array")) {
      return false;
    }

    // On COFF, if the section name contains '$', it is highly likely that the
    // user is using section sorting to create an array of globals similar to
    // the way initialization callbacks are registered in .init_array and
    // .CRT$XCU. The ATL also registers things in .ATL$__[azm]. Adding redzones
    // to such globals is counterproductive, because the intent is that they
    // will form an array, and out-of-bounds accesses are expected.
    // See https://github.com/google/sanitizers/issues/305
    // and http://msdn.microsoft.com/en-US/en-en/library/bb918180(v=vs.120).aspx
    if (TargetTriple.isOSBinFormatCOFF() && Section.contains('$')) {
      LLVM_DEBUG(dbgs() << "Ignoring global in sorted section (contains '$'): "
                        << *G << "\n");
      return false;
    }

    if (TargetTriple.isOSBinFormatMachO()) {
      StringRef ParsedSegment, ParsedSection;
      unsigned TAA = 0, StubSize = 0;
      bool TAAParsed;
      std::string ErrorCode = MCSectionMachO::ParseSectionSpecifier(
          Section, ParsedSegment, ParsedSection, TAA, TAAParsed, StubSize);
      assert(ErrorCode.empty() && "Invalid section specifier.");

      // Ignore the globals from the __OBJC section. The ObjC runtime assumes
      // those conform to /usr/lib/objc/runtime.h, so we can't add redzones to
      // them.
      if (ParsedSegment == "__OBJC" ||
          (ParsedSegment == "__DATA" && ParsedSection.startswith("__objc_"))) {
        LLVM_DEBUG(dbgs() << "Ignoring ObjC runtime global: " << *G << "\n");
        return false;
      }
      // See https://github.com/google/sanitizers/issues/32
      // Constant CFString instances are compiled in the following way:
      //  -- the string buffer is emitted into
      //     __TEXT,__cstring,cstring_literals
      //  -- the constant NSConstantString structure referencing that buffer
      //     is placed into __DATA,__cfstring
      // Therefore there's no point in placing redzones into __DATA,__cfstring.
      // Moreover, it causes the linker to crash on OS X 10.7
      if (ParsedSegment == "__DATA" && ParsedSection == "__cfstring") {
        LLVM_DEBUG(dbgs() << "Ignoring CFString: " << *G << "\n");
        return false;
      }
      // The linker merges the contents of cstring_literals and removes the
      // trailing zeroes.
      if (ParsedSegment == "__TEXT" && (TAA & MachO::S_CSTRING_LITERALS)) {
        LLVM_DEBUG(dbgs() << "Ignoring a cstring literal: " << *G << "\n");
        return false;
      }
    }
  }

  return true;
}

// On Mach-O platforms, we emit global metadata in a separate section of the
// binary in order to allow the linker to properly dead strip. This is only
// supported on recent versions of ld64.
bool ModuleFastAddressSanitizer::ShouldUseMachOGlobalsSection() const {
  if (!TargetTriple.isOSBinFormatMachO())
    return false;

  if (TargetTriple.isMacOSX() && !TargetTriple.isMacOSXVersionLT(10, 11))
    return true;
  if (TargetTriple.isiOS() /* or tvOS */ && !TargetTriple.isOSVersionLT(9))
    return true;
  if (TargetTriple.isWatchOS() && !TargetTriple.isOSVersionLT(2))
    return true;

  return false;
}

StringRef ModuleFastAddressSanitizer::getGlobalMetadataSection() const {
  switch (TargetTriple.getObjectFormat()) {
  case Triple::COFF:  return ".ASAN$GL";
  case Triple::ELF:   return "asan_globals";
  case Triple::MachO: return "__DATA,__asan_globals,regular";
  case Triple::Wasm:
  case Triple::XCOFF:
    report_fatal_error(
        "ModuleFastAddressSanitizer not implemented for object file format.");
  case Triple::UnknownObjectFormat:
    break;
  }
  llvm_unreachable("unsupported object format");
}

void ModuleFastAddressSanitizer::initializeCallbacks(Module &M) {
  IRBuilder<> IRB(*C);

  // Declare our poisoning and unpoisoning functions.
  AsanPoisonGlobals =
      M.getOrInsertFunction(kAsanPoisonGlobalsName, IRB.getVoidTy(), IntptrTy);
  AsanUnpoisonGlobals =
      M.getOrInsertFunction(kAsanUnpoisonGlobalsName, IRB.getVoidTy());

  // Declare functions that register/unregister globals.
  AsanRegisterGlobals = M.getOrInsertFunction(
      kAsanRegisterGlobalsName, IRB.getVoidTy(), IntptrTy, IntptrTy);
  AsanUnregisterGlobals = M.getOrInsertFunction(
      kAsanUnregisterGlobalsName, IRB.getVoidTy(), IntptrTy, IntptrTy);

  // Declare the functions that find globals in a shared object and then invoke
  // the (un)register function on them.
  AsanRegisterImageGlobals = M.getOrInsertFunction(
      kAsanRegisterImageGlobalsName, IRB.getVoidTy(), IntptrTy);
  AsanUnregisterImageGlobals = M.getOrInsertFunction(
      kAsanUnregisterImageGlobalsName, IRB.getVoidTy(), IntptrTy);

  AsanRegisterElfGlobals =
      M.getOrInsertFunction(kAsanRegisterElfGlobalsName, IRB.getVoidTy(),
                            IntptrTy, IntptrTy, IntptrTy);
  AsanUnregisterElfGlobals =
      M.getOrInsertFunction(kAsanUnregisterElfGlobalsName, IRB.getVoidTy(),
                            IntptrTy, IntptrTy, IntptrTy);
}

// Put the metadata and the instrumented global in the same group. This ensures
// that the metadata is discarded if the instrumented global is discarded.
void ModuleFastAddressSanitizer::SetComdatForGlobalMetadata(
    GlobalVariable *G, GlobalVariable *Metadata, StringRef InternalSuffix) {
  Module &M = *G->getParent();
  Comdat *C = G->getComdat();
  if (!C) {
    if (!G->hasName()) {
      // If G is unnamed, it must be internal. Give it an artificial name
      // so we can put it in a comdat.
      assert(G->hasLocalLinkage());
      G->setName(Twine(kAsanGenPrefix) + "_anon_global");
    }

    if (!InternalSuffix.empty() && G->hasLocalLinkage()) {
      std::string Name = G->getName();
      Name += InternalSuffix;
      C = M.getOrInsertComdat(Name);
    } else {
      C = M.getOrInsertComdat(G->getName());
    }

    // Make this IMAGE_COMDAT_SELECT_NODUPLICATES on COFF. Also upgrade private
    // linkage to internal linkage so that a symbol table entry is emitted. This
    // is necessary in order to create the comdat group.
    if (TargetTriple.isOSBinFormatCOFF()) {
      C->setSelectionKind(Comdat::NoDuplicates);
      if (G->hasPrivateLinkage())
        G->setLinkage(GlobalValue::InternalLinkage);
    }
    G->setComdat(C);
  }

  assert(G->hasComdat());
  Metadata->setComdat(G->getComdat());
}

// Create a separate metadata global and put it in the appropriate ASan
// global registration section.
GlobalVariable *
ModuleFastAddressSanitizer::CreateMetadataGlobal(Module &M, Constant *Initializer,
                                             StringRef OriginalName) {
  auto Linkage = TargetTriple.isOSBinFormatMachO()
                     ? GlobalVariable::InternalLinkage
                     : GlobalVariable::PrivateLinkage;
  GlobalVariable *Metadata = new GlobalVariable(
      M, Initializer->getType(), false, Linkage, Initializer,
      Twine("__asan_global_") + GlobalValue::dropLLVMManglingEscape(OriginalName));
  Metadata->setSection(getGlobalMetadataSection());
  return Metadata;
}

IRBuilder<> ModuleFastAddressSanitizer::CreateAsanModuleDtor(Module &M) {
  AsanDtorFunction =
      Function::Create(FunctionType::get(Type::getVoidTy(*C), false),
                       GlobalValue::InternalLinkage, kAsanModuleDtorName, &M);
  BasicBlock *AsanDtorBB = BasicBlock::Create(*C, "", AsanDtorFunction);

  return IRBuilder<>(ReturnInst::Create(*C, AsanDtorBB));
}

void ModuleFastAddressSanitizer::InstrumentGlobalsCOFF(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());
  auto &DL = M.getDataLayout();

  for (size_t i = 0; i < ExtendedGlobals.size(); i++) {
    Constant *Initializer = MetadataInitializers[i];
    GlobalVariable *G = ExtendedGlobals[i];
    GlobalVariable *Metadata =
        CreateMetadataGlobal(M, Initializer, G->getName());

    // The MSVC linker always inserts padding when linking incrementally. We
    // cope with that by aligning each struct to its size, which must be a power
    // of two.
    unsigned SizeOfGlobalStruct = DL.getTypeAllocSize(Initializer->getType());
    assert(isPowerOf2_32(SizeOfGlobalStruct) &&
           "global metadata will not be padded appropriately");
    Metadata->setAlignment(assumeAligned(SizeOfGlobalStruct));

    SetComdatForGlobalMetadata(G, Metadata, "");
  }
}

void ModuleFastAddressSanitizer::InstrumentGlobalsELF(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers,
    const std::string &UniqueModuleId) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());

  SmallVector<GlobalValue *, 16> MetadataGlobals(ExtendedGlobals.size());
  for (size_t i = 0; i < ExtendedGlobals.size(); i++) {
    GlobalVariable *G = ExtendedGlobals[i];
    GlobalVariable *Metadata =
        CreateMetadataGlobal(M, MetadataInitializers[i], G->getName());
    MDNode *MD = MDNode::get(M.getContext(), ValueAsMetadata::get(G));
    Metadata->setMetadata(LLVMContext::MD_associated, MD);
    MetadataGlobals[i] = Metadata;

    SetComdatForGlobalMetadata(G, Metadata, UniqueModuleId);
  }

  // Update llvm.compiler.used, adding the new metadata globals. This is
  // needed so that during LTO these variables stay alive.
  if (!MetadataGlobals.empty())
    appendToCompilerUsed(M, MetadataGlobals);

  // RegisteredFlag serves two purposes. First, we can pass it to dladdr()
  // to look up the loaded image that contains it. Second, we can store in it
  // whether registration has already occurred, to prevent duplicate
  // registration.
  //
  // Common linkage ensures that there is only one global per shared library.
  GlobalVariable *RegisteredFlag = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::CommonLinkage,
      ConstantInt::get(IntptrTy, 0), kAsanGlobalsRegisteredFlagName);
  RegisteredFlag->setVisibility(GlobalVariable::HiddenVisibility);

  // Create start and stop symbols.
  GlobalVariable *StartELFMetadata = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::ExternalWeakLinkage, nullptr,
      "__start_" + getGlobalMetadataSection());
  StartELFMetadata->setVisibility(GlobalVariable::HiddenVisibility);
  GlobalVariable *StopELFMetadata = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::ExternalWeakLinkage, nullptr,
      "__stop_" + getGlobalMetadataSection());
  StopELFMetadata->setVisibility(GlobalVariable::HiddenVisibility);

  // Create a call to register the globals with the runtime.
  IRB.CreateCall(AsanRegisterElfGlobals,
                 {IRB.CreatePointerCast(RegisteredFlag, IntptrTy),
                  IRB.CreatePointerCast(StartELFMetadata, IntptrTy),
                  IRB.CreatePointerCast(StopELFMetadata, IntptrTy)});

  // We also need to unregister globals at the end, e.g., when a shared library
  // gets closed.
  IRBuilder<> IRB_Dtor = CreateAsanModuleDtor(M);
  IRB_Dtor.CreateCall(AsanUnregisterElfGlobals,
                      {IRB.CreatePointerCast(RegisteredFlag, IntptrTy),
                       IRB.CreatePointerCast(StartELFMetadata, IntptrTy),
                       IRB.CreatePointerCast(StopELFMetadata, IntptrTy)});
}

void ModuleFastAddressSanitizer::InstrumentGlobalsMachO(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());

  // On recent Mach-O platforms, use a structure which binds the liveness of
  // the global variable to the metadata struct. Keep the list of "Liveness" GV
  // created to be added to llvm.compiler.used
  StructType *LivenessTy = StructType::get(IntptrTy, IntptrTy);
  SmallVector<GlobalValue *, 16> LivenessGlobals(ExtendedGlobals.size());

  for (size_t i = 0; i < ExtendedGlobals.size(); i++) {
    Constant *Initializer = MetadataInitializers[i];
    GlobalVariable *G = ExtendedGlobals[i];
    GlobalVariable *Metadata =
        CreateMetadataGlobal(M, Initializer, G->getName());

    // On recent Mach-O platforms, we emit the global metadata in a way that
    // allows the linker to properly strip dead globals.
    auto LivenessBinder =
        ConstantStruct::get(LivenessTy, Initializer->getAggregateElement(0u),
                            ConstantExpr::getPointerCast(Metadata, IntptrTy));
    GlobalVariable *Liveness = new GlobalVariable(
        M, LivenessTy, false, GlobalVariable::InternalLinkage, LivenessBinder,
        Twine("__asan_binder_") + G->getName());
    Liveness->setSection("__DATA,__asan_liveness,regular,live_support");
    LivenessGlobals[i] = Liveness;
  }

  // Update llvm.compiler.used, adding the new liveness globals. This is
  // needed so that during LTO these variables stay alive. The alternative
  // would be to have the linker handling the LTO symbols, but libLTO
  // current API does not expose access to the section for each symbol.
  if (!LivenessGlobals.empty())
    appendToCompilerUsed(M, LivenessGlobals);

  // RegisteredFlag serves two purposes. First, we can pass it to dladdr()
  // to look up the loaded image that contains it. Second, we can store in it
  // whether registration has already occurred, to prevent duplicate
  // registration.
  //
  // common linkage ensures that there is only one global per shared library.
  GlobalVariable *RegisteredFlag = new GlobalVariable(
      M, IntptrTy, false, GlobalVariable::CommonLinkage,
      ConstantInt::get(IntptrTy, 0), kAsanGlobalsRegisteredFlagName);
  RegisteredFlag->setVisibility(GlobalVariable::HiddenVisibility);

  IRB.CreateCall(AsanRegisterImageGlobals,
                 {IRB.CreatePointerCast(RegisteredFlag, IntptrTy)});

  // We also need to unregister globals at the end, e.g., when a shared library
  // gets closed.
  IRBuilder<> IRB_Dtor = CreateAsanModuleDtor(M);
  IRB_Dtor.CreateCall(AsanUnregisterImageGlobals,
                      {IRB.CreatePointerCast(RegisteredFlag, IntptrTy)});
}

void ModuleFastAddressSanitizer::InstrumentGlobalsWithMetadataArray(
    IRBuilder<> &IRB, Module &M, ArrayRef<GlobalVariable *> ExtendedGlobals,
    ArrayRef<Constant *> MetadataInitializers) {
  assert(ExtendedGlobals.size() == MetadataInitializers.size());
  unsigned N = ExtendedGlobals.size();
  assert(N > 0);

  // On platforms that don't have a custom metadata section, we emit an array
  // of global metadata structures.
  ArrayType *ArrayOfGlobalStructTy =
      ArrayType::get(MetadataInitializers[0]->getType(), N);
  auto AllGlobals = new GlobalVariable(
      M, ArrayOfGlobalStructTy, false, GlobalVariable::InternalLinkage,
      ConstantArray::get(ArrayOfGlobalStructTy, MetadataInitializers), "");
  if (Mapping.Scale > 3)
    AllGlobals->setAlignment(Align(1ULL << Mapping.Scale));

  IRB.CreateCall(AsanRegisterGlobals,
                 {IRB.CreatePointerCast(AllGlobals, IntptrTy),
                  ConstantInt::get(IntptrTy, N)});

  // We also need to unregister globals at the end, e.g., when a shared library
  // gets closed.
  IRBuilder<> IRB_Dtor = CreateAsanModuleDtor(M);
  IRB_Dtor.CreateCall(AsanUnregisterGlobals,
                      {IRB.CreatePointerCast(AllGlobals, IntptrTy),
                       ConstantInt::get(IntptrTy, N)});
}

// This function replaces all global variables with new variables that have
// trailing redzones. It also creates a function that poisons
// redzones and inserts this function into llvm.global_ctors.
// Sets *CtorComdat to true if the global registration code emitted into the
// asan constructor is comdat-compatible.
bool ModuleFastAddressSanitizer::InstrumentGlobals(IRBuilder<> &IRB, Module &M,
                                               bool *CtorComdat) {
  *CtorComdat = false;

  SmallVector<GlobalVariable *, 16> GlobalsToChange;

  for (auto &G : M.globals()) {
    if (ShouldInstrumentGlobal(&G)) GlobalsToChange.push_back(&G);
  }

  size_t n = GlobalsToChange.size();
  if (n == 0) {
    *CtorComdat = true;
    return false;
  }

  auto &DL = M.getDataLayout();

  // A global is described by a structure
  //   size_t beg;
  //   size_t size;
  //   size_t size_with_redzone;
  //   const char *name;
  //   const char *module_name;
  //   size_t has_dynamic_init;
  //   void *source_location;
  //   size_t odr_indicator;
  // We initialize an array of such structures and pass it to a run-time call.
  StructType *GlobalStructTy =
      StructType::get(IntptrTy, IntptrTy, IntptrTy, IntptrTy, IntptrTy,
                      IntptrTy, IntptrTy, IntptrTy);
  SmallVector<GlobalVariable *, 16> NewGlobals(n);
  SmallVector<Constant *, 16> Initializers(n);

  bool HasDynamicallyInitializedGlobals = false;

  // We shouldn't merge same module names, as this string serves as unique
  // module ID in runtime.
  GlobalVariable *ModuleName = createPrivateGlobalForString(
      M, M.getModuleIdentifier(), /*AllowMerging*/ false, kAsanGenPrefix);

  for (size_t i = 0; i < n; i++) {
    static const uint64_t kMaxGlobalRedzone = 1 << 18;
    GlobalVariable *G = GlobalsToChange[i];

    // FIXME: Metadata should be attched directly to the global directly instead
    // of being added to llvm.asan.globals.
    auto MD = GlobalsMD.get(G);
    StringRef NameForGlobal = G->getName();
    // Create string holding the global name (use global name from metadata
    // if it's available, otherwise just write the name of global variable).
    GlobalVariable *Name = createPrivateGlobalForString(
        M, MD.Name.empty() ? NameForGlobal : MD.Name,
        /*AllowMerging*/ true, kAsanGenPrefix);

    Type *Ty = G->getValueType();
    uint64_t SizeInBytes = DL.getTypeAllocSize(Ty);
    uint64_t MinRZ = MinRedzoneSizeForGlobal();
    // MinRZ <= RZ <= kMaxGlobalRedzone
    // and trying to make RZ to be ~ 1/4 of SizeInBytes.
    uint64_t RZ = std::max(
        MinRZ, std::min(kMaxGlobalRedzone, (SizeInBytes / MinRZ / 4) * MinRZ));
    uint64_t RightRedzoneSize = RZ;
    // Round up to MinRZ
    if (SizeInBytes % MinRZ) RightRedzoneSize += MinRZ - (SizeInBytes % MinRZ);
    assert(((RightRedzoneSize + SizeInBytes) % MinRZ) == 0);
    Type *RightRedZoneTy = ArrayType::get(IRB.getInt8Ty(), RightRedzoneSize);

    StructType *NewTy = StructType::get(Ty, RightRedZoneTy);
    Constant *NewInitializer = ConstantStruct::get(
        NewTy, G->getInitializer(), Constant::getNullValue(RightRedZoneTy));

    // Create a new global variable with enough space for a redzone.
    GlobalValue::LinkageTypes Linkage = G->getLinkage();
    if (G->isConstant() && Linkage == GlobalValue::PrivateLinkage)
      Linkage = GlobalValue::InternalLinkage;
    GlobalVariable *NewGlobal =
        new GlobalVariable(M, NewTy, G->isConstant(), Linkage, NewInitializer,
                           "", G, G->getThreadLocalMode());
    NewGlobal->copyAttributesFrom(G);
    NewGlobal->setComdat(G->getComdat());
    NewGlobal->setAlignment(MaybeAlign(MinRZ));
    // Don't fold globals with redzones. ODR violation detector and redzone
    // poisoning implicitly creates a dependence on the global's address, so it
    // is no longer valid for it to be marked unnamed_addr.
    NewGlobal->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

    // Move null-terminated C strings to "__asan_cstring" section on Darwin.
    if (TargetTriple.isOSBinFormatMachO() && !G->hasSection() &&
        G->isConstant()) {
      auto Seq = dyn_cast<ConstantDataSequential>(G->getInitializer());
      if (Seq && Seq->isCString())
        NewGlobal->setSection("__TEXT,__asan_cstring,regular");
    }

    // Transfer the debug info.  The payload starts at offset zero so we can
    // copy the debug info over as is.
    SmallVector<DIGlobalVariableExpression *, 1> GVs;
    G->getDebugInfo(GVs);
    for (auto *GV : GVs)
      NewGlobal->addDebugInfo(GV);

    Value *Indices2[2];
    Indices2[0] = IRB.getInt32(0);
    Indices2[1] = IRB.getInt32(0);

    G->replaceAllUsesWith(
        ConstantExpr::getGetElementPtr(NewTy, NewGlobal, Indices2, true));
    NewGlobal->takeName(G);
    G->eraseFromParent();
    NewGlobals[i] = NewGlobal;

    Constant *SourceLoc;
    if (!MD.SourceLoc.empty()) {
      auto SourceLocGlobal = createPrivateGlobalForSourceLoc(M, MD.SourceLoc);
      SourceLoc = ConstantExpr::getPointerCast(SourceLocGlobal, IntptrTy);
    } else {
      SourceLoc = ConstantInt::get(IntptrTy, 0);
    }

    Constant *ODRIndicator = ConstantExpr::getNullValue(IRB.getInt8PtrTy());
    GlobalValue *InstrumentedGlobal = NewGlobal;

    bool CanUsePrivateAliases =
        TargetTriple.isOSBinFormatELF() || TargetTriple.isOSBinFormatMachO() ||
        TargetTriple.isOSBinFormatWasm();
    if (CanUsePrivateAliases && UsePrivateAlias) {
      // Create local alias for NewGlobal to avoid crash on ODR between
      // instrumented and non-instrumented libraries.
      InstrumentedGlobal =
          GlobalAlias::create(GlobalValue::PrivateLinkage, "", NewGlobal);
    }

    // ODR should not happen for local linkage.
    if (NewGlobal->hasLocalLinkage()) {
      ODRIndicator = ConstantExpr::getIntToPtr(ConstantInt::get(IntptrTy, -1),
                                               IRB.getInt8PtrTy());
    } else if (UseOdrIndicator) {
      // With local aliases, we need to provide another externally visible
      // symbol __odr_asan_XXX to detect ODR violation.
      auto *ODRIndicatorSym =
          new GlobalVariable(M, IRB.getInt8Ty(), false, Linkage,
                             Constant::getNullValue(IRB.getInt8Ty()),
                             kODRGenPrefix + NameForGlobal, nullptr,
                             NewGlobal->getThreadLocalMode());

      // Set meaningful attributes for indicator symbol.
      ODRIndicatorSym->setVisibility(NewGlobal->getVisibility());
      ODRIndicatorSym->setDLLStorageClass(NewGlobal->getDLLStorageClass());
      ODRIndicatorSym->setAlignment(Align::None());
      ODRIndicator = ODRIndicatorSym;
    }

    Constant *Initializer = ConstantStruct::get(
        GlobalStructTy,
        ConstantExpr::getPointerCast(InstrumentedGlobal, IntptrTy),
        ConstantInt::get(IntptrTy, SizeInBytes),
        ConstantInt::get(IntptrTy, SizeInBytes + RightRedzoneSize),
        ConstantExpr::getPointerCast(Name, IntptrTy),
        ConstantExpr::getPointerCast(ModuleName, IntptrTy),
        ConstantInt::get(IntptrTy, MD.IsDynInit), SourceLoc,
        ConstantExpr::getPointerCast(ODRIndicator, IntptrTy));

    if (ClInitializers && MD.IsDynInit) HasDynamicallyInitializedGlobals = true;

    LLVM_DEBUG(dbgs() << "NEW GLOBAL: " << *NewGlobal << "\n");

    Initializers[i] = Initializer;
  }

  // Add instrumented globals to llvm.compiler.used list to avoid LTO from
  // ConstantMerge'ing them.
  SmallVector<GlobalValue *, 16> GlobalsToAddToUsedList;
  for (size_t i = 0; i < n; i++) {
    GlobalVariable *G = NewGlobals[i];
    if (G->getName().empty()) continue;
    GlobalsToAddToUsedList.push_back(G);
  }
  appendToCompilerUsed(M, ArrayRef<GlobalValue *>(GlobalsToAddToUsedList));

  std::string ELFUniqueModuleId =
      (UseGlobalsGC && TargetTriple.isOSBinFormatELF()) ? getUniqueModuleId(&M)
                                                        : "";

  if (!ELFUniqueModuleId.empty()) {
    InstrumentGlobalsELF(IRB, M, NewGlobals, Initializers, ELFUniqueModuleId);
    *CtorComdat = true;
  } else if (UseGlobalsGC && TargetTriple.isOSBinFormatCOFF()) {
    InstrumentGlobalsCOFF(IRB, M, NewGlobals, Initializers);
  } else if (UseGlobalsGC && ShouldUseMachOGlobalsSection()) {
    InstrumentGlobalsMachO(IRB, M, NewGlobals, Initializers);
  } else {
    InstrumentGlobalsWithMetadataArray(IRB, M, NewGlobals, Initializers);
  }

  // Create calls for poisoning before initializers run and unpoisoning after.
  if (HasDynamicallyInitializedGlobals)
    createInitializerPoisonCalls(M, ModuleName);

  LLVM_DEBUG(dbgs() << M);
  return true;
}

int ModuleFastAddressSanitizer::GetAsanVersion(const Module &M) const {
  int LongSize = M.getDataLayout().getPointerSizeInBits();
  bool isAndroid = Triple(M.getTargetTriple()).isAndroid();
  int Version = 8;
  // 32-bit Android is one version ahead because of the switch to dynamic
  // shadow.
  Version += (LongSize == 32 && isAndroid);
  return Version;
}

static bool updateInitializer(Constant *Initializer, LLVMContext &C, DenseSet<Value*> &UpdatedList, const DataLayout &DL) {
	auto CE = dyn_cast<ConstantExpr>(Initializer);
	//errs() << "INIT: " << *Initializer << "\n";
	if (UpdatedList.count(Initializer)) {
		return false;
	}
	UpdatedList.insert(Initializer);
	if (CE && CE->getOpcode() == Instruction::GetElementPtr) {

		bool AllZeros = true;
  	for (unsigned i = 1, e = CE->getNumOperands(); i != e; ++i) {
			auto OpC = cast<ConstantInt>(CE->getOperand(1));
    	if (!OpC->isZero()) {
				AllZeros = false;
      	break;
			}
  	}
		if (AllZeros) {
			return false;
		}

		auto Int8PtrTy = Type::getInt8PtrTy(C);
		auto Int8Ty = Type::getInt8Ty(C);
		auto Int64Ty = Type::getInt64Ty(C);
		auto Base = CE->getOperand(0);
		Constant *Res = NULL;
		Type *BaseTy = Base->getType();

		if (BaseTy != Int8PtrTy) {
			//errs() << "Base: " << *Base << "\n";
			Res = ConstantExpr::getBitCast(Base, Int8PtrTy);
    	Res = ConstantExpr::getGetElementPtr(Int8Ty, Res, ConstantInt::get(Int64Ty, (0xFFFEULL<<48)));
    	Res = ConstantExpr::getBitCast(Res, BaseTy);
			//errs() << "Res: " << *Res << "\n";
		}
		else {
    	Res = ConstantExpr::getGetElementPtr(Int8Ty, Base, ConstantInt::get(Int64Ty, (0xFFFEULL<<48)));
		}
		//errs() << "Res: " << *Res << "\n";
		CE->handleOperandChange(Base, Res);
		//errs() << "OperandChangeDone\n";
		return true;
	}
	for (unsigned i = 0; i < Initializer->getNumOperands(); i++) {
  	Constant *Val = cast<Constant>(Initializer->getOperand(i));
		assert(Val);
		if (!isa<ConstantInt>(Val)) {
			if (updateInitializer(Val, C, UpdatedList, DL)) {
				UpdatedList.insert(Initializer->getOperand(i));
			}
		}
	}
	return false;
}

static void instrumentGlobal(Module &M, GlobalVariable *GV, DenseSet<Value*> &UpdatedList) {
  Constant *Initializer = GV->getInitializer();
  auto C = &(M.getContext());
	auto Int64Ty = Type::getInt64Ty(*C);
  const DataLayout &DL = M.getDataLayout();
  uint64_t SizeInBytes =
      DL.getTypeAllocSize(Initializer->getType());
  uint64_t Padding = alignTo(8, GV->getAlignment());
	std::vector<uint8_t> Init(Padding, 0);
	uint64_t HeaderVal = ((SizeInBytes << 32) | 0xfaceULL);
	uint8_t *Data = (uint8_t*)&HeaderVal;
	for (uint64_t i = Padding - 8; i < Padding; i++) {
		Init[i] = *Data;
		Data++;
	}

	if (Initializer) {
		updateInitializer(Initializer, *C, UpdatedList, DL);
	}

	Constant *Pad = ConstantDataArray::get(*C, Init);

	Initializer = ConstantStruct::getAnon({Pad, Initializer});

  auto *NewGV = new GlobalVariable(M, Initializer->getType(), GV->isConstant(),
                                   GlobalValue::ExternalLinkage, Initializer,
                                   GV->getName() + ".fastsan");
  NewGV->copyAttributesFrom(GV);
  NewGV->setLinkage(GlobalValue::PrivateLinkage);
  NewGV->copyMetadata(GV, 0);
  NewGV->setAlignment(MaybeAlign(GV->getAlignment()));

  NewGV->setUnnamedAddr(GlobalValue::UnnamedAddr::None);

  Constant *Aliasee = ConstantExpr::getIntToPtr(
      ConstantExpr::getAdd(
          ConstantExpr::getPtrToInt(NewGV, Int64Ty),
          ConstantInt::get(Int64Ty, Padding)),
      GV->getType());
  auto *Alias = GlobalAlias::create(GV->getValueType(), GV->getAddressSpace(),
                                    GV->getLinkage(), "", Aliasee, &M);
  Alias->setVisibility(GV->getVisibility());
  Alias->takeName(GV);
  GV->replaceAllUsesWith(Alias);
  GV->eraseFromParent();
}



bool ModuleFastAddressSanitizer::instrumentModuleNew(Module &M) {
  std::vector<GlobalVariable *> Globals;
  for (GlobalVariable &GV : M.globals()) {
    if (GV.isDeclarationForLinker() || GV.getName().startswith("llvm.") ||
        GV.isThreadLocal())
      continue;

    if (GV.hasCommonLinkage()) {
			GV.setLinkage(llvm::GlobalVariable::WeakAnyLinkage);
		}

    if (GV.hasSection()) {
      continue;
		}

    Globals.push_back(&GV);
  }

	DenseSet<Value*> UpdatedList;
  for (GlobalVariable *GV : Globals) {
    instrumentGlobal(M, GV, UpdatedList);
  }
	return true;
}

bool ModuleFastAddressSanitizer::instrumentModule(Module &M) {
	instrumentModuleNew(M);
	if (!CompileKernel)
		return false;
//#if 0
  initializeCallbacks(M);

  if (CompileKernel)
    return false;

  // Create a module constructor. A destructor is created lazily because not all
  // platforms, and not all modules need it.
  std::string AsanVersion = std::to_string(GetAsanVersion(M));
  std::string VersionCheckName =
      ClInsertVersionCheck ? (kAsanVersionCheckNamePrefix + AsanVersion) : "";
  std::tie(AsanCtorFunction, std::ignore) = createSanitizerCtorAndInitFunctions(
      M, kAsanModuleCtorName, kAsanInitName, /*InitArgTypes=*/{},
      /*InitArgs=*/{}, VersionCheckName);

  bool CtorComdat = true;
  // TODO(glider): temporarily disabled globals instrumentation for KASan.
  if (ClGlobals) {
    IRBuilder<> IRB(AsanCtorFunction->getEntryBlock().getTerminator());
    InstrumentGlobals(IRB, M, &CtorComdat);
  }

  const uint64_t Priority = GetCtorAndDtorPriority(TargetTriple);

  // Put the constructor and destructor in comdat if both
  // (1) global instrumentation is not TU-specific
  // (2) target is ELF.
  if (UseCtorComdat && TargetTriple.isOSBinFormatELF() && CtorComdat) {
    AsanCtorFunction->setComdat(M.getOrInsertComdat(kAsanModuleCtorName));
    appendToGlobalCtors(M, AsanCtorFunction, Priority, AsanCtorFunction);
    if (AsanDtorFunction) {
      AsanDtorFunction->setComdat(M.getOrInsertComdat(kAsanModuleDtorName));
      appendToGlobalDtors(M, AsanDtorFunction, Priority, AsanDtorFunction);
    }
  } else {
    appendToGlobalCtors(M, AsanCtorFunction, Priority);
    if (AsanDtorFunction)
      appendToGlobalDtors(M, AsanDtorFunction, Priority);
  }
//#endif

  return true;
}

void FastAddressSanitizer::initializeCallbacks(Module &M) {
  IRBuilder<> IRB(*C);
  // Create __asan_report* callbacks.
  // IsWrite, TypeSize and Exp are encoded in the function name.
  for (int Exp = 0; Exp < 2; Exp++) {
    for (size_t AccessIsWrite = 0; AccessIsWrite <= 1; AccessIsWrite++) {
      const std::string TypeStr = AccessIsWrite ? "store" : "load";
      const std::string ExpStr = Exp ? "exp_" : "";
      const std::string EndingStr = Recover ? "_noabort" : "";

      SmallVector<Type *, 3> Args2 = {IntptrTy, IntptrTy};
      SmallVector<Type *, 2> Args1{1, IntptrTy};
      if (Exp) {
        Type *ExpType = Type::getInt32Ty(*C);
        Args2.push_back(ExpType);
        Args1.push_back(ExpType);
      }
      AsanErrorCallbackSized[AccessIsWrite][Exp] = M.getOrInsertFunction(
          kAsanReportErrorTemplate + ExpStr + TypeStr + "_n" + EndingStr,
          FunctionType::get(IRB.getVoidTy(), Args2, false));

      AsanMemoryAccessCallbackSized[AccessIsWrite][Exp] = M.getOrInsertFunction(
          ClMemoryAccessCallbackPrefix + ExpStr + TypeStr + "N" + EndingStr,
          FunctionType::get(IRB.getVoidTy(), Args2, false));

      for (size_t AccessSizeIndex = 0; AccessSizeIndex < kNumberOfAccessSizes;
           AccessSizeIndex++) {
        const std::string Suffix = TypeStr + itostr(1ULL << AccessSizeIndex);
        AsanErrorCallback[AccessIsWrite][Exp][AccessSizeIndex] =
            M.getOrInsertFunction(
                kAsanReportErrorTemplate + ExpStr + Suffix + EndingStr,
                FunctionType::get(IRB.getVoidTy(), Args1, false));

        AsanMemoryAccessCallback[AccessIsWrite][Exp][AccessSizeIndex] =
            M.getOrInsertFunction(
                ClMemoryAccessCallbackPrefix + ExpStr + Suffix + EndingStr,
                FunctionType::get(IRB.getVoidTy(), Args1, false));
      }
    }
  }

  const std::string MemIntrinCallbackPrefix =
      CompileKernel ? std::string("") : ClMemoryAccessCallbackPrefix;
  AsanMemmove = M.getOrInsertFunction(MemIntrinCallbackPrefix + "memmove",
                                      IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                                      IRB.getInt8PtrTy(), IntptrTy);
  AsanMemcpy = M.getOrInsertFunction(MemIntrinCallbackPrefix + "memcpy",
                                     IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                                     IRB.getInt8PtrTy(), IntptrTy);
  AsanMemset = M.getOrInsertFunction(MemIntrinCallbackPrefix + "memset",
                                     IRB.getInt8PtrTy(), IRB.getInt8PtrTy(),
                                     IRB.getInt32Ty(), IntptrTy);

  AsanHandleNoReturnFunc =
      M.getOrInsertFunction(kAsanHandleNoReturnName, IRB.getVoidTy());

  AsanPtrCmpFunction =
      M.getOrInsertFunction(kAsanPtrCmp, IRB.getVoidTy(), IntptrTy, IntptrTy);
  AsanPtrSubFunction =
      M.getOrInsertFunction(kAsanPtrSub, IRB.getVoidTy(), IntptrTy, IntptrTy);
  // We insert an empty inline asm after __asan_report* to avoid callback merge.
  EmptyAsm = InlineAsm::get(FunctionType::get(IRB.getVoidTy(), false),
                            StringRef(""), StringRef(""),
                            /*hasSideEffects=*/true);
  if (Mapping.InGlobal)
    AsanShadowGlobal = M.getOrInsertGlobal("__asan_shadow",
                                           ArrayType::get(IRB.getInt8Ty(), 0));
}

bool FastAddressSanitizer::maybeInsertAsanInitAtFunctionEntry(Function &F) {
  // For each NSObject descendant having a +load method, this method is invoked
  // by the ObjC runtime before any of the static constructors is called.
  // Therefore we need to instrument such methods with a call to __asan_init
  // at the beginning in order to initialize our runtime before any access to
  // the shadow memory.
  // We cannot just ignore these methods, because they may call other
  // instrumented functions.
  if (F.getName().find(" load]") != std::string::npos) {
    FunctionCallee AsanInitFunction =
        declareSanitizerInitFunction(*F.getParent(), kAsanInitName, {});
    IRBuilder<> IRB(&F.front(), F.front().begin());
    IRB.CreateCall(AsanInitFunction, {});
    return true;
  }
  return false;
}

void FastAddressSanitizer::maybeInsertDynamicShadowAtFunctionEntry(Function &F) {
  // Generate code only when dynamic addressing is needed.
  if (Mapping.Offset != kDynamicShadowSentinel)
    return;

  IRBuilder<> IRB(&F.front().front());
  if (Mapping.InGlobal) {
    if (ClWithIfuncSuppressRemat) {
      // An empty inline asm with input reg == output reg.
      // An opaque pointer-to-int cast, basically.
      InlineAsm *Asm = InlineAsm::get(
          FunctionType::get(IntptrTy, {AsanShadowGlobal->getType()}, false),
          StringRef(""), StringRef("=r,0"),
          /*hasSideEffects=*/false);
      LocalDynamicShadow =
          IRB.CreateCall(Asm, {AsanShadowGlobal}, ".asan.shadow");
    } else {
      LocalDynamicShadow =
          IRB.CreatePointerCast(AsanShadowGlobal, IntptrTy, ".asan.shadow");
    }
  } else {
    Value *GlobalDynamicAddress = F.getParent()->getOrInsertGlobal(
        kAsanShadowMemoryDynamicAddress, IntptrTy);
    LocalDynamicShadow = IRB.CreateLoad(IntptrTy, GlobalDynamicAddress);
  }
}

void FastAddressSanitizer::markEscapedLocalAllocas(Function &F) {
  // Find the one possible call to llvm.localescape and pre-mark allocas passed
  // to it as uninteresting. This assumes we haven't started processing allocas
  // yet. This check is done up front because iterating the use list in
  // isInterestingAlloca would be algorithmically slower.
  assert(ProcessedAllocas.empty() && "must process localescape before allocas");

  // Try to get the declaration of llvm.localescape. If it's not in the module,
  // we can exit early.
  if (!F.getParent()->getFunction("llvm.localescape")) return;

  // Look for a call to llvm.localescape call in the entry block. It can't be in
  // any other block.
  for (Instruction &I : F.getEntryBlock()) {
    IntrinsicInst *II = dyn_cast<IntrinsicInst>(&I);
    if (II && II->getIntrinsicID() == Intrinsic::localescape) {
      // We found a call. Mark all the allocas passed in as uninteresting.
      for (Value *Arg : II->arg_operands()) {
        AllocaInst *AI = dyn_cast<AllocaInst>(Arg->stripPointerCasts());
        assert(AI && AI->isStaticAlloca() &&
               "non-static alloca arg to localescape");
        ProcessedAllocas[AI] = false;
      }
      break;
    }
  }
}

static uint64_t
fetchMallocSize(Value *V, const TargetLibraryInfo *TLI)
{
	if (auto CI = dyn_cast<CallInst>(V)) {
		LibFunc Func;
		if (TLI->getLibFunc(ImmutableCallSite(CI), Func)) {
			auto Name = CI->getCalledFunction()->getName();
			if (Name == "malloc") {
				auto Sz = CI->getArgOperand(0);
				return (isa<ConstantInt>(Sz)) ? cast<ConstantInt>(Sz)->getZExtValue() : 0;
			}
			else if (Name == "calloc") {
				IRBuilder<> IRB(CI->getParent());
				IRB.SetInsertPoint(CI->getNextNode());
				auto Sz = CI->getArgOperand(0);
				auto Count = CI->getArgOperand(1);
				if (isa<ConstantInt>(Sz) && isa<ConstantInt>(Count)) {
					return (cast<ConstantInt>(Sz)->getZExtValue()) *
						(cast<ConstantInt>(Count)->getZExtValue());
				}
				return 0;
			}
			else if (Name == "realloc") {
				auto Sz = CI->getArgOperand(1);
				return (isa<ConstantInt>(Sz)) ? cast<ConstantInt>(Sz)->getZExtValue() : 0;
			}
			/*else if (Name == "__ctype_b_loc") {
				return 128 * sizeof(unsigned short);
			}
			else if (Name == "__ctype_toupper_loc" || Name == "__ctype_tolower_loc") {
				return 128 * sizeof(int);
			}*/
		}
	}
	return 0;
}


static uint64_t getKnownObjSize(Value *V, const DataLayout &DL, bool &Static, const TargetLibraryInfo *TLI) {
	uint64_t Size;
  ObjectSizeOpts Opts;
  Opts.RoundToAlign = true;
  Opts.NullIsUnknownSize = true;
  if (getObjectSize(V, Size, DL, TLI, Opts)) {
		Static = true;
    return Size;
	}
	Size = fetchMallocSize(V, TLI);
	if (Size) {
		Static = true;
		return Size;
	}
	Static = false;
	auto Ty = V->getType()->getPointerElementType();
	return (Ty->isSized()) ? DL.getTypeAllocSize(Ty) : 0;
}

static Value *getAllocaSize(AllocaInst *AI)
{
	assert(!AI->isStaticAlloca());
	Type *Ty = AI->getAllocatedType();
  uint64_t SizeInBytes = AI->getModule()->getDataLayout().getTypeAllocSize(Ty);
	IRBuilder<> IRB(AI->getParent());
	IRB.SetInsertPoint(AI);
	Value *ArrSz = AI->getArraySize();
	if (ArrSz->getType()->isPointerTy()) {
		ArrSz = IRB.CreatePtrToInt(ArrSz, IRB.getInt64Ty());
	}
	else if (ArrSz->getType() != IRB.getInt64Ty()) {
		ArrSz = IRB.CreateZExt(ArrSz, IRB.getInt64Ty());
	}
	Value *Sz = IRB.CreateMul(ArrSz, ConstantInt::get(IRB.getInt64Ty(), SizeInBytes));
	return Sz;
}

Value* FastAddressSanitizer::getStaticBaseSize(Function &F, const Value *V1, const DataLayout &DL, const TargetLibraryInfo *TLI)
{
	Value *V = const_cast<Value*>(V1);
	bool Static;
	uint64_t Size = getKnownObjSize(V, DL, Static, TLI);
	if (Static) {
		return ConstantInt::get(Int64Ty, Size);
	}
	if (auto CI = dyn_cast<CallInst>(V)) {
		LibFunc Func;
		if (TLI->getLibFunc(ImmutableCallSite(CI), Func)) {
			auto Name = CI->getCalledFunction()->getName();
			if (Name == "malloc") {
				return CI->getArgOperand(0);
			}
			else if (Name == "calloc") {
				IRBuilder<> IRB(CI->getParent());
				IRB.SetInsertPoint(CI->getNextNode());
				return IRB.CreateMul(CI->getArgOperand(0), CI->getArgOperand(1));
			}
			else if (Name == "realloc") {
				return CI->getArgOperand(1);
			}
			/*else if (Name == "__ctype_b_loc") {
				assert(0);
				return ConstantInt::get(Int64Ty, 128 * sizeof(unsigned short));
			}
			else if (Name == "__ctype_toupper_loc" || Name == "__ctype_tolower_loc") {
				assert(0);
				return ConstantInt::get(Int64Ty, 128 * sizeof(int));
			}*/
		}
	}

	auto AI = dyn_cast<AllocaInst>(V);
	if (AI && !AI->isStaticAlloca()) {
		return getAllocaSize(AI);
	}

	auto GV = dyn_cast<GlobalVariable>(V);
	if (GV && GV->hasInitializer()) {
  	Constant *Initializer = GV->getInitializer();
  	return ConstantInt::get(Int64Ty, DL.getTypeAllocSize(Initializer->getType()));
	}
	return NULL;
}

static Value* sanGetLimit(Function &F, Value *V, IRBuilder<> &IRB)
{
	auto M = F.getParent();
	auto Fn = M->getOrInsertFunction("san_get_limit_must_check", IRB.getInt8PtrTy(), V->getType());
	auto Ret = IRB.CreateCall(Fn, {V});
	//errs() << "Adding in Get Limit:: " << *Ret << "\n";
	//errs() << *(Ret->getParent()) << "\n";
	return Ret;
}

static bool indefiniteBase(Value *V, const DataLayout &DL) {

  SmallPtrSet<Value *, 4> Visited;
  SmallVector<Value *, 4> Worklist;
  Worklist.push_back(V);

  while (!Worklist.empty())
	{
    Value *P = Worklist.pop_back_val();

    if (!Visited.insert(P).second)
      continue;

		if (isa<IntToPtrInst>(P) && !IsNonInteriorIntPtr(P, DL)) {
			return true;
		}


		if (isa<SelectInst>(P) || isa<PHINode>(P)) {
			auto U = cast<User>(P);
			for (unsigned i = 0; i < U->getNumOperands(); i++) {
				Worklist.push_back(U->getOperand(i));
			}
		}
	}

	return false;
}

Value* FastAddressSanitizer::getLimitSafe(Function &F, const Value *V1, const DataLayout &DL, const TargetLibraryInfo *TLI)
{
	Value *Ret = getStaticBaseSize(F, V1, DL, TLI);
	assert(Ret == NULL && "static base was possible");

	Value *V = const_cast<Value*>(V1);

	auto InstPt = dyn_cast<Instruction>(V);
	if (InstPt == NULL) {
		assert(isa<Argument>(V) || isa<GlobalVariable>(V));
		InstPt = &*F.begin()->getFirstInsertionPt();
	}
	else {
		if (isa<PHINode>(InstPt)) {
			InstPt = InstPt->getParent()->getFirstNonPHI();
		}
		else {
			InstPt = InstPt->getNextNode();
		}
	}

	IRBuilder<> IRB(InstPt);

	auto M = F.getParent();

	if (indefiniteBase(V, DL)) {
		auto Fn = M->getOrInsertFunction("san_get_limit_must_check", IRB.getInt8PtrTy(), V->getType());
		auto Ret = IRB.CreateCall(Fn, {V});
		//errs() << "Adding in Get Limit Safe:: " << *Ret << "\n";
		//errs() << *(Ret->getParent()) << "\n";
		return Ret;
	}

	auto Fn = M->getOrInsertFunction("san_get_limit_check", IRB.getInt8PtrTy(), V->getType());
	return IRB.CreateCall(Fn, {V});
}


Value* FastAddressSanitizer::getLimit(Function &F, const Value *V1, const DataLayout &DL, const TargetLibraryInfo *TLI)
{
	Value *Ret = getStaticBaseSize(F, V1, DL, TLI);
	assert(Ret == NULL && "static base was possible");

	Value *V = const_cast<Value*>(V1);

	auto InstPt = dyn_cast<Instruction>(V);
	if (InstPt == NULL) {
		assert(isa<Argument>(V) || isa<GlobalVariable>(V));
		InstPt = &*F.begin()->getFirstInsertionPt();
	}
	else {
		if (isa<PHINode>(InstPt)) {
			InstPt = InstPt->getParent()->getFirstNonPHI();
		}
		else {
			InstPt = InstPt->getNextNode();
		}
	}

	IRBuilder<> IRB(InstPt);

	if (indefiniteBase(V, DL)) {
		//V = sanGetBase(F, V, IRB);
		return sanGetLimit(F, V, IRB);
	}
	auto Int8PtrPtrTy = Int8PtrTy->getPointerTo();
	return IRB.CreateLoad(Int8PtrTy, IRB.CreateBitCast(V, Int8PtrPtrTy));
}

static bool isPtrMask(const Value *V)
{
  auto I = dyn_cast<IntrinsicInst>(V);
  return (I &&
    (I->getIntrinsicID() == Intrinsic::ptrmask ||
     I->getIntrinsicID() == Intrinsic::ptrmask1));
}

bool FastAddressSanitizer::isSafeAlloca(const AllocaInst *AllocaPtr, const TargetLibraryInfo *TLI)
{
  SmallPtrSet<const Value *, 16> Visited;
  SmallVector<const Value *, 8> WorkList;
  WorkList.push_back(AllocaPtr);

  // A DFS search through all uses of the alloca in bitcasts/PHI/GEPs/etc.
  while (!WorkList.empty()) {
    const Value *V = WorkList.pop_back_val();
    for (const Use &UI : V->uses()) {
      auto I = cast<const Instruction>(UI.getUser());
      assert(V == UI.get());

      switch (I->getOpcode()) {
			case Instruction::Load:
				break;
			case Instruction::VAArg:
				break;

      case Instruction::Store:
        if (V == I->getOperand(0)) {
					return false;
        }
        break;

      case Instruction::Ret:
        return false;

      case Instruction::Call:
      case Instruction::Invoke: {
        ImmutableCallSite CS(I);

        if (I->isLifetimeStartOrEnd())
          continue;
        if (dyn_cast<MemIntrinsic>(I)) {
        	continue;
        }

				if (isPtrMask(I)) {
          continue;
        }
				LibFunc Func;
    		if (TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
					if (!TLI->mayCapturePtr(Func)) {
						continue;
					}
				}

        ImmutableCallSite::arg_iterator B = CS.arg_begin(), E = CS.arg_end();
        for (ImmutableCallSite::arg_iterator A = B; A != E; ++A)
          if (A->get() == V)
            if (!(CS.doesNotCapture(A - B) && (CS.doesNotAccessMemory(A - B) ||
                                               CS.doesNotAccessMemory()))) {
              return false;
            }
        continue;
      }

      default:
        if (Visited.insert(I).second)
          WorkList.push_back(cast<const Instruction>(I));
      }
    }
  }

  // All uses of the alloca are safe, we can place it on the safe stack.
  return true;
}

bool static isAllocaCallSafe(const AllocaInst *AllocaPtr, const TargetLibraryInfo *TLI)
{
  SmallPtrSet<const Value *, 16> Visited;
  SmallVector<const Value *, 8> WorkList;
  WorkList.push_back(AllocaPtr);

  // A DFS search through all uses of the alloca in bitcasts/PHI/GEPs/etc.
  while (!WorkList.empty()) {
    const Value *V = WorkList.pop_back_val();
    for (const Use &UI : V->uses()) {
      auto I = cast<const Instruction>(UI.getUser());
      assert(V == UI.get());

      switch (I->getOpcode()) {
			case Instruction::Load:
				break;
			case Instruction::VAArg:
				break;

      case Instruction::Store:
        if (V == I->getOperand(0)) {
					return false;
        }
        break;

      case Instruction::Ret:
        return false;

      case Instruction::Call:
      case Instruction::Invoke: {
        ImmutableCallSite CS(I);

        if (I->isLifetimeStartOrEnd())
          continue;
        if (dyn_cast<MemIntrinsic>(I)) {
        	continue;
        }

				if (isPtrMask(I)) {
          continue;
        }
				LibFunc Func;
    		if (TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
					if (!TLI->mayCapturePtr(Func)) {
						continue;
					}
				}

        ImmutableCallSite::arg_iterator B = CS.arg_begin(), E = CS.arg_end();
        for (ImmutableCallSite::arg_iterator A = B; A != E; ++A)
          if (A->get() == V)
            if (!(CS.doesNotCapture(A - B))) {
              return false;
            }
        continue;
      }

      default:
        if (Visited.insert(I).second)
          WorkList.push_back(cast<const Instruction>(I));
      }
    }
  }

  // All uses of the alloca are safe, we can place it on the safe stack.
  return true;
}

static void addUnsafePointer(DenseMap<Value*, uint64_t> &Map, Value *V, uint64_t Size)
{
	if (Map.count(V)) {
		uint64_t PrevSize = Map[V];
		if (Size > PrevSize) {
			Map[V] = Size;
		}
	}
	else {
		Map[V] = Size;
	}
}

static bool
isNonAccessInst(const Instruction *I, Value *Ptr) {
	if (isa<MemIntrinsic>(I)) {
		return false;
	}
	if (isa<ReturnInst>(I) || isa<CallInst>(I)) {
		return true;
	}
	else if (auto SI = dyn_cast<StoreInst>(I)) {
		if (Ptr == SI->getValueOperand()) {
			return true;
		}
	}
	return false;
}

static bool
inSameLoop(const Value *Base, const Value *Ptr, LoopInfo &LI)
{
	if (isa<PHINode>(Base)) {
		//errs() << "Finding BASE: "<< *Base << "\n";
		auto L1 = LI.getLoopFor(cast<Instruction>(Base)->getParent());
		//errs() << "L1: " << L1 << "\n";
		if (L1 == NULL) {
			return true;
		}
		auto L2 = LI.getLoopFor(cast<Instruction>(Ptr)->getParent());
		//errs() << "L2: " << L2 << "\n";
		if (LI.isNotAlreadyContainedIn(L2, L1)) {
			//errs() << "L1 and L2 are different\n";
			return false;
		}
	}
	return true;
}

static bool
inSameLoop1(const Value *Base, const Value *Ptr1, const Value *Ptr2, LoopInfo &LI)
{
	if (isa<PHINode>(Base)) {
		//errs() << "Finding BASE: "<< *Base << "\n";
		auto L1 = LI.getLoopFor(cast<Instruction>(Ptr1)->getParent());
		//errs() << "L1: " << L1 << "\n";
		if (L1 == NULL) {
			return true;
		}
		auto L2 = LI.getLoopFor(cast<Instruction>(Ptr2)->getParent());
		//errs() << "L2: " << L2 << "\n";
		if (LI.isNotAlreadyContainedIn(L2, L1)) {
			//errs() << "L1 and L2 are different\n";
			return false;
		}
	}
	return true;
}

#if 0
static bool
hasUnsafeUse(Function &F, Instruction *Ptr, DenseSet<Value*> &UnsafeUses)
{
	for (const Use &UI : Ptr->uses()) {
	  auto I = cast<const Instruction>(UI.getUser());
		if (UnsafeUses.count(I)) {
			if (!isNonAccessInst(I, Ptr)) {
				return true;
			}
		}
	}
	return false;
}

static void
removeOnlyNonAccessPtrs(Function &F, DenseSet<Value*> &TmpSet, DenseSet<Value*> &UnsafeUses)
{
	DenseSet<Value*> ToDelete;
	for (auto Ptr : TmpSet) {
		if (!hasUnsafeUse(F, cast<Instruction>(Ptr), UnsafeUses)) {
			assert(0);
			ToDelete.insert(Ptr);
		}
	}

	for (auto Ptr : ToDelete) {
		assert(TmpSet.count(Ptr));
		TmpSet.erase(Ptr);
	}
}
#endif

static bool
mustAccessMemory(Instruction *I, const TargetLibraryInfo *TLI) {
	auto CS = dyn_cast<CallInst>(I);
	if (CS == NULL) {
		return false;
	}
	if (isa<MemIntrinsic>(CS)) {
		return true;
	}
	LibFunc Func;
  if (TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
		if (TLI->mustAccessMemory(Func)) {
			return true;
		}
	}
	return false;
}

static bool
postDominatesAnyUse(Function &F, Instruction *Ptr, PostDominatorTree &PDT,
	DenseSet<Value*> &UnsafeUses, LoopInfo &LI, const TargetLibraryInfo *TLI)
{
	//errs() << "CHECKING1 : " << *Ptr << "\n";
	for (const Use &UI : Ptr->uses()) {
	  auto I = cast<Instruction>(UI.getUser());
		bool MustAccessMem = UnsafeUses.count(I) ? false : mustAccessMemory(I, TLI);
		if (UnsafeUses.count(I) || MustAccessMem) {
			if ((MustAccessMem || !isNonAccessInst(I, Ptr)) && PDT.dominates(I, Ptr)) {
				if (inSameLoop(Ptr, I, LI)) {
					return true;
				}
			}
		}
	}
	return false;
}

static bool
mayBeNull(Instruction *Ptr) {
	for (const Use &UI : Ptr->uses()) {
	  auto I = dyn_cast<const ICmpInst>(UI.getUser());
		if (I) {
			auto Op1 = I->getOperand(0);
			auto Op2 = I->getOperand(1);
			assert(Ptr == Op1 || Ptr == Op2);
			auto Op = (Ptr == Op1) ? Op2 : Op1;
			if (isa<ConstantInt>(Op) || isa<ConstantPointerNull>(Op)) {
				return true;
			}
		}
	}
	return false;
}

static bool
postDominatesAnyPtrDef(Function &F, Instruction *Base, PostDominatorTree &PDT,
	DenseSet<Value*> &Ptrs, LoopInfo &LI, DenseMap<Value*, Value*> &LoopUsages,
	DenseSet<Value*> &CondLoop, bool &Recurrence)
{
	Recurrence = false;
	//errs() << "CHECKING2 : " << *Base << "\n";
	assert(!Ptrs.empty());

	for (const Use &UI : Base->uses()) {
	  auto I = dyn_cast<IntrinsicInst>(UI.getUser());
		if (I && I->getIntrinsicID() == Intrinsic::ptrmask) {
			if (mayBeNull(I)) {
				//errs() << "Returning FALSE1\n";
				return false;
			}
		}
	}

	for (auto V : Ptrs) {
	  auto I = cast<const Instruction>(V);
		assert(I);
		if (PDT.dominates(I, Base)) {
			if (inSameLoop(Base, I, LI)) {
				return true;
			}
		}
	}
	//errs() << "Returning FALSE\n";
	return false;
}

static bool
postDominatesAnyStore(Function &F, Value *V, PostDominatorTree &PDT, DenseSet<Instruction*> &Stores, LoopInfo &LI)
{
	assert(!Stores.empty());
	auto I = cast<const Instruction>(V);

	for (auto SI : Stores) {
		if (PDT.dominates(SI, I)) {
			if (inSameLoop(I, SI, LI)) {
				return true;
			}
		}
	}
	return false;
}


static void
abortIfTrue(Function &F, Instruction *InsertPt, Value *Base,
	Value *Ptr, Value *Limit, Value *TySize, Value *Callsite)
{
	//auto Int8PtrTy = Base->getType();
	auto M = F.getParent();
  //auto &C = M->getContext();
	const DataLayout &DL = F.getParent()->getDataLayout();

	//Instruction *Then =
    //    SplitBlockAndInsertIfThen(Cond, InsertPt, false);    //,
                                  //MDBuilder(C).createBranchWeights(1, 100000));
	IRBuilder<> IRB(InsertPt);
	FunctionCallee Fn;
	if (!indefiniteBase(Base, DL)) {
		Fn = M->getOrInsertFunction("san_abort2", IRB.getVoidTy(), Base->getType(),
			Ptr->getType(), Limit->getType(), TySize->getType(),
			IRB.getInt64Ty(), Callsite->getType(), IRB.getInt8PtrTy());
	}
	else {
		Fn = M->getOrInsertFunction("san_abort3", IRB.getVoidTy(), Base->getType(),
			Ptr->getType(), Limit->getType(), TySize->getType(),
			IRB.getInt64Ty(), Callsite->getType(), IRB.getInt8PtrTy());
	}
	auto Call = IRB.CreateCall(Fn, {Base, Ptr, Limit, TySize, ConstantInt::get(IRB.getInt64Ty(), 0),
		Callsite, Constant::getNullValue(IRB.getInt8PtrTy())});

	//auto Fn = M->getOrInsertFunction("san_abort2", IRB.getVoidTy());
	//auto Call = IRB.CreateCall(Fn, {});
	//Call->addAttribute(AttributeList::FunctionIndex, Attribute::Cold);

	if (F.getSubprogram()) {
    if (auto DL = InsertPt->getDebugLoc()) {
      Call->setDebugLoc(DL);
		}
  }
}

#if 0
static void
setInvalidBit(Function &F, Instruction *I, Value *Cmp, Value *V) {
	IRBuilder<> IRB(I);
	auto InvalidMask = IRB.CreateShl(IRB.CreateZExt(Cmp, IRB.getInt64Ty()), 48);
	auto TheFn = Intrinsic::getDeclaration(F.getParent(), Intrinsic::ptrunmask, {V->getType(), V->getType(), IRB.getInt64Ty()});
	auto NewV = IRB.CreateCall(TheFn, {V, InvalidMask});

	if (auto Ret = dyn_cast<ReturnInst>(I)) {
		if (V == Ret->getOperand(0)) {
			Ret->setOperand(0, NewV);
		}
	}
	else if (auto Call = dyn_cast<CallBase>(I)) {
		for (unsigned i = 0; i < Call->getNumOperands(); i++) {
			if (V == Call->getOperand(i)) {
				Call->setOperand(i, NewV);
			}
		}
	}
	else if (auto SI = dyn_cast<StoreInst>(I)) {
		if (V == SI->getOperand(0)) {
			SI->setOperand(0, NewV);
		}
	}
	else {
		assert(0);
	}
}
#endif

static void
instrumentAllUses(Function &F, Instruction *Ptr, Value *Base,
	DenseSet<Value*> &UnsafeUses,
	Value *Limit, Value *TySize, Value *Callsite) {

	for (const Use &UI : Ptr->uses()) {
	  auto I = cast<Instruction>(UI.getUser());
		if (UnsafeUses.count(I)) {
			if (!isNonAccessInst(I, Ptr)) {
				abortIfTrue(F, I, Base, Ptr, Limit, TySize, Callsite);
			}
			else {
				// THIS LOGIC DOESN'T WORK BECAUSE BASE CAN'T BE DEREFRENCED
				//setInvalidBit(F, I, Cmp, Ptr);
			}
		}
	}
}

static Instruction* getUseInBasicBlock(Instruction *Ptr) {
	for (const Use &UI : Ptr->uses()) {
	  auto I = cast<Instruction>(UI.getUser());
		if (!isa<PHINode>(I) && I->getParent() == Ptr->getParent()) {
			return I;
		}
	}
	return Ptr->getParent()->getTerminator();
}

#if 0
static Value* getPtrOffset(Function &F, IRBuilder<> &IRB, Value *V)
{
	auto Intrin = Intrinsic::ptroffset;

	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrin, {IRB.getInt64Ty(), V->getType(), IRB.getInt64Ty()});
	V = IRB.CreateCall(TheFn, {V, ConstantInt::get(IRB.getInt64Ty(), 49)});
	return V;
}
#endif

void FastAddressSanitizer::
addBoundsCheck(Function &F, Value *Base, Value *Ptr, Value *Limit,
	Value *TySize, DenseSet<Value*> &UnsafeUses, int &callsites,
	bool MayNull)
{
	auto InstPtr = dyn_cast<Instruction>(Ptr);
	assert(InstPtr && "Invalid Ptr");

	InstPtr = getUseInBasicBlock(InstPtr);


#if 0
	IRBuilder<> IRB(InstPtr);
	auto Base8 = IRB.CreateBitCast(Base, Int8PtrTy);
	auto BaseOffset = getPtrOffset(F, IRB, Base8);
	BaseOffset = IRB.CreateNeg(BaseOffset);
	auto NewBase = IRB.CreateGEP(Base8, BaseOffset);

	auto Ptr8 = IRB.CreateBitCast(Ptr, Int8PtrTy);
	Value *PtrLimit = IRB.CreateGEP(Int8Ty, Ptr8, TySize);
	if (Limit->getType()->isIntegerTy()) {
		Limit = IRB.CreateGEP(Int8Ty, Base8, Limit);
	}
	assert(Limit->getType() == Int8PtrTy);

	auto Cmp1 = IRB.CreateICmpULT(Ptr8, NewBase);
	auto Cmp2 = IRB.CreateICmpULT(Limit, PtrLimit);
	auto Cmp = IRB.CreateOr(Cmp1, Cmp2);
	auto CmpInst = dyn_cast<Instruction>(Cmp);
	assert(CmpInst && "no cmp inst");

	auto Intrinsic = dyn_cast<IntrinsicInst>(Base);
	if (Intrinsic && Intrinsic->getIntrinsicID() != Intrinsic::safe_load) {
		//if (Intrinsic->getIntrinsicID() != Intrinsic::ptrunmask) {
			errs() << "Base is Intrinsic\n" << *Base << "\n";
			errs() << F << "\n";
			assert(0);
		//}
	}
#endif

	if (!MayNull) {
		abortIfTrue(F, InstPtr, Base, Ptr, Limit, TySize, ConstantInt::get(Int32Ty, callsites));
	}
	else {
		instrumentAllUses(F, cast<Instruction>(Ptr), Base, UnsafeUses, Limit, TySize, ConstantInt::get(Int32Ty, callsites));
	}
	callsites++;
}

void FastAddressSanitizer::
addBoundsCheckWithLenAtUseHelper(Function &F, 
	Value *Base, Value *Ptr, Value *TySize, Instruction* InstPtr,
	int &callsites, 
	Value *Limit)
{
#if 0
	IRBuilder<> IRB(InstPtr);

	auto Intrinsic = dyn_cast<IntrinsicInst>(Base);
	if (Intrinsic && Intrinsic->getIntrinsicID() != Intrinsic::safe_load) {
		//if (Intrinsic->getIntrinsicID() != Intrinsic::ptrunmask) {
			errs() << "Base is Intrinsic\n" << *Base << "\n";
			errs() << F << "\n";
			assert(0);
		//}
	}

	auto Base8 = IRB.CreateBitCast(Base, Int8PtrTy);
	auto BaseOffset = getPtrOffset(F, IRB, Base8);
	BaseOffset = IRB.CreateNeg(BaseOffset);
	auto NewBase = IRB.CreateGEP(Base8, BaseOffset);


	auto Ptr8 = IRB.CreateBitCast(Ptr, Int8PtrTy);
	Value *PtrLimit = IRB.CreateGEP(Int8Ty, Ptr8, TySize);
	
	auto Cmp1 = IRB.CreateICmpULT(Ptr8, NewBase);
	auto Cmp2 = IRB.CreateICmpULT(Limit, PtrLimit);
	auto Cmp = IRB.CreateOr(Cmp1, Cmp2);
	auto CmpInst = dyn_cast<Instruction>(Cmp);
	assert(CmpInst && "no cmp inst");
#endif

	abortIfTrue(F, InstPtr, Base, Ptr, Limit, TySize, ConstantInt::get(Int32Ty, callsites));
	callsites++;
}

void FastAddressSanitizer::
addBoundsCheckWithLenAtUse(Function &F, Value *Base, Value *Ptr, Value *TySize,
	DenseSet<Value*> &UnsafeUses, int &callsites, DenseMap<Value*, Value*> &PtrUseToLenMap)
{
	for (const Use &UI : Ptr->uses()) {
	  auto I = cast<Instruction>(UI.getUser());
		if (UnsafeUses.count(I)) {
			if (!isNonAccessInst(I, Ptr)) {
				assert(PtrUseToLenMap.count(I));
				auto Limit = PtrUseToLenMap[I];
				addBoundsCheckWithLenAtUseHelper(F, Base, Ptr, TySize, I, callsites, Limit);
			}
			else {
				// THIS LOGIC DOESN'T WORK BECAUSE BASE CAN'T BE DEREFRENCED
			}
		}
	}
}

static Value*
addLengthAtPtrUseHelper(Function &F, Value *Base,
	DenseMap<Value*, Value*> &PtrUseToLenMap,
	DenseSet<Value*> &GetLengths,
	DenseMap<Value*, Value*> &LenToBaseMap,
	Instruction *User)
{
	auto InstPtr = User->getParent()->getFirstNonPHI();

	auto BaseI = dyn_cast<Instruction>(Base);
	if (BaseI && !isa<PHINode>(BaseI) && BaseI->getParent() == InstPtr->getParent()) {
		// CAN HAPPEN IF NULL CHECK ON BASE SOMEWHERE
		InstPtr = BaseI->getNextNode();
		//assert(0);
	}

	IRBuilder<> IRB(InstPtr);

	auto Int8PtrTy = IRB.getInt8PtrTy();
	const DataLayout &DL = F.getParent()->getDataLayout();
	Value *Limit;

	if (indefiniteBase(Base, DL)) {
		Limit = sanGetLimit(F, Base, IRB);
	}
	else {
		auto Int8PtrPtrTy = Int8PtrTy->getPointerTo();
		Limit = IRB.CreateLoad(Int8PtrTy, IRB.CreateBitCast(Base, Int8PtrPtrTy));
	}

	GetLengths.insert(Limit);
	LenToBaseMap[Limit] = Base;
	PtrUseToLenMap[User] = Limit;
	return Limit;
}


static void
addLengthAtPtrUse(Function &F, Value *Base, Value *Ptr,
	DenseMap<Value*, Value*> &PtrUseToLenMap,
	DenseSet<Value*> &UnsafeUses,
	DenseSet<Value*> &GetLengths,
	DenseMap<Value*, Value*> &LenToBaseMap)
{
	for (const Use &UI : Ptr->uses()) {
	  auto I = cast<Instruction>(UI.getUser());
		if (UnsafeUses.count(I)) {
			if (!isNonAccessInst(I, Ptr)) {
				addLengthAtPtrUseHelper(F, Base, PtrUseToLenMap, GetLengths, LenToBaseMap, I);
				assert(PtrUseToLenMap.count(I));
			}
		}
	}
}

static void
addLengthAtPtr(Function &F, Value *Base, Value *Ptr,
	DenseMap<Value*, Value*> &PtrToLenMap,
	DenseSet<Value*> &GetLengths,
	DenseSet<Value*> &GetLengthsCond,
	DenseMap<Value*, Value*> &LenToBaseMap,
	DenseMap<Value*, Value*> &LoopUsages,
	DenseSet<Value*> &CondLoop)
{
	auto InstPtr = dyn_cast<Instruction>(Ptr);
	assert(InstPtr && "Invalid Ptr");
	InstPtr = InstPtr->getParent()->getFirstNonPHI();

	if (LoopUsages.count(Ptr)) {
		InstPtr = cast<BasicBlock>(LoopUsages[Ptr])->getFirstNonPHI();
	}
	else {
		// CAN HAPPEN IF NULL CHECK ON BASE SOMEWHERE
		auto BaseI = dyn_cast<Instruction>(Base);
		if (BaseI && !isa<PHINode>(BaseI) && BaseI->getParent() == InstPtr->getParent()) {
			InstPtr = BaseI->getNextNode();
			//errs() << "Base: " << *Base << " Ptr:" << *Ptr << "\n";
			//errs() << "Basic Block: " << *BaseI->getParent() << "\n";
			//assert(0);
		}
	}

	IRBuilder<> IRB(InstPtr);

	auto Int8PtrTy = IRB.getInt8PtrTy();
	const DataLayout &DL = F.getParent()->getDataLayout();
	Value *Limit;

	if (indefiniteBase(Base, DL)) {
		Limit = sanGetLimit(F, Base, IRB);
	}
	else {
		auto Int8PtrPtrTy = Int8PtrTy->getPointerTo();
		Limit = IRB.CreateLoad(Int8PtrTy, IRB.CreateBitCast(Base, Int8PtrPtrTy));
	}

	if (CondLoop.count(Ptr)) {
		GetLengthsCond.insert(Limit);
	}

	GetLengths.insert(Limit);
	LenToBaseMap[Limit] = Base;
	PtrToLenMap[Ptr] = Limit;
}

static void createReplacementMap(Function *F, DenseMap<Value*, Value*> &ReplacementMap)
{
	auto Name = F->getName();
	if (!Name.startswith("san.interior")) {
		return;
	}
	
  Function::arg_iterator DestI = F->arg_begin();
	while (DestI != F->arg_end()) {
		if (DestI->getName().startswith("__interior")) {
			break;
		}
		DestI++;
	}

	assert(DestI != F->arg_end());
	auto InteriorBegin = DestI;
  Function::arg_iterator It = F->arg_begin();

	for (; It != InteriorBegin; It++) {
		if (It->getType()->isPointerTy()) {
			assert(DestI != F->arg_end());
			ReplacementMap[&*It] = &*DestI++;
		}
	}
}

static Value* tryGettingBaseAndOffset(Value *V, int64_t &Offset, const DataLayout &DL, DenseMap<Value*, Value*> &ReplacementMap) {
	Value *Ret = NULL;
	SmallVector<const Value *, 2> Objects;

	if (isa<UndefValue>(V)) {
		Offset = INVALID_OFFSET;
		return Constant::getNullValue(V->getType());
	}

	GetUnderlyingObjects1(V, Objects, DL);
	if (Objects.size() == 1) {
		Ret = const_cast<Value*>(Objects[0]);
		if (Ret->getType()->isIntegerTy()) {
			assert(0);
			Offset = INVALID_OFFSET;
			return Ret;
		}
		if (isa<Constant>(Ret) && !isa<GlobalVariable>(Ret)) {
			Offset = INVALID_OFFSET;
			return Constant::getNullValue(V->getType());
		}

		assert(!isa<PHINode>(Ret) && !isa<SelectInst>(Ret));
		Value *Base = GetPointerBaseWithConstantOffset(V, Offset, DL);
		/*if (Base == Ret && Offset < 0) {
			errs() << "Base: " << *Base << " Offset: " << Offset << "\n";
			errs() << "V: " << *V << "\n";
			errs() << *cast<Instruction>(V)->getParent()->getParent() << "\n";
		}
		assert((Base != Ret || Offset >= 0) && "negative Offset");*/
		if (Base != Ret) {
			Offset = INVALID_OFFSET;
		}
		if (ReplacementMap.count(Ret)) {
			Ret = ReplacementMap[Ret];
		}
	}
	else {
		Ret = GetUnderlyingObject1(V, DL, 0);
		assert(isa<PHINode>(Ret) || isa<SelectInst>(Ret));
		Offset = INVALID_OFFSET;
	}
	return Ret;
}

static Value* emitCall(Function &F, Instruction *I, Value *Ptr, Value *Name, int LineNum)
{
	FunctionCallee Fn;
	IRBuilder<> IRB(I);
	auto PtrTy = Ptr->getType();
	auto LineTy = IRB.getInt32Ty();
	auto M = F.getParent();
	auto NameTy = Name->getType();

	Fn = M->getOrInsertFunction("san_page_fault_limit", IRB.getInt8PtrTy(), PtrTy, LineTy, NameTy);
	auto *Line = ConstantInt::get(LineTy, LineNum);
	auto Call = IRB.CreateCall(Fn, {Ptr, Line, Name});

	if (F.getSubprogram()) {
    if (auto DL = I->getDebugLoc()) {
      Call->setDebugLoc(DL);
		}
  }
	return Call;
}

static Value* createCondLimit(Function &F, Instruction *I,
	Value *Ptr, int id, Value *Name, bool Conditional)
{
	Ptr = Ptr->stripPointerCasts();

	int LineNum = 0;
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	LineNum = (LineNum << 16) | id;
	if (!Conditional) {
		return emitCall(F, I, Ptr, Name, LineNum);
	}

	assert(0);
	auto Base = Ptr->stripPointerCasts();
	auto Entry = F.begin()->getFirstNonPHI();

	IRBuilder<> IRB(cast<Instruction>(Entry));
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Tmp = IRB.CreateAlloca(Int8PtrTy);

	if (isa<Argument>(Base) || isa<GlobalVariable>(Base)) {
	}
	else if (isa<PHINode>(Base)) {
		auto InstPt = cast<Instruction>(Base)->getParent()->getFirstNonPHI();
		IRB.SetInsertPoint(InstPt);
	}
	else {
		auto InstPt = cast<Instruction>(Base)->getNextNode();
		IRB.SetInsertPoint(InstPt);
	}

	IRB.CreateStore(Constant::getNullValue(Int8PtrTy), Tmp);

	IRB.SetInsertPoint(I);

	auto Limit = IRB.CreateLoad(Tmp);
	auto Cmp = IRB.CreateICmpEQ(Limit, Constant::getNullValue(Int8PtrTy));
	Instruction *Term = SplitBlockAndInsertIfThen(Cmp, I, false);
	auto Call = emitCall(F, Term, Ptr, Name, LineNum);
	IRB.SetInsertPoint(Term);
	IRB.CreateStore(Call, Tmp);

	IRB.SetInsertPoint(I);

  PHINode *PHI = IRB.CreatePHI(Int8PtrTy, 2);

  BasicBlock *CondBlock = cast<Instruction>(Cmp)->getParent();
  PHI->addIncoming(Limit, CondBlock);
  BasicBlock *ThenBlock = Term->getParent();
  PHI->addIncoming(Call, ThenBlock);

/*
	auto Call1 = emitCall(F, I, Ptr, Name, LineNum);
	auto Cmp1 = IRB.CreateICmpNE(Call1, PHI);
	Instruction *Term1 = SplitBlockAndInsertIfThen(Cmp1, I, false);
	emitCall(F, Term1, Constant::getNullValue(Int8PtrTy), Name, LineNum);
*/
  return PHI;
}

#if 0
static Value* addHandler(Function &F, Instruction *I, Value *Ptr, Value *Val, DenseSet<Value*> &GetLengths, 
	bool call, int id, Value *Name)
{
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);
	FunctionCallee Fn;
	int LineNum = 0;
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	LineNum = (LineNum << 16) | id;
	auto PtrTy = Ptr->getType();
	auto LineTy = IRB.getInt32Ty(); //Line->getType();
	auto M = F.getParent();
	//auto Name = IRB.CreateGlobalStringPtr(M->getName());
	auto NameTy = Name->getType();

	if (call) {
		assert(Val == NULL);
		Fn = M->getOrInsertFunction("san_page_fault_call", PtrTy, PtrTy, LineTy, NameTy);
	}
	else {
		if (GetLengths.count(I)) {
			assert(Val == NULL);
			Fn = M->getOrInsertFunction("san_page_fault_limit", IRB.getInt8PtrTy(), PtrTy, LineTy, NameTy);
		}
		else if (!Val) {
			if (1 /*I->getType()->isPointerTy()*/) {
				Fn = M->getOrInsertFunction("san_page_fault_load", PtrTy, PtrTy, LineTy, NameTy);
			}
			else {
				Fn = M->getOrInsertFunction("san_page_fault", PtrTy, PtrTy, LineTy, NameTy);
			}
		}
		else {
			Fn = M->getOrInsertFunction("san_page_fault_store", PtrTy, PtrTy, Val->getType(), LineTy, NameTy);
		}
	}

	CallInst *Call;
	auto *Line = ConstantInt::get(LineTy, LineNum);

	if (!Val) {
		Call = IRB.CreateCall(Fn, {Ptr, Line, Name});
	}
	else {
		Call = IRB.CreateCall(Fn, {Ptr, Val, Line, Name});
	}
	if (F.getSubprogram()) {
    if (auto DL = I->getDebugLoc()) {
      Call->setDebugLoc(DL);
		}
  }
	return Call;
}
#endif

static uint64_t getAllocaSizeInBytes1(const AllocaInst &AI)
{
	uint64_t ArraySize = 1;
  if (AI.isArrayAllocation()) {
    const ConstantInt *CI = dyn_cast<ConstantInt>(AI.getArraySize());
    assert(CI && "non-constant array size");
    ArraySize = CI->getZExtValue();
  }
  Type *Ty = AI.getAllocatedType();
  uint64_t SizeInBytes =
      AI.getModule()->getDataLayout().getTypeAllocSize(Ty);
  return SizeInBytes * ArraySize;
}
#if 0
#endif

#if 0
static void addAlloca(Function &F, AllocaInst *AI, int id, Value *Name) {
	uint64_t Size = (AI->isStaticAlloca()) ? getAllocaSizeInBytes1(*AI) : 0;
	IRBuilder<> IRB(AI->getNextNode());
	FunctionCallee Fn;
	int LineNum = 0;
	if (F.getSubprogram() && AI->getDebugLoc()) {
		LineNum = AI->getDebugLoc()->getLine();
	}
	LineNum = (LineNum << 16) | id;
	auto LineTy = IRB.getInt32Ty(); //Line->getType();
	auto SizeTy = IRB.getInt64Ty();
	auto M = F.getParent();
	//auto Name = IRB.CreateGlobalStringPtr(F.getName());
	auto NameTy = Name->getType();

	Fn = M->getOrInsertFunction("san_alloca", IRB.getVoidTy(), AI->getType(), SizeTy, LineTy, NameTy);
	auto *Line = ConstantInt::get(LineTy, LineNum);
	auto *Sz = ConstantInt::get(SizeTy, Size);
	IRB.CreateCall(Fn, {AI, Sz, Line, Name});
}


static void addCall(Function &F, CallBase *CI, int id, Value *Name) {
	int NumArgs = 0;
	Value *Args[2];
	for (auto ArgIt = CI->arg_begin(), End = CI->arg_end(); ArgIt != End && NumArgs < 2; ++ArgIt) {
		Value *A = *ArgIt;
    if (A->getType()->isPointerTy()) {
			Args[NumArgs++] = A;
		}
	}

	if (!NumArgs) {
		return;
	}
	IRBuilder<> IRB(CI);
	if (NumArgs == 1) {
		Args[1] = ConstantInt::get(IRB.getInt64Ty(), 0xabcdefabcdefULL);
	}

	FunctionCallee Fn;
	int LineNum = 0;
	if (F.getSubprogram() && CI->getDebugLoc()) {
		LineNum = CI->getDebugLoc()->getLine();
	}
	LineNum = (LineNum << 16) | id;
	auto LineTy = IRB.getInt32Ty(); //Line->getType();
	auto M = F.getParent();
	//auto Name = IRB.CreateGlobalStringPtr(F.getName());
	auto NameTy = Name->getType();

	Fn = M->getOrInsertFunction("san_call", IRB.getVoidTy(), Args[0]->getType(), Args[1]->getType(), LineTy, NameTy);
	auto *Line = ConstantInt::get(LineTy, LineNum);
	IRB.CreateCall(Fn, {Args[0], Args[1], Line, Name});
}


static void addMemcpy(Function &F, Instruction *I, Value *Ptr, Value *Size, Value *Name) {
	IRBuilder<> IRB(I);

	FunctionCallee Fn;
	int LineNum = 0;
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	auto PtrTy = Ptr->getType();
	auto LineTy = IRB.getInt32Ty(); //Line->getType();
	auto M = F.getParent();
	//auto Name = IRB.CreateGlobalStringPtr(F.getName());
	auto NameTy = Name->getType();

	Fn = M->getOrInsertFunction("san_memcpy", IRB.getVoidTy(), PtrTy, Size->getType(), LineTy, NameTy);
	auto *Line = ConstantInt::get(LineTy, LineNum);
	IRB.CreateCall(Fn, {Ptr, Size, Line, Name});
}

static void addArgument(Function &F, Value *Ptr, Value *Name) {
  Instruction *I = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);

	FunctionCallee Fn;
	int LineNum = 0;
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	auto PtrTy = Ptr->getType();
	auto LineTy = IRB.getInt32Ty(); //Line->getType();
	auto M = F.getParent();
	//auto Name = IRB.CreateGlobalStringPtr(F.getName());
	auto NameTy = Name->getType();

	Fn = M->getOrInsertFunction("san_page_fault_arg", IRB.getVoidTy(), PtrTy, LineTy, NameTy);
	auto *Line = ConstantInt::get(LineTy, LineNum);
	IRB.CreateCall(Fn, {Ptr, Line, Name});
}

static void addReturn(Function &F, Instruction *I, Value *Ptr, Value *Name) {
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);

	FunctionCallee Fn;
	int LineNum = 0;
	auto LineTy = IRB.getInt32Ty(); //Line->getType();
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	if (Ptr == NULL) {
		Ptr = ConstantInt::get(LineTy, 0);
	}
	auto PtrTy = Ptr->getType();
	auto M = F.getParent();
	//auto Name = IRB.CreateGlobalStringPtr(F.getName());
	auto NameTy = Name->getType();

	Fn = M->getOrInsertFunction("san_page_fault_ret", IRB.getVoidTy(), PtrTy, LineTy, NameTy);
	auto *Line = ConstantInt::get(LineTy, LineNum);
	IRB.CreateCall(Fn, {Ptr, Line, Name});
}
#endif

static Value* getNoInterior(Function &F, Instruction *I, Value *V)
{
	if (V->getType()->isPointerTy()) {
  	const DataLayout &DL = F.getParent()->getDataLayout();
		auto Ret = GetUnderlyingObject(V, DL);
		if (isa<AllocaInst>(Ret) || isa<GlobalVariable>(Ret)) {
			return V;
		}
	}
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);
	auto Intrin = (isa<PtrToIntInst>(V)) ? Intrinsic::ptrmask1 : Intrinsic::ptrmask;

	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrin, {V->getType(), V->getType(), IRB.getInt64Ty()});
	V = IRB.CreateCall(TheFn, {V, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<49)-1)});
	return V;
}

static Value* buildInvalid(Function &F, Value *Ptr, Instruction *I)
{
	IRBuilder<> IRB(I);
	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrinsic::ptrunmask, {Ptr->getType(), Ptr->getType(), IRB.getInt64Ty()});
	Ptr = IRB.CreateCall(TheFn, {Ptr, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<48))});
	return Ptr;
}


static Value* buildNoInterior(Function &F, IRBuilder<> &IRB, Value *Ptr)
{
	if (isa<AllocaInst>(Ptr) || isa<GlobalVariable>(Ptr)) {
		assert(0);
	}

	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrinsic::ptrmask, {Ptr->getType(), Ptr->getType(), IRB.getInt64Ty()});
	Ptr = IRB.CreateCall(TheFn, {Ptr, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<49)-1)});
	return Ptr;
}

static Value* getNoInteriorCall(Function &F, Instruction *I, Value *V)
{
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);
	auto Intrin = (isa<PtrToIntInst>(V)) ? Intrinsic::ptrmask1 : Intrinsic::ptrmask;

	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrin, {V->getType(), V->getType(), IRB.getInt64Ty()});
	V = IRB.CreateCall(TheFn, {V, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<48)-1)});
	return V;
}


static Value* getNoInteriorMap(Function &F, Instruction *Unused, Value *Oper, DenseMap<Value*, Value*> &RepMap)
{
	Value *Ret;
	if (RepMap.count(Oper)) {
		Ret = RepMap[Oper];
	}
	else {
		Instruction *I = dyn_cast<Instruction>(Oper);
		if (!I) {
			I = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
			assert(I);
		}
		else if (isa<PHINode>(I)) {
			I = I->getParent()->getFirstNonPHI();
		}
		else {
			I = I->getNextNode();
		}
		Ret = getNoInterior(F, I, Oper);
		RepMap[Oper] = Ret;
	}
	return Ret;
}

static void instrumentPageFaultHandler(Function &F, DenseSet<Value*> &GetLengths,
	DenseSet<Value*> &GetLengthsCond,
	DenseSet<StoreInst*> &Stores, DenseSet<CallBase*> &CallSites)
{
	int id = 0;
	Instruction *Entry = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
	assert(Entry);
	IRBuilder<> IRB(Entry);
	auto Name = IRB.CreateGlobalStringPtr(F.getName());
	DenseSet<AllocaInst*> AllocaInsts;
	DenseMap<Value*, Value*> RepMap;
	//DenseMap<Value*, Value*> LoadMap;
	DenseSet<LoadInst*> LoadSet;

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			Instruction *I = &Inst;
			Value *Ret;
			Value *Oper;
			if (GetLengths.count(I)) {
				LoadInst *LI = dyn_cast<LoadInst>(I);
				if (LI) {
					//Oper = LI->getPointerOperand();
					//Ret = getNoInteriorMap(F, LI, Oper, RepMap);
					assert(!LI->uses().empty());
					LoadSet.insert(LI);
					//Ret = addHandler(F, I, LI->getPointerOperand(), NULL, GetLengths, false, id++, Name);
					//LI->setOperand(0, Ret);
				}
				else {
					assert(isa<CallBase>(I));
				}
			}
			else if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
				Oper = LI->getPointerOperand();
				Ret = getNoInteriorMap(F, LI, Oper, RepMap);
				//Ret = addHandler(F, I, Oper, NULL, GetLengths, false, id++, Name);
				LI->setOperand(0, Ret);
			}
			else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {
				//Value *Val = (Stores.count(SI)) ? SI->getValueOperand() : NULL;
				//Value *Val = SI->getValueOperand();
				Oper = SI->getPointerOperand();
				Ret = getNoInteriorMap(F, SI, Oper, RepMap);
				//Ret = addHandler(F, I, Oper, Val, GetLengths, false, id++, Name);
				SI->setOperand(1, Ret);
			}
			else if (auto *AI = dyn_cast<AtomicRMWInst>(I)) {
				//Ret = addHandler(F, I, AI->getPointerOperand(), NULL, GetLengths, false, id++, Name);
				Oper = AI->getPointerOperand();
				Ret = getNoInteriorMap(F, AI, Oper, RepMap);
				AI->setOperand(0, Ret);
			}
			else if (auto *AI = dyn_cast<AtomicCmpXchgInst>(I)) {
				//Ret = addHandler(F, I, AI->getPointerOperand(), NULL, GetLengths, false, id++, Name);
				Oper = AI->getPointerOperand();
				Ret = getNoInteriorMap(F, AI, Oper, RepMap);
				AI->setOperand(0, Ret);
			}
			else if (auto *CI = dyn_cast<CallBase>(I)) {
				if (CI->isIndirectCall()) {
					//Ret = addHandler(F, I, CI->getCalledOperand(), NULL, GetLengths, true, id++, Name);
					Oper = CI->getCalledOperand();
					Ret = getNoInteriorCall(F, CI, Oper);
					CI->setCalledOperand(Ret);
				}
				else {
					auto MT = dyn_cast<MemTransferInst>(CI);
					if (MT) {
						//addMemcpy(F, MT, MT->getOperand(1), MT->getOperand(2), Name);
					}
					else if (CallSites.count(CI)) {
						//addCall(F, CI, id++, Name);
					}
				}
			}
			//else if (auto R = dyn_cast<ReturnInst>(I)) {
				//Value *RetVal = R->getReturnValue();
				//addReturn(F, R, RetVal, Name);
			//}
			else if (auto AI = dyn_cast<AllocaInst>(I)) {
				AllocaInsts.insert(AI);
			}
		}
	}

	for (auto LI : LoadSet) {
		auto Ret = createCondLimit(F, LI, LI->getPointerOperand(), id++, Name, GetLengthsCond.count(LI) > 0);
		LI->replaceAllUsesWith(Ret);
		LI->eraseFromParent();
	}

//#if 0
	int NumArgsAdded = 0;
  for (Argument &Arg : F.args()) {
		if (Arg.getType()->isPointerTy()) {
			//addArgument(F, &Arg, Name);
			NumArgsAdded++;
		}
	}
	if (!NumArgsAdded) {
		//addArgument(F, Constant::getNullValue(F.getType()), Name);
	}
//#endif
}


static void recordStackPointer(Function *F, Instruction *I, Value *StackBase, int &RecordIndex)
{
	IRBuilder<> IRB(I->getNextNode());
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int32Ty = IRB.getInt32Ty();
	auto Int8PtrPtrTy = Int8PtrTy->getPointerTo();

	auto BasePtr = IRB.CreateBitCast(StackBase, Int8PtrPtrTy);
	auto StorePtr = IRB.CreateGEP(Int8PtrTy, BasePtr, ConstantInt::get(Int32Ty, RecordIndex));
	RecordIndex++;
	IRB.CreateStore(IRB.CreateBitCast(I, Int8PtrTy), StorePtr);

#if 0
	auto M = F->getParent();
	auto RetTy = Type::getVoidTy(M->getContext());
	auto Fn = M->getOrInsertFunction("san_record_stack_pointer", RetTy, I->getType());
	CallInst::Create(Fn, {I}, "", I->getNextNode());
#endif
}

static Value* enterScope(Function *F, int NumSlots)
{
	auto M = F->getParent();
	auto RetTy = Type::getInt8PtrTy(M->getContext());
	auto Int32Ty = Type::getInt32Ty(M->getContext());
  Instruction *Entry = dyn_cast<Instruction>(F->begin()->getFirstInsertionPt());
	auto Fn = M->getOrInsertFunction("san_enter_scope", RetTy, Int32Ty);
	return CallInst::Create(Fn, {ConstantInt::get(Int32Ty, NumSlots)}, "", Entry);
}

static void exitScope(Function *F, Value *V)
{
	auto M = F->getParent();
	auto RetTy = Type::getVoidTy(M->getContext());
	auto Fn = M->getOrInsertFunction("san_exit_scope", RetTy, V->getType());
  for (auto &BB : *F) {
    for (auto &Inst : BB) {
			if (auto Ret = dyn_cast<ReturnInst>(&Inst)) {
				CallInst::Create(Fn, {V}, "", Ret);
			}
		}
	}
}

#define MAX_OFFSET ((1ULL<<15) - 1)
static Value* allocaToMalloc(Function *F, AllocaInst *AI, bool &DallocaReg)
{
	auto M = F->getParent();
	auto Int32Ty = Type::getInt32Ty(M->getContext());
	auto RetTy = Type::getVoidTy(M->getContext());
	size_t alignment = 0;
	Value *Size;
	alignment = AI->getAlignment();
	if (AI->isStaticAlloca()) {
		size_t Sz = getAllocaSizeInBytes1(*AI);
		if (Sz < MAX_OFFSET) {
			return NULL;
		}
		Size = ConstantInt::get(Int32Ty, Sz);
	}
	else {
  	Size = getAllocaSize(AI);
		IRBuilder<> IRB(AI);
		auto Int64Ty = IRB.getInt64Ty();
		auto MaxOffset = ConstantInt::get(Int64Ty, MAX_OFFSET);
		auto Cmp = IRB.CreateICmp(ICmpInst::ICMP_UGE, Size, MaxOffset);
		auto InsertPt = AI->getNextNode();
		Instruction *IfTerm;
		IfTerm = SplitBlockAndInsertIfThen(Cmp, InsertPt, false);
		auto Fn = M->getOrInsertFunction("san_dalloca", AI->getType(), Size->getType(), Int32Ty);
		IRB.SetInsertPoint(IfTerm);
		auto Call = IRB.CreateCall(Fn, {Size, ConstantInt::get(Int32Ty, alignment)});
		IRB.SetInsertPoint(InsertPt);
  	PHINode *PHI = IRB.CreatePHI(AI->getType(), 2);
		AI->replaceAllUsesWith(PHI);
  	PHI->addIncoming(AI, AI->getParent());
  	PHI->addIncoming(Call, Call->getParent());
		if (!DallocaReg) {
			DallocaReg = true;
  		Instruction *Entry = dyn_cast<Instruction>(F->begin()->getFirstInsertionPt());
			IRB.SetInsertPoint(Entry);
			Fn = M->getOrInsertFunction("san_dalloca_register", Int32Ty);
			auto Reg = IRB.CreateCall(Fn, {});

			Fn = M->getOrInsertFunction("san_dalloca_deregister", IRB.getVoidTy(), Int32Ty);
			for (auto &BB : *F) {
				auto Term = BB.getTerminator();
				if (isa<ReturnInst>(Term)) {
					IRB.SetInsertPoint(Term);
					IRB.CreateCall(Fn, {Reg});
				}
			}
		}

		return NULL;
	}

  Instruction *Entry = dyn_cast<Instruction>(F->begin()->getFirstInsertionPt());
	IRBuilder<> IRB(Entry);
	auto Fn = M->getOrInsertFunction("san_alloca", AI->getType(), Size->getType(), Int32Ty);
	auto Call = IRB.CreateCall(Fn, {Size, ConstantInt::get(Int32Ty, alignment)});
  AI->replaceAllUsesWith(Call);
	AI->eraseFromParent();

	Fn = M->getOrInsertFunction("san_alloca_free", RetTy, Call->getType());

	for (auto &BB : *F) {
		auto Term = BB.getTerminator();
		if (isa<ReturnInst>(Term)) {
			IRB.SetInsertPoint(Term);
			IRB.CreateCall(Fn, {Call});
		}
	}

	return Call;
}

void FastAddressSanitizer::patchStaticAlloca(Function &F, AllocaInst *AI, Value *StackBase, int &RecordIndex) {
	size_t Alignment = AI->getAlignment();
	uint64_t Size = getAllocaSizeInBytes(*AI);
	uint64_t HeaderVal = 0xfaceULL | (Size << 32);
	auto AllocaSize = ConstantInt::get(Int64Ty, HeaderVal);
  uint64_t Padding = alignTo(8, Alignment);

	assert(Padding >= 8);

	/*if (F.getName().startswith("register_attribute")) {
	 errs() << "Size: " << Size << "\n";
	 errs() << *AI << "\n";
	}*/

	Type *AllocatedType = AI->getAllocatedType();
  if (AI->isArrayAllocation()) {
    uint64_t ArraySize =
        cast<ConstantInt>(AI->getArraySize())->getZExtValue();
    AllocatedType = ArrayType::get(AllocatedType, ArraySize);
  }

  Type *TypeWithPadding = StructType::get(
      ArrayType::get(Int8Ty, Padding), AllocatedType);
  auto *NewAI = new AllocaInst(
      TypeWithPadding, AI->getType()->getAddressSpace(), nullptr, "", AI);
  NewAI->takeName(AI);
  NewAI->setAlignment(MaybeAlign(Alignment));
  NewAI->setUsedWithInAlloca(AI->isUsedWithInAlloca());
  NewAI->setSwiftError(AI->isSwiftError());
  NewAI->copyMetadata(*AI);
	IRBuilder<> Builder(AI);
  auto Field = Builder.CreateGEP(NewAI, {ConstantInt::get(Int32Ty, 0), ConstantInt::get(Int32Ty, 1)});
	auto SizeField = Builder.CreateGEP(Builder.CreateBitCast(Field, Int64PtrTy), ConstantInt::get(Int32Ty, -1));
	Builder.CreateStore(AllocaSize, SizeField);
  AI->replaceAllUsesWith(Field);
	AI->eraseFromParent();
	if (StackBase) {
		recordStackPointer(&F, cast<Instruction>(Field), StackBase, RecordIndex);
	}
}

void FastAddressSanitizer::patchDynamicAlloca(Function &F, AllocaInst *AI, Value *StackBase, int &RecordIndex) {

  uint64_t Padding = alignTo(8, AI->getAlignment());
  Value *OldSize = getAllocaSize(AI);
  IRBuilder<> IRB(AI);
  Value *NewSize = IRB.CreateAdd(OldSize, ConstantInt::get(Int64Ty, Padding));
	Value *Header = IRB.CreateOr(IRB.CreateShl(OldSize, 32), 0xfaceULL);

  AllocaInst *NewAI = IRB.CreateAlloca(IRB.getInt8Ty(), NewSize);
  NewAI->takeName(AI);
  NewAI->setAlignment(MaybeAlign(AI->getAlignment()));
  NewAI->setUsedWithInAlloca(AI->isUsedWithInAlloca());
  NewAI->setSwiftError(AI->isSwiftError());
  NewAI->copyMetadata(*AI);


  auto Field = IRB.CreateBitCast(IRB.CreateGEP(NewAI, {ConstantInt::get(Int32Ty, Padding)}), AI->getType());
	auto SizeField = IRB.CreateGEP(IRB.CreateBitCast(Field, Int64PtrTy), ConstantInt::get(Int32Ty, -1));
	IRB.CreateStore(Header, SizeField);
  AI->replaceAllUsesWith(Field);
	AI->eraseFromParent();
	if (StackBase) {
		recordStackPointer(&F, cast<Instruction>(Field), StackBase, RecordIndex);
	}
}

#if 0
static void setBoundsForArgv(Function &F, int Sanitizer)
{
	if (F.getName() == "main" && F.arg_size() > 0) {
		assert(F.arg_size() > 1 && F.arg_size() <= 3);
		auto argc = F.getArg(0);
		auto argv = F.getArg(1);
		auto IntTy = argc->getType();
		auto Fn = F.getParent()->getOrInsertFunction("san_copy_argv", argv->getType(), IntTy, argv->getType(), IntTy);
  	Instruction *Entry = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
		auto Call = CallInst::Create(Fn, {argc, argv, ConstantInt::get(IntTy, Sanitizer)}, "", Entry);
    argv->replaceAllUsesWith(Call);
		Call->setArgOperand(1, argv);
		if (F.arg_size() == 3) {
			auto env = F.getArg(2);
			auto Fn = F.getParent()->getOrInsertFunction("san_copy_env", env->getType(), env->getType());
			auto Call = CallInst::Create(Fn, {env}, "", Entry);
    	env->replaceAllUsesWith(Call);
			Call->setArgOperand(0, env);
		}
	}
}
#endif


static bool
handleLargerThanBase(Value *V, const DataLayout &DL, const TargetLibraryInfo *TLI, DenseSet<Value*> &LargerThanBase, uint64_t &PtrSize) {
	auto S = V->stripPointerCasts();
	if (S != V) {
		bool Static;
		auto ObjSize = getKnownObjSize(S, DL, Static, TLI);
		auto Ty = V->getType()->getPointerElementType();
		PtrSize = (Ty->isSized()) ? DL.getTypeAllocSize(Ty) : 0;
		if (ObjSize == 0) {
			ObjSize = 1;
		}
		if (ObjSize < (uint64_t)PtrSize) {
			errs() << "larger than base: " << *S << " VAL " << *V <<  " SZ1 " << ObjSize << " SZ2 " << PtrSize << "\n";
			LargerThanBase.insert(V);
			return true;
		}
	}
	return false;
}

void FastAddressSanitizer::recordAllUnsafeAccesses(Function &F, DenseSet<Value*> &UnsafeUses,
	DenseMap<Value*, uint64_t> &UnsafePointers, DenseSet<CallBase*> &CallSites,
	DenseSet<ReturnInst*> &RetSites, DenseSet<StoreInst*> &Stores,
	DenseSet<AllocaInst*> &UnsafeAllocas,
	DenseSet<Instruction*> &ICmpOrSub,
	DenseSet<Instruction*> &IntToPtr,
	DenseSet<Instruction*> &PtrToInt,
	DenseSet<Instruction*> &RestorePoints,
	DenseSet<Value*> &InteriorPointersSet,
	DenseSet<Instruction*> &GEPs,
	DenseSet<Value*> &LargerThanBase,
	DenseSet<CallInst*> &MemCalls,
	DenseSet<Instruction*> &FnPtrs,
	const TargetLibraryInfo *TLI)
{
  const DataLayout &DL = F.getParent()->getDataLayout();
  Value *Addr;
	bool IsWrite = false;
  unsigned Alignment = 0;
  uint64_t TypeSize = 0;
  Value *MaybeMask = nullptr;
	uint64_t PtrSz;

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			Addr = isInterestingMemoryAccess(&Inst, &IsWrite, &TypeSize, &Alignment, &MaybeMask);
			if (Addr) {
				addUnsafePointer(UnsafePointers, Addr, TypeSize/8);
				UnsafeUses.insert(&Inst);
				//errs() << "non-Call-Unsafe: " << *Addr << "\n";
			}
			else {
				if (auto CS = dyn_cast<CallBase>(&Inst)) {
        	if (!Inst.isLifetimeStartOrEnd() && !isa<DbgInfoIntrinsic>(Inst)) {
						auto II = dyn_cast<IntrinsicInst>(&Inst);
						if (!II || II->getIntrinsicID() != Intrinsic::ptrmask) {
							/*if (CS->isTailCall()) {
								errs() << F << "\n";
								errs() << *CS << "\n";
							}
							assert(!CS->isTailCall());*/
							auto CI = dyn_cast<CallInst>(CS);
							if (CI && CI->getCalledFunction() && CI->canReturnTwice()) {
								RestorePoints.insert(CI);
							}
          		for (auto ArgIt = CS->arg_begin(), End = CS->arg_end(), Start = CS->arg_begin(); ArgIt != End; ++ArgIt) {
								if (!(CS->doesNotCapture(ArgIt - Start) && (CS->doesNotAccessMemory(ArgIt - Start) ||
              	                                 CS->doesNotAccessMemory()))) {
            			Value *A = *ArgIt;
              		if (A->getType()->isPointerTy()) {
										CallSites.insert(CS);
										if (!IsNonInteriorObject(A, DL)) {
											auto ElemTy = A->getType()->getPointerElementType();
											if (ElemTy->isSized()) {
												InteriorPointersSet.insert(A);
											}
											else {
												A = A->stripPointerCasts();
												errs() << "NO-SIZED1: " << *A << "\n";
												if (!isa<Function>(A)) {
													assert(0);
												}
												FnPtrs.insert(CI);
											}
										}
										else {
											if (handleLargerThanBase(A, DL, TLI, LargerThanBase, PtrSz)) {
												// THIS LOGIC DOESN'T WORK BECAUSE BASE CAN'T BE DEREFRENCED
												//addUnsafePointer(UnsafePointers, A, PtrSz);
												//UnsafeUses.insert(CI);
											}
										}

              		}
								}
            	}
						}
          }
				}
				else if (auto Ret = dyn_cast<ReturnInst>(&Inst)) {
					Value *RetVal = Ret->getReturnValue();
          if (RetVal && RetVal->getType()->isPointerTy()) {
						if (!IsNonInteriorObject(RetVal, DL)) {
							auto ElemTy = RetVal->getType()->getPointerElementType();
							if (ElemTy->isSized()) {
								InteriorPointersSet.insert(RetVal);
								RetSites.insert(Ret);
							}
							else {
								RetVal = RetVal->stripPointerCasts();
								errs() << "NO-SIZED: " << *RetVal << "\n";
								if (!isa<Function>(RetVal)) {
									assert(0);
								}
								FnPtrs.insert(Ret);
							}
            }
						else {
							if (handleLargerThanBase(RetVal, DL, TLI, LargerThanBase, PtrSz)) {
								RetSites.insert(Ret);
								// THIS LOGIC DOESN'T WORK BECAUSE BASE CAN'T BE DEREFRENCED
								//addUnsafePointer(UnsafePointers, RetVal, PtrSz);
								//UnsafeUses.insert(Ret);
							}
						}
          }
				}
				else if (auto Ret = dyn_cast<IntToPtrInst>(&Inst)) {
					IntToPtr.insert(Ret);
				}
				else if (auto Ret = dyn_cast<PtrToIntInst>(&Inst)) {
					PtrToInt.insert(Ret);
				}
				else if (auto Ret = dyn_cast<ICmpInst>(&Inst)) {
					ICmpOrSub.insert(Ret);
				}
				else if (auto LP = dyn_cast<LandingPadInst>(&Inst)) {
					RestorePoints.insert(LP);
				}
				else if (auto GEP = dyn_cast<GetElementPtrInst>(&Inst)) {
					GEPs.insert(GEP);
				}
				/*else if (auto BO = dyn_cast<BinaryOperator>(&Inst)) {
					if (BO->getOpcode() == Instruction::Sub) {
						ICmpOrSub.insert(BO);
					}
				}*/
			}

			if (auto SI = dyn_cast<StoreInst>(&Inst)) {
				auto V = SI->getValueOperand();
				if (V->getType()->isPointerTy()) {
					if (!IsNonInteriorObject(V, DL)) {
						auto ElemTy = V->getType()->getPointerElementType();
						if (ElemTy->isSized()) {
          		InteriorPointersSet.insert(V);
							Stores.insert(SI);
						}
						else {
							V = V->stripPointerCasts();
							errs() << "NO-SIZED2: " << *V << "\n";
							if (!isa<Function>(V)) {
								assert(0);
							}
							FnPtrs.insert(SI);
						}
          }
					else {
						if (handleLargerThanBase(V, DL, TLI, LargerThanBase, PtrSz)) {
							Stores.insert(SI);
							// THIS LOGIC DOESN'T WORK BECAUSE BASE CAN'T BE DEREFRENCED
							//addUnsafePointer(UnsafePointers, V, PtrSz);
							//UnsafeUses.insert(SI);
						}
					}
				}
				else if (auto PI = dyn_cast<PtrToIntInst>(V)) {
					auto PO = PI->getOperand(0);
					if (!IsNonInteriorObject(PO, DL)) {

						auto ElemTy = PO->getType()->getPointerElementType();
						if (ElemTy->isSized()) {
          		InteriorPointersSet.insert(PO);
							Stores.insert(SI);
						}
						else {
							errs() << "NO-SIZED3: " << *PO << "\n";
						}

          }
				}
			}

			if (auto AI = dyn_cast<AllocaInst>(&Inst)) {
				if (!isSafeAlloca(AI, TLI)) {
					UnsafeAllocas.insert(AI);
				}
			}

			if (auto MI = dyn_cast<MemIntrinsic>(&Inst)) {
				//const DataLayout &DL = MI->getModule()->getDataLayout();
				auto ID = MI->getIntrinsicID();
				addUnsafePointer(UnsafePointers, MI->getArgOperand(0), 1);
				MemCalls.insert(MI);
				if (ID != Intrinsic::memset) {
					addUnsafePointer(UnsafePointers, MI->getArgOperand(1), 1);
				}
			}
			else if (auto CS = dyn_cast<CallInst>(&Inst)) {
				LibFunc Func;
				if (CS && TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
					if (Func == LibFunc_strlen || Func == LibFunc_sprintf || Func == LibFunc_vsprintf
							|| Func == LibFunc_snprintf || Func == LibFunc_vsnprintf) {
						addUnsafePointer(UnsafePointers, CS->getArgOperand(0), 1);
						MemCalls.insert(CS);
					}
				}
			}

		}
	}
}

static void
handleSelectBase(Function &F, const DataLayout &DL, SelectInst *Sel,
	DenseMap<Value*, Value*> &PhiAndSelectMap, DenseMap<Value*, Value*> &RepMap);

static void
handlePhiBase(Function &F, const DataLayout &DL, PHINode *Phi,
	DenseMap<Value*, Value*> &PhiAndSelectMap, DenseMap<Value*, Value*> &RepMap);

static Value*
getPhiOrSelectBase(Function &F, const DataLayout &DL, Value *Base,
	DenseMap<Value*, Value*> &PhiAndSelectMap, DenseMap<Value*, Value*> &RepMap)
{
	assert(isa<PHINode>(Base) || isa<SelectInst>(Base));
	if (!PhiAndSelectMap.count(Base)) {
		if (isa<PHINode>(Base)) {
			handlePhiBase(F, DL, dyn_cast<PHINode>(Base), PhiAndSelectMap, RepMap);
		}
		else if (isa<SelectInst>(Base)) {
			handleSelectBase(F, DL, dyn_cast<SelectInst>(Base), PhiAndSelectMap, RepMap);
		}
	}
	assert(PhiAndSelectMap.count(Base));
	return PhiAndSelectMap[Base];
}

static void
handleSelectBase(Function &F, const DataLayout &DL, SelectInst *Sel,
	DenseMap<Value*, Value*> &PhiAndSelectMap, DenseMap<Value*, Value*> &RepMap)
{
	Value *TrueOp = Sel->getTrueValue();
	Value *FalseOp = Sel->getFalseValue();
	IRBuilder<> IRB(Sel);
	SelectInst *SelBase =
		dyn_cast<SelectInst>(IRB.CreateSelect(Sel->getCondition(), TrueOp, FalseOp, Sel->getName() + ".sbase"));
	int64_t Offset;

	assert(!PhiAndSelectMap.count(Sel));
	PhiAndSelectMap[Sel] = SelBase;
	PhiAndSelectMap[SelBase] = SelBase;


	IRB.SetInsertPoint(SelBase);

	Value *Base = tryGettingBaseAndOffset(Sel->getTrueValue(), Offset, DL, RepMap);
	assert(Base);

	if (isa<PHINode>(Base) || isa<SelectInst>(Base)) {
		Base = getPhiOrSelectBase(F, DL, Base, PhiAndSelectMap, RepMap);
	}

	if (Base->getType() != TrueOp->getType()) {
		Base = IRB.CreateBitCast(Base, TrueOp->getType());
	}
	SelBase->setTrueValue(Base);

	Base = tryGettingBaseAndOffset(Sel->getFalseValue(), Offset, DL, RepMap);
	assert(Base);
	if (isa<PHINode>(Base) || isa<SelectInst>(Base)) {
		Base = getPhiOrSelectBase(F, DL, Base, PhiAndSelectMap, RepMap);
	}

	if (Base->getType() != FalseOp->getType()) {
		Base = IRB.CreateBitCast(Base, FalseOp->getType());
	}

	SelBase->setFalseValue(Base);
}

static Value* addTypeCastForPhiOp(Function &F, Value *Base, Value *Ptr, Type *DstTy)
{
	if (Base->getType() == DstTy) {
		return Base;
	}
	assert(isa<Argument>(Ptr) || isa<Instruction>(Ptr) || isa<Constant>(Ptr));
	BasicBlock *BB;
	auto Inst = dyn_cast<Instruction>(Ptr);
	if (Inst) {
		BB = Inst->getParent();
	}
	else {
		BB = &F.getEntryBlock();
	}
	assert(BB);

	IRBuilder<> IRB(BB->getTerminator());
	return IRB.CreateBitCast(Base, DstTy);
}

static void
handlePhiBase(Function &F, const DataLayout &DL, PHINode *Phi,
	DenseMap<Value*, Value*> &PhiAndSelectMap, DenseMap<Value*, Value*> &RepMap)
{
	IRBuilder<> IRB(Phi);
	PHINode *PhiBase = IRB.CreatePHI(Phi->getType(), Phi->getNumIncomingValues(), Phi->getName() + ".pbase");
	int64_t Offset;

	assert(!PhiAndSelectMap.count(Phi));
	PhiAndSelectMap[Phi] = PhiBase;
	PhiAndSelectMap[PhiBase] = PhiBase;

	for (unsigned i = 0; i < Phi->getNumIncomingValues(); i++) {

		auto PrevBB = Phi->getIncomingBlock(i);
		auto PrevVal = Phi->getIncomingValue(i);
		Value *Op = NULL;
		for (unsigned j = 0; j < i; j++) {
			if (PhiBase->getIncomingBlock(j) == PrevBB) {
				Op = PhiBase->getIncomingValue(j);
				break;
			}
			if (Phi->getIncomingValue(j) == PrevVal) {
				Op = PhiBase->getIncomingValue(j);
				break;
			}
		}

		if (Op == NULL) {
			auto PhiOp = Phi->getIncomingValue(i);
			Value *Base = tryGettingBaseAndOffset(PhiOp, Offset, DL, RepMap);
			assert(Base);
			if (isa<PHINode>(Base) || isa<SelectInst>(Base)) {
				Base = getPhiOrSelectBase(F, DL, Base, PhiAndSelectMap, RepMap);
			}
			Op = addTypeCastForPhiOp(F, Base, PhiOp, PhiOp->getType());
		}

		PhiBase->addIncoming(Op, PrevBB);
	}
}

static void
findPhiAndSelectBases(Function &F, DenseSet<Value*> &PhiAndSelectNodes,
	DenseMap<Value*, Value*> &PhiAndSelectMap, DenseMap<Value*, Value*> &RepMap)
{
  const DataLayout &DL = F.getParent()->getDataLayout();

	for (Value *Node : PhiAndSelectNodes) {
		if (!PhiAndSelectMap.count(Node)) {
			if (auto Phi = dyn_cast<PHINode>(Node)) {
				handlePhiBase(F, DL, Phi, PhiAndSelectMap, RepMap);
			}
			else if (auto Sel = dyn_cast<SelectInst>(Node)) {
				handleSelectBase(F, DL, Sel, PhiAndSelectMap, RepMap);
			}
			else {
				assert(0);
			}
			assert(PhiAndSelectMap.count(Node));
		}
	}
}

static void findAllBaseAndOffsets(Function &F, DenseMap<Value*, uint64_t> &UnsafePointers,
	std::map<Value*, std::pair<const Value*, int64_t>> &UnsafeMap,
	DenseMap<Value*, Value*> &PtrToBaseMap,
	DenseSet<Value*> &TmpSet,
	DominatorTree &DT, DenseMap<Value*, Value*> &ReplacementMap, const TargetLibraryInfo *TLI,
	DenseSet<Value*> &InteriorPointersSet,
	DenseSet<Value*> &LargerThanBase)
{
  const DataLayout &DL = F.getParent()->getDataLayout();

	for (auto It : UnsafePointers) {
		Value *V = It.first;
		uint64_t TypeSize = It.second;
		int64_t Offset;

		if (isa<ConstantExpr>(V)) {
			continue;
		}
		if (isa<Constant>(V) && cast<Constant>(V)->isNullValue()) {
			continue;
		}

		Value *Base = tryGettingBaseAndOffset(V, Offset, DL, ReplacementMap);
		/*if (Base == NULL) {
			continue;
		}*/
		assert(Base);

		PtrToBaseMap[V] = Base;


		if (Offset >= 0) {
			bool Static = false;
			uint64_t BaseSize = getKnownObjSize(Base, DL, Static, TLI);
			Offset += TypeSize;
			if (Offset > (int64_t)BaseSize) {
				if (Static) {
					errs() << "Out of bound array access\n";
					errs() << F << "\n";
					errs() << "Base: " << *Base << "\n";
					errs() << "Val: " << *V << "\n";
					exit(0);
				}
				UnsafeMap[V] = std::make_pair(Base, Offset);
				TmpSet.insert(V);
			}
		}
		else {
			Value *Base1 = GetPointerBaseWithConstantOffset(V, Offset, DL);
			UnsafeMap[V] = std::make_pair(Base1, Offset);
			TmpSet.insert(V);
		}
	}

	for (auto V : InteriorPointersSet) {
		if (!PtrToBaseMap.count(V)) {
			int64_t Offset;
			Value *Base = tryGettingBaseAndOffset(V, Offset, DL, ReplacementMap);
			assert(Base);
			PtrToBaseMap[V] = Base;
		}
	}

	for (auto V : LargerThanBase) {
		if (!PtrToBaseMap.count(V)) {
			int64_t Offset;
			Value *Base = tryGettingBaseAndOffset(V, Offset, DL, ReplacementMap);
			assert(Base);
			PtrToBaseMap[V] = Base;
		}
	}
}

static void CheckLenInSameBasicBlock(Instruction *len1, Instruction *len2)
{
	if (len1->getParent() == len2->getParent()) {
		if (isa<CallInst>(len1) && isa<LoadInst>(len2)) {
			errs() << "Replacing: len with call : " << *len2 << " :: "  << *len1 << "\n";
			errs() << "BASIC BLOCk" << *(len1->getParent()) << "\n";
			errs() << "FUNC:" << *(len1->getParent()->getParent()) << "\n";
			assert(0);
		}

		if (isa<CallInst>(len1) && isa<CallInst>(len2)) {
			errs() << "Replacing: call with call : " << *len2 << " :: "  << *len1 << "\n";
		}
	}
}

static void removeRedundentLengths(Function &F, DenseSet<Value*> &GetLengths,
	DenseMap<Value*, Value*> &LenToBaseMap
	)
{
	DominatorTree DT(F);
	DenseSet<Instruction*> ToDelete;
	for (auto itr1 = GetLengths.begin(); itr1 != GetLengths.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != GetLengths.end(); itr2++) {
			Instruction *len1 = cast<Instruction>(*itr1);
			Instruction *len2 = cast<Instruction>(*itr2);
			if (ToDelete.count(len1) || ToDelete.count(len2)) {
				continue;
			}
			if (!LenToBaseMap.count(len1) || !LenToBaseMap.count(len2)) {
				continue;
			}
			if (LenToBaseMap[len1] != LenToBaseMap[len2]) {
				continue;
			}
			if (DT.dominates(len1, len2)) {
				CheckLenInSameBasicBlock(len1, len2);
    		len2->replaceAllUsesWith(len1);
				ToDelete.insert(len2);
			}
			else if (DT.dominates(len2, len1)) {
				CheckLenInSameBasicBlock(len2, len1);
    		len1->replaceAllUsesWith(len2);
				ToDelete.insert(len1);
			}
		}
	}
	for (auto len : ToDelete) {
		assert(GetLengths.count(len));
		GetLengths.erase(len);
		len->eraseFromParent();
	}
}

static void removeRedundentAccesses(Function &F,
	std::map<Value*, std::pair<const Value*, int64_t>> &UnsafeMap, DenseSet<Value*> &TmpSet,
	DominatorTree &DT, AAResults *AA)
{
	// FIXME: Offset Calulation Needs to be done with respect to closest base
	// If the closest base with constant offset is common, we can remove some checks
	//const Value* NullVal = NULL;
	DenseSet<Value*> ToDelete;

	for (auto itr1 = TmpSet.begin(); itr1 != TmpSet.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != TmpSet.end(); itr2++) {

			auto *Ptr1 = dyn_cast<Instruction>(*itr1);
      auto *Ptr2 = dyn_cast<Instruction>(*itr2);

			if (ToDelete.count(Ptr1) || ToDelete.count(Ptr2)) {
				continue;
			}

			if (Ptr1 == NULL) {
				Value *V = *itr1;
				errs() << "PTR1: " << *V << "\n";
				errs() << F << "\n";
			}
			if (Ptr2 == NULL) {
				Value *V = *itr2;
				errs() << "PTR2: " << *V << "\n";
				errs() << F << "\n";
			}
			assert(Ptr1 && "Ptr1 is not an instruction");
			assert(Ptr2 && "Ptr2 is not an instruction");

			auto AR = AA->alias(MemoryLocation(Ptr1), MemoryLocation(Ptr2));

			if (AR == MustAlias) {
				if (DT.dominates(Ptr1, Ptr2)) {
					//UnsafeMap[Ptr2] = std::make_pair(NullVal, 0);
					ToDelete.insert(Ptr2);
				}
				else if (DT.dominates(Ptr2, Ptr1)) {
					//UnsafeMap[Ptr1] = std::make_pair(NullVal, 0);
					ToDelete.insert(Ptr1);
				}
			}
			else {
				auto *Ptr1Base = UnsafeMap[Ptr1].first;
				auto *Ptr2Base = UnsafeMap[Ptr2].first;
				if (Ptr1Base == Ptr2Base) {
					auto Ptr1Off = UnsafeMap[Ptr1].second;
					auto Ptr2Off = UnsafeMap[Ptr2].second;

					//if (Ptr1Off > 0 && Ptr2Off > 0) {
						auto Ptr1DominatesPtr2 = DT.dominates(Ptr1, Ptr2);
						auto Ptr2DominatesPtr1 = DT.dominates(Ptr2, Ptr1);
						if (Ptr1DominatesPtr2 || Ptr2DominatesPtr1) {
							if (Ptr1Off >= Ptr2Off && Ptr1DominatesPtr2) {
								//UnsafeMap[Ptr2] = std::make_pair(NullVal, 0);
								ToDelete.insert(Ptr2);
							}
							else if (Ptr2Off >= Ptr1Off && Ptr2DominatesPtr1) {
								//UnsafeMap[Ptr1] = std::make_pair(NullVal, 0);
								ToDelete.insert(Ptr1);
							}
						}
					//}

				}
			}
		}
	}
	for (auto V : ToDelete) {
		assert(TmpSet.count(V));
		TmpSet.erase(V);
	}
}

static Value *
checkSizeWithLimit(Function &F, Value *Base, Value *Limit,
	IRBuilder<> &IRB, size_t TypeSize, Type *RetTy, Value *V, bool CheckOffset)
{
	auto Int64 = IRB.getInt64Ty();
	auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();
	//auto LI = dyn_cast<Instruction>(Limit);
	//if (LI && LI->getType()->isPointerTy() && LI->getParent() == I->getParent()) {
		//IRB.SetInsertPoint(LI->getNextNode());
	//}
	if (CheckOffset) {
		auto Fn = F.getParent()->getOrInsertFunction("san_interior_limit", Int8PtrTy, Base->getType(), V->getType(), Int64, Limit->getType());
		auto Ret = IRB.CreateCall(Fn, {Base, V, ConstantInt::get(Int64, TypeSize), Limit});
		return IRB.CreateBitCast(Ret, RetTy);
	}

	if (Limit->getType()->isIntegerTy()) {
		auto Base8 = IRB.CreateBitCast(Base, Int8PtrTy);
		Limit = IRB.CreateGEP(Int8Ty, Base8, Limit);
	}
	assert(Limit->getType() == Int8PtrTy);

	auto Fn = F.getParent()->getOrInsertFunction("san_check_size_limit", Int8PtrTy, Base->getType(), Int64, Int8PtrTy);
	auto Ret = IRB.CreateCall(Fn, {Base, ConstantInt::get(Int64, TypeSize), Limit});
	return IRB.CreateBitCast(Ret, RetTy);
}


static void createCondCall(Function &F, Instruction *_Call,
	Value *Base, DominatorTree *DT, LoopInfo *LI)
{
	auto Call = cast<CallInst>(_Call);
	auto Entry = F.begin()->getFirstNonPHI();
	IRBuilder<> IRB(cast<Instruction>(Entry));
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Tmp = IRB.CreateAlloca(Int8PtrTy);

	if (isa<Argument>(Base) || isa<GlobalVariable>(Base)) {
	}
	else if (isa<PHINode>(Base)) {
		auto InstPt = cast<Instruction>(Base)->getParent()->getFirstNonPHI();
		IRB.SetInsertPoint(InstPt);
	}
	else {
		if (isa<Constant>(Base)) {
			return;
		}
		auto InstPt = cast<Instruction>(Base)->getNextNode();
		IRB.SetInsertPoint(InstPt);
	}

	IRB.CreateStore(Constant::getNullValue(Int8PtrTy), Tmp);

	IRB.SetInsertPoint(Call);

	auto Limit = IRB.CreateLoad(Tmp);
	auto Cmp = IRB.CreateICmpEQ(Limit, Constant::getNullValue(Int8PtrTy));
	Instruction *Term = SplitBlockAndInsertIfThen(Cmp, Call, false, NULL, DT, LI);
	auto IfEnd = Call->getNextNode();


  Call->removeFromParent();
	Call->insertBefore(Term);


	IRB.SetInsertPoint(IfEnd);

  PHINode *PHI = IRB.CreatePHI(Int8PtrTy, 2);

  BasicBlock *CondBlock = cast<Instruction>(Cmp)->getParent();
  PHI->addIncoming(Limit, CondBlock);
  BasicBlock *ThenBlock = Term->getParent();
	Call->replaceAllUsesWith(PHI);
  PHI->addIncoming(Call, ThenBlock);
	IRB.SetInsertPoint(Term);
	IRB.CreateStore(Call, Tmp);
}

static void callOnceInLoopAfterDef(Function &F, Instruction *Call,
	Instruction *Def, DominatorTree *DT, LoopInfo *LI)
{
	auto Entry = F.begin()->getFirstNonPHI();
	IRBuilder<> IRB(cast<Instruction>(Entry));

	auto Int8Ty = IRB.getInt8Ty();
	auto Tmp = IRB.CreateAlloca(Int8Ty);

	if (isa<PHINode>(Def)) {
		Def = Def->getParent()->getFirstNonPHI();
	}

	IRB.SetInsertPoint(Def);
	IRB.CreateStore(Constant::getNullValue(Int8Ty), Tmp);


	IRB.SetInsertPoint(Call);
	auto First = IRB.CreateLoad(Tmp);
	auto Cmp = IRB.CreateICmpEQ(First, Constant::getNullValue(Int8Ty));
	Instruction *IfTerm = SplitBlockAndInsertIfThen(Cmp, Call, false, NULL, DT, LI);
  Call->removeFromParent();
	Call->insertBefore(IfTerm);
	IRB.SetInsertPoint(IfTerm);
	IRB.CreateStore(ConstantInt::get(Int8Ty, 1), Tmp);
}

static Value* createCondSafeLimit(Function &F, Instruction *InsertPt, Value *Base, bool NeedRecurrance, bool MustCheck)
{
	IRBuilder<> IRB(InsertPt);
	Value *Limit;
	if (NeedRecurrance) {
		assert(0);
	}
	else {
		FunctionCallee Fn;
		if (MustCheck) {
			Fn = F.getParent()->getOrInsertFunction("san_get_limit_must_check", IRB.getInt8PtrTy(), Base->getType());
		}
		else {
			Fn = F.getParent()->getOrInsertFunction("san_get_limit_check", IRB.getInt8PtrTy(), Base->getType());
		}
		Limit = IRB.CreateCall(Fn, {Base});
		/*if (MustCheck) {
			errs() << "Adding in Cond Safe:: " << *Limit << "\n";
			errs() << *(InsertPt->getParent()) << "\n";
		}*/
	}
	return Limit;
}



static Value*
getInteriorValue(Function &F, Instruction *I, Value *V,
	DenseSet<Value*> &InteriorPointersSet,
	DenseSet<Value*> &SafePtrs, DenseMap<Value*, Value*> &PtrToBaseMap,
	Value *Limit, int ID,
	DenseMap<Value*, Value*> &ILoopUsages,
  DenseSet<Value*> &ICondLoop,
	DenseSet<Value*> &IGetLengths,
	DenseMap<Value*, Value*> &ILenToBaseMap
	)
{
	Value *Ret = NULL;
	auto M = F.getParent();
	Type *RetTy = V->getType();

	//errs() << "GetInterior: I :: " << *I << "\n";
	//errs() << "GetInterior: V :: " << *V << "\n";


	if (InteriorPointersSet.count(V)) {
		assert(PtrToBaseMap.count(V));
		Instruction *LoopHeader = NULL;
		if (ILoopUsages.count(V)) {
			assert(0);
			errs() << "USED_IN_LOOP: " << *V << "\n";
			LoopHeader = cast<BasicBlock>(ILoopUsages[V])->getFirstNonPHI();
		}

		auto Base = PtrToBaseMap[V];
		const DataLayout &DL = M->getDataLayout();
		bool Indefinite = indefiniteBase(Base, DL);
		auto PTy = V->getType()->getPointerElementType();
		size_t TypeSize = DL.getTypeStoreSize(PTy);


		if (/*Indefinite*/false) {
			IRBuilder<> IRB(I);
			auto Fn = M->getOrInsertFunction("san_interior_must_check", RetTy, Base->getType(), V->getType(), IRB.getInt64Ty(), IRB.getInt64Ty());
			Ret = IRB.CreateCall(Fn, {Base, V, ConstantInt::get(IRB.getInt64Ty(), TypeSize), ConstantInt::get(IRB.getInt64Ty(), ID)});
		}
		else {
			if (SafePtrs.count(V)) {
				IRBuilder<> IRB(I);
				auto Fn = M->getOrInsertFunction("san_interior", IRB.getInt8PtrTy(), Base->getType(),
					V->getType(), IRB.getInt64Ty(), IRB.getInt64Ty(), IRB.getInt8PtrTy());
				Ret = IRB.CreateCall(Fn,
					{Base, V, ConstantInt::get(IRB.getInt64Ty(), TypeSize),
					ConstantInt::get(IRB.getInt64Ty(), ID), Constant::getNullValue(IRB.getInt8PtrTy())});
				Ret = IRB.CreateBitCast(Ret, RetTy);
			}
			else {
				if (!Limit) {
					auto InsertPt = (LoopHeader) ? LoopHeader : I;
#if 0
					if (ICondLoop.count(V)) {
						assert(0);
						if (!isa<Instruction>(Base)) {
							InsertPt = cast<Instruction>(F.begin()->getFirstInsertionPt());
						}
						else {
							if (isa<PHINode>(Base)) {
								InsertPt = cast<PHINode>(Base)->getParent()->getFirstNonPHI();
							}
							else {
								InsertPt = cast<Instruction>(Base)->getNextNode();
							}
						}
					}
#endif
					Limit = createCondSafeLimit(F, InsertPt, Base, false, Indefinite);
					IGetLengths.insert(Limit);
					ILenToBaseMap[Limit] = Base;
					if (ICondLoop.count(V)) {
						ICondLoop.insert(Limit);
					}


					IRBuilder<> IRB(I);
					Ret = checkSizeWithLimit(F, Base, Limit, IRB, TypeSize, RetTy, V, true);
				}
				else {
					IRBuilder<> IRB(I);
					Ret = checkSizeWithLimit(F, Base, Limit, IRB, TypeSize, RetTy, V, true);
					//errs() << "Adding Interior:: " << *Ret << "\n";
					//errs() << "Before:: " << *I << "\n";
					return Ret;
				}
			}
		}
	}
	else if (isa<Constant>(V) && !isa<GlobalVariable>(V)) {
		IRBuilder<> IRB(I);
  	const DataLayout &DL = F.getParent()->getDataLayout();
		if (isa<ConstantExpr>(V)) {
			int64_t Offset = 0;
			Value *Base = GetPointerBaseWithConstantOffset(V, Offset, DL);
			if (isa<GlobalVariable>(Base) && Offset == 0) {
				return Ret;
			}
		}
		auto Fn = Intrinsic::getDeclaration(M, Intrinsic::ptrunmask, {V->getType(), V->getType(), IRB.getInt64Ty()});
		Ret = IRB.CreateCall(Fn, {V, ConstantInt::get(IRB.getInt64Ty(), (0x1ULL<<48))});
	}
	return Ret;
}

static Value*
SanCheckSize(Function &F, Instruction *I, Value *V, Value *Limit,
	DenseMap<Value*, Value*> &ILoopUsages,
  DenseSet<Value*> &ICondLoop,
	DenseSet<Value*> &IGetLengths,
	DenseMap<Value*, Value*> &ILenToBaseMap
)
{
	auto M = F.getParent();
	const DataLayout &DL = M->getDataLayout();
	auto PTy = V->getType()->getPointerElementType();
	size_t TypeSize = DL.getTypeStoreSize(PTy);
	auto Base = V->stripPointerCasts();

	Instruction *LoopHeader = NULL;
	if (ILoopUsages.count(V)) {
		errs() << "USED_IN_LOOP: " << *V << "\n";
		LoopHeader = cast<BasicBlock>(ILoopUsages[V])->getFirstNonPHI();
	}

	if (!Limit) {
		auto InsertPt = (LoopHeader) ? LoopHeader : I;

#if 0
		if (ICondLoop.count(V)) {
			assert(0);
			if (!isa<Instruction>(Base)) {
				InsertPt = cast<Instruction>(F.begin()->getFirstInsertionPt());
			}
			else {
				if (isa<PHINode>(Base)) {
					InsertPt = cast<PHINode>(Base)->getParent()->getFirstNonPHI();
				}
				else {
					InsertPt = cast<Instruction>(Base)->getNextNode();
				}
			}
		}
#endif

		Limit = createCondSafeLimit(F, InsertPt, Base, false, false);
		IGetLengths.insert(Limit);
		ILenToBaseMap[Limit] = Base;
		if (ICondLoop.count(V)) {
			ICondLoop.insert(Limit);
		}
	}
	IRBuilder<> IRB(I);
	return checkSizeWithLimit(F, Base, Limit, IRB, TypeSize, V->getType(), V, false);
}

static void collectUnsafeUses(Function &F,
	DenseSet<CallBase*> &CallSites, DenseSet<ReturnInst*> &RetSites, DenseSet<StoreInst*> &Stores,
	DenseSet<Value*> &InteriorPointersSet,
  DenseMap<Value*, DenseSet<Instruction*>> &InteriorsUseMap,
	const TargetLibraryInfo *TLI)
{
	if (InteriorPointersSet.empty()) {
		return;
	}
	for (auto SI : Stores) {
		auto V = SI->getValueOperand();
		if (isa<PtrToIntInst>(V)) {
			V = cast<Instruction>(V)->getOperand(0);
		}

		if (InteriorPointersSet.count(V)) {
			InteriorsUseMap[V].insert(SI);
		}
	}

	for (auto RI : RetSites) {
		auto V = RI->getReturnValue();
		assert(V && "return value null!");
		if (InteriorPointersSet.count(V)) {
			InteriorsUseMap[V].insert(RI);
		}
	}

	for (auto CS : CallSites) {
		LibFunc Func;
		bool LibCall = false;
		if (isa<IntrinsicInst>(CS)) {
			LibCall = true;
		}
    if (TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
			if (!TLI->isInteriorSafe(Func)) {
				LibCall = true;
			}
		}
		DenseMap<Value*, Value*> InteriorToBase;
    AttributeList PAL = CS->getAttributes();
    for (auto ArgIt = CS->arg_begin(), End = CS->arg_end(), Start = CS->arg_begin(); ArgIt != End; ++ArgIt) {
			if (!(CS->doesNotCapture(ArgIt - Start) && (CS->doesNotAccessMemory(ArgIt - Start) ||
                                       CS->doesNotAccessMemory()))) {
    		Value *A = *ArgIt;
      	if (A->getType()->isPointerTy()) {
					if (!(LibCall || PAL.hasParamAttribute(ArgIt - Start, Attribute::ByVal))) {
						if (InteriorPointersSet.count(A)) {
							InteriorsUseMap[A].insert(CS);
						}
					}
      	}
			}
		}
	}
}

static void collectSafeEscapes(Function &F,
	DenseSet<CallBase*> &CallSites, DenseSet<ReturnInst*> &RetSites, DenseSet<StoreInst*> &Stores,
	DenseSet<Value*> &InteriorPointersSet,
  const TargetLibraryInfo *TLI, DenseSet<Value*> &SafeInteriors,
	PostDominatorTree &PDT, LoopInfo &LI)
{
	DenseMap<Value*, DenseSet<Instruction*>> InteriorsUseMap;
	DenseMap<Value*, Value*> InteriorValues;

	collectUnsafeUses(F, CallSites, RetSites, Stores, InteriorPointersSet, InteriorsUseMap, TLI);

	if (!InteriorsUseMap.empty()) {
		for (auto It : InteriorsUseMap) {
			auto V = It.first;
			auto Uses = It.second;
			if (isa<Instruction>(V)) {
				if (postDominatesAnyStore(F, V, PDT, Uses, LI)) {
					SafeInteriors.insert(V);
				}
			}
		}
	}
}

static Value*
insertBoundsCheck(Function &F, CallBase *I, bool Intrin) {
	return NULL;
	int NumPointerArgs = 0;
	bool is_strlen = false;
	bool is_strcpy = false;

	if (Intrin) {
		if (auto MI = dyn_cast<MemIntrinsic>(I)) {
			if (MI->getIntrinsicID() == Intrinsic::memset) {
				NumPointerArgs = 1;
			}
			else {
				NumPointerArgs = 2;
			}
		}
	}
	else {
		auto Name = I->getCalledFunction()->getName();
		if (Name == "memcmp") {
			NumPointerArgs = 2;
		}
		else if (Name == "strlen") {
			is_strlen = true;
		}
		else if (Name == "strcpy") {
			is_strcpy = true;
		}
	}
	if (NumPointerArgs == 2) {
		IRBuilder<> IRB(I);
		auto Ptr1 = I->getOperand(0);
		auto Ptr2 = I->getOperand(1);
		auto Len = I->getOperand(2);

		//Function *TheFn =
      //Intrinsic::getDeclaration(F.getParent(), Intrinsic::san_check2, {Ptr1->getType(), Ptr2->getType(), Len->getType()});
		auto TheFn = F.getParent()->getOrInsertFunction("san_check2", IRB.getVoidTy(),
			Ptr1->getType(), Ptr2->getType(), Len->getType());
		return IRB.CreateCall(TheFn, {Ptr1, Ptr2, Len});
	}
	else if (NumPointerArgs == 1) {
		IRBuilder<> IRB(I);
		auto Ptr1 = I->getOperand(0);
		auto Len = I->getOperand(2);

		//Function *TheFn =
      //Intrinsic::getDeclaration(F.getParent(), Intrinsic::san_check1, {Ptr1->getType(), Len->getType()});
		auto TheFn = F.getParent()->getOrInsertFunction("san_check1", IRB.getVoidTy(),
			Ptr1->getType(), Len->getType());
		return IRB.CreateCall(TheFn, {Ptr1, Len});
	}
	else {
		if (is_strcpy) {
			IRBuilder<> IRB(I);
			auto Ptr1 = I->getOperand(0);
			auto Ptr2 = I->getOperand(1);

			//Function *TheFn =
      	//Intrinsic::getDeclaration(F.getParent(), Intrinsic::san_check3, {Ptr1->getType(), Ptr2->getType()});
			auto TheFn = F.getParent()->getOrInsertFunction("san_check3", IRB.getVoidTy(),
				Ptr1->getType(), Ptr2->getType());
			return IRB.CreateCall(TheFn, {Ptr1, Ptr2});
		}
		else if (is_strlen) {
			IRBuilder<> IRB(I->getNextNode());
			auto Ptr1 = I->getOperand(0);
			auto Len = I;

			//Function *TheFn =
      	//Intrinsic::getDeclaration(F.getParent(), Intrinsic::san_check1, {Ptr1->getType(), Len->getType()});
			auto TheFn = F.getParent()->getOrInsertFunction("san_check4", IRB.getVoidTy(),
				Ptr1->getType(), Len->getType());
			return IRB.CreateCall(TheFn, {Ptr1, Len});
		}
	}
	return NULL;
}


static bool checkWithinRange(Function &F,
	Value *Base,
	Value *Ptr,
	Value *Limit)
{
	if (!isa<ConstantInt>(Limit)) {
		return false;
	}
	const DataLayout &DL = F.getParent()->getDataLayout();
	int64_t Offset = cast<ConstantInt>(Limit)->getZExtValue();
	int64_t CurOffset = 0;
	auto PTy = Ptr->getType()->getPointerElementType();
	int64_t Off = DL.getTypeStoreSize(PTy);

  Value *B = GetPointerBaseWithConstantOffset(Ptr, CurOffset, DL);
	if (B != Base) {
		return false;
	}
	return CurOffset + Off <= Offset;
}

static Value* getLimitIfAvailable(Function &F,
	DominatorTree &DT,
	Value *Ptr,
	Instruction *I,
	Value *Base,
	DenseMap<Value*, Value*> &BaseToLenMap,
	DenseMap<Value*, DenseSet<Value*>> &BaseToLenSetMap,
	bool &WithinRange,
	bool CheckSet)
{
	WithinRange = false;
	Value *Ret = NULL;
	if (BaseToLenMap.count(Base)) {
		Ret = BaseToLenMap[Base];
	}
	else if (CheckSet && BaseToLenSetMap.count(Base)) {
		auto LenSet = BaseToLenSetMap[Base];
		for (auto Len : LenSet) {
			I = I->getParent()->getTerminator();
			if (DT.dominates(cast<Instruction>(Len), I)) {
				Ret = Len;
				break;
			}
		}
	}
	if (Ret) {
		if (checkWithinRange(F, Base, Ptr, Ret)) {
			WithinRange = true;
		}
	}
	return Ret;
}

static bool
isAliasWithSafePtr(Function &F, DominatorTree &DT, DenseSet<Value*> &SafePtrs, Instruction *Ptr)
{
	Value *PtrS = Ptr->stripPointerCasts();
  const DataLayout &DL = F.getParent()->getDataLayout();

	for (auto _SafePtr : SafePtrs) {
		if (!isa<Instruction>(_SafePtr)) {
			continue;
		}
		auto SafePtr = cast<Instruction>(_SafePtr);
		auto SafePtrS = SafePtr->stripPointerCasts();
		if (PtrS == SafePtrS) {
			if (DT.dominates(SafePtr, Ptr) || SafePtr->getParent() == Ptr->getParent()) {
				auto SafePtrTy = SafePtr->getType()->getPointerElementType();
				size_t SafePtrSize = DL.getTypeStoreSize(SafePtrTy);

				auto PtrTy = Ptr->getType()->getPointerElementType();
				size_t PtrSize = DL.getTypeStoreSize(PtrTy);
				if (SafePtrSize >= PtrSize) {
					errs() << "FOUND REPLACE: " << *Ptr << "  LD/ST: " << *SafePtr << "\n";
					return true;
				}
			}
		}
	}
	return false;
}


static void handleInteriors(Function &F, DenseMap<Value*, Value*> &ReplacementMap,
	DenseSet<CallBase*> &CallSites, DenseSet<ReturnInst*> &RetSites, DenseSet<StoreInst*> &Stores,
	DenseSet<Value*> &InteriorPointersSet,
  const TargetLibraryInfo *TLI, DenseSet<Value*> &SafePtrs, 
	DenseMap<Value*, Value*> &PtrToBaseMap,
	DenseSet<Value*> &SafeInteriors,
	DenseMap<Value*, Value*> &BaseToLenMap,
	DenseMap<Value*, DenseSet<Value*>> &BaseToLenSetMap,
	DenseMap<Value*, Value*> &ILoopUsages,
	DenseSet<Value*> &ICondLoop,
	DenseSet<Value*> &IGetLength,
	DenseMap<Value*, Value*> &ILenToBaseMap
	)
{
	DominatorTree DT(F);

	DenseMap<Value*, Value*> InteriorValues;
	Value *Interior;
	bool InRange;
	Value *Limit;
	int ID = 0;

	for (auto I : SafeInteriors) {
		if (!SafePtrs.count(I)) {
			if (isAliasWithSafePtr(F, DT, SafePtrs, cast<Instruction>(I))) {
				SafePtrs.insert(I);
			}
		}
	}

	for (auto I : SafeInteriors) {
		Instruction *InsertPt = cast<Instruction>(I)->getNextNode();
		if (isa<PHINode>(InsertPt)) {
			InsertPt = InsertPt->getParent()->getFirstNonPHI();
		}

		Limit = NULL;
		if (InteriorPointersSet.count(I) && !SafePtrs.count(I)) {
			assert(PtrToBaseMap.count(I));
			auto Base = PtrToBaseMap[I];
			Limit = getLimitIfAvailable(F, DT, I, InsertPt, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
			if (InRange) {
				SafePtrs.insert(I);
			}
		}
		if (Limit && isa<Instruction>(Limit) &&
				(isa<PHINode>(I) || isa<IntToPtrInst>(I)) &&
				DT.dominates(cast<Instruction>(I), cast<Instruction>(Limit))) {
			InsertPt = cast<Instruction>(Limit)->getNextNode();
		}

		InteriorValues[I] = getInteriorValue(F, InsertPt, I,
			InteriorPointersSet, SafePtrs, PtrToBaseMap, Limit, ID++,
			ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
	}



	for (auto SI : Stores) {
		auto V = SI->getValueOperand();
		Type *Ty = V->getType();
		bool IsInt = false;
		if (isa<PtrToIntInst>(V)) {
			V = cast<Instruction>(V)->getOperand(0);
			IsInt = true;
		}
		if (InteriorValues.count(V)) {
			Interior = InteriorValues[V];
		}
		else {

			Limit = NULL;
			if (InteriorPointersSet.count(V) && !SafePtrs.count(V)) {
				assert(PtrToBaseMap.count(V));
				auto Base = PtrToBaseMap[V];
				Limit = getLimitIfAvailable(F, DT, V, SI, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
				if (InRange) {
					SafePtrs.insert(V);
				}
			}

		 	Interior = getInteriorValue(F, SI, V, InteriorPointersSet, SafePtrs, PtrToBaseMap, Limit, ID++,
				ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
		}
		if (Interior) {
			if (Interior->getType() != Ty) {
				IRBuilder<> IRB(SI);
				auto Op = (IsInt) ? IRB.CreatePtrToInt(Interior, Ty) : IRB.CreateBitCast(Interior, Ty);
				SI->setOperand(0, Op);
			}
			else {
				SI->setOperand(0, Interior);
			}
		}
	}

	for (auto RI : RetSites) {
		auto V = RI->getReturnValue();
		assert(V && "return value null!");
		if (InteriorValues.count(V)) {
			Interior = InteriorValues[V];
		}
		else {

			Limit = NULL;
			if (InteriorPointersSet.count(V) && !SafePtrs.count(V)) {
				assert(PtrToBaseMap.count(V));
				auto Base = PtrToBaseMap[V];
				Limit = getLimitIfAvailable(F, DT, V, RI, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
				if (InRange) {
					SafePtrs.insert(V);
				}
			}
			Interior = getInteriorValue(F, RI, V, InteriorPointersSet, SafePtrs, PtrToBaseMap, Limit, ID++,
				ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
		}
		if (Interior) {
			if (Interior->getType() != V->getType()) {
				IRBuilder<> IRB(RI);
				RI->setOperand(0, IRB.CreateBitCast(Interior, V->getType()));
			}
			else {
				RI->setOperand(0, Interior);
			}
		}
	}

	DenseSet<Value*> LibCalls;
	DenseSet<Value*> NewCalls;
	DenseMap<Value*, LibFunc> LibFuncMap;

	for (auto CS : CallSites) {
		LibFunc Func;
		bool LibCall = false;
		bool Intrin = false;
		if (isa<IntrinsicInst>(CS)) {
			LibCall = true;
			Intrin = true;
		}
    else if (TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
			if (!TLI->isInteriorSafe(Func)) {
				LibCall = true;
			}
			LibFuncMap[CS] = Func;
		}
		if (LibCall) {
			LibCalls.insert(CS);
			auto Check = insertBoundsCheck(F, CS, Intrin);
			if (Check) {
				NewCalls.insert(Check);
			}
		}
	}

	for (auto Calls : NewCalls) {
		CallSites.insert(cast<CallBase>(Calls));
	}

	for (auto CS : CallSites) {
		bool LibCall = LibCalls.count(CS) > 0;

		DenseMap<Value*, Value*> InteriorToBase;
    AttributeList PAL = CS->getAttributes();
    for (auto ArgIt = CS->arg_begin(), End = CS->arg_end(), Start = CS->arg_begin(); ArgIt != End; ++ArgIt) {
			if (!(CS->doesNotCapture(ArgIt - Start) && (CS->doesNotAccessMemory(ArgIt - Start) ||
                                       CS->doesNotAccessMemory()))) {
    		Value *A = *ArgIt;
      	if (A->getType()->isPointerTy()) {
					if (LibCall || PAL.hasParamAttribute(ArgIt - Start, Attribute::ByVal)) {
						if (!LibFuncMap.count(CS) || !TLI->isUserArgument(LibFuncMap[CS], ArgIt - Start)) {
							auto Interior = getNoInterior(F, CS, A);
							CS->setArgOperand(ArgIt - Start, Interior);
						}
					}
					else {
						if (InteriorPointersSet.count(A) || (isa<Constant>(A) && !isa<GlobalVariable>(A))) {
							if (InteriorValues.count(A)) {
								Interior = InteriorValues[A];
							}
							else {

								Limit = NULL;
								if (InteriorPointersSet.count(A) && !SafePtrs.count(A)) {
									assert(PtrToBaseMap.count(A));
									auto Base = PtrToBaseMap[A];
									Limit = getLimitIfAvailable(F, DT, A, CS, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
									if (InRange) {
										SafePtrs.insert(A);
									}
								}
								Interior = getInteriorValue(F, CS, A, InteriorPointersSet, SafePtrs, PtrToBaseMap, Limit, ID++,
									ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
							}
							if (Interior) {
								if (Interior->getType() != A->getType()) {
									IRBuilder<> IRB(CS);
									CS->setArgOperand(ArgIt - Start, IRB.CreateBitCast(Interior, A->getType()));
								}
								else {
									CS->setArgOperand(ArgIt - Start, Interior);
								}
							}
						}
					}
      	}
			}
		}
		//if (!InteriorToBase.empty()) {
			//createInteriorCall(CS, InteriorToBase);
		//}
	}
}

static void handleLargerBase(Function &F,
	DenseSet<CallBase*> &CallSites,
	DenseSet<ReturnInst*> &RetSites,
	DenseSet<StoreInst*> &Stores,
	DenseSet<Value*> &LargerThanBaseSet,
  const TargetLibraryInfo *TLI,
	DenseSet<Value*> &SafePtrs,
	DenseMap<Value*, Value*> &PtrToBaseMap,
	DenseSet<Value*> &SafeLargerThan,
	DenseMap<Value*, Value*> &BaseToLenMap,
	DenseMap<Value*, DenseSet<Value*>> &BaseToLenSetMap,
	DenseMap<Value*, Value*> &ILoopUsages,
  DenseSet<Value*> &ICondLoop,
	DenseSet<Value*> &IGetLength,
	DenseMap<Value*, Value*> &ILenToBaseMap
	)
{
	DominatorTree DT(F);
	DenseSet<Value*> LargerThanBase;
	DenseMap<Value*, Value*> CheckedValues;
	Value *CheckedVal;
	bool InRange;

	for (auto I : SafeLargerThan) {
		if (!SafePtrs.count(I)) {
			if (isAliasWithSafePtr(F, DT, SafePtrs, cast<Instruction>(I))) {
				SafePtrs.insert(I);
			}
		}
	}

	for (auto V : LargerThanBaseSet) {
		if (!SafePtrs.count(V)) {
			LargerThanBase.insert(V);
		}
	}

	for (auto I : SafeLargerThan) {
		if (!LargerThanBase.count(I)) {
			continue;
		}
		Instruction *InsertPt = cast<Instruction>(I)->getNextNode();
		if (isa<PHINode>(InsertPt)) {
			InsertPt = InsertPt->getParent()->getFirstNonPHI();
		}

		auto Base = I->stripPointerCasts();
		auto Limit = getLimitIfAvailable(F, DT, I, InsertPt, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
		if (!InRange) {

			if (Limit && isa<Instruction>(Limit) &&
					isa<PHINode>(I) &&
					DT.dominates(cast<Instruction>(I), cast<Instruction>(Limit))) {
				InsertPt = cast<Instruction>(Limit)->getNextNode();
			}

			CheckedVal = SanCheckSize(F, InsertPt, I, Limit, ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
			CheckedValues[I] = CheckedVal;
		}
		else {
			LargerThanBase.erase(I);
		}
	}

	for (auto SI : Stores) {
		auto V = SI->getValueOperand();
		if (LargerThanBase.count(V)) {
			if (CheckedValues.count(V)) {
				CheckedVal = CheckedValues[V];
				SI->setOperand(0, CheckedVal);
			}
			else {
				auto Base = V->stripPointerCasts();
				auto Lim = getLimitIfAvailable(F, DT, V, SI, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
				assert(!InRange);
				if (!InRange) {
					CheckedVal = SanCheckSize(F, SI, V, Lim, ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
					SI->setOperand(0, CheckedVal);
				}
			}
		}
	}

	for (auto RI : RetSites) {
		auto V = RI->getReturnValue();
		if (LargerThanBase.count(V)) {
			if (CheckedValues.count(V)) {
				CheckedVal = CheckedValues[V];
				RI->setOperand(0, CheckedVal);
			}
			else {

				auto Base = V->stripPointerCasts();
				auto Lim = getLimitIfAvailable(F, DT, V, RI, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
				assert(!InRange);
				if (!InRange) {
					CheckedVal = SanCheckSize(F, RI, V, Lim, ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
					RI->setOperand(0, CheckedVal);
				}
			}
		}
	}

	for (auto CS : CallSites) {
		LibFunc Func;
		bool LibCall = false;
		if (isa<IntrinsicInst>(CS)) {
			LibCall = true;
		}
    if (TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
			if (!TLI->isInteriorSafe(Func)) {
				LibCall = true;
			}
		}
    AttributeList PAL = CS->getAttributes();
    for (auto ArgIt = CS->arg_begin(), End = CS->arg_end(), Start = CS->arg_begin(); ArgIt != End; ++ArgIt) {
			if (!(CS->doesNotCapture(ArgIt - Start) && (CS->doesNotAccessMemory(ArgIt - Start) ||
                                       CS->doesNotAccessMemory()))) {
    		Value *A = *ArgIt;
      	if (A->getType()->isPointerTy()) {
					if (!(LibCall || PAL.hasParamAttribute(ArgIt - Start, Attribute::ByVal))) {
						if (LargerThanBase.count(A)) {

							if (CheckedValues.count(A)) {
								CheckedVal = CheckedValues[A];
								CS->setArgOperand(ArgIt - Start, CheckedVal);
							}
							else {

								auto Base = A->stripPointerCasts();
								auto Lim = getLimitIfAvailable(F, DT, A, CS, Base, BaseToLenMap, BaseToLenSetMap, InRange, true);
								assert(!InRange);
								if (!InRange) {
									CheckedVal = SanCheckSize(F, CS, A, Lim, ILoopUsages, ICondLoop, IGetLength, ILenToBaseMap);
									CS->setArgOperand(ArgIt - Start, CheckedVal);
								}
							}

						}
					}
      	}
			}
		}
	}

}


static void restoreStack(Function &F, DenseSet<Instruction*> &RestorePoints, Value *StackBase)
{
  for (Instruction *I : RestorePoints) {
    IRBuilder<> IRB(I->getNextNode());
		auto Fn = F.getParent()->getOrInsertFunction("san_restore_scope", IRB.getVoidTy(), StackBase->getType());
    IRB.CreateCall(Fn, {StackBase});
  }
}


static void enableMasking(Function &F) {
	if (F.getName() == "main") {
  	Instruction *Entry = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
		IRBuilder<> IRB(Entry);
		auto Fn = F.getParent()->getOrInsertFunction("san_enable_mask", IRB.getVoidTy());
		IRB.CreateCall(Fn, {});
	}
}

static AllocaInst* copyArgsByValToAllocas1(Function &F, Argument &Arg) {
  Instruction *CopyInsertPoint = &F.front().front();
  IRBuilder<> IRB(CopyInsertPoint);
  const DataLayout &DL = F.getParent()->getDataLayout();
  //for (Argument &Arg : F.args()) {
    if (Arg.hasByValAttr()) {
      Type *Ty = Arg.getType()->getPointerElementType();
      const Align Alignment =
          DL.getValueOrABITypeAlignment(Arg.getParamAlign(), Ty);

      AllocaInst *AI = IRB.CreateAlloca(
          Ty, nullptr,
          (Arg.hasName() ? Arg.getName() : "Arg" + Twine(Arg.getArgNo())) +
              ".byval");
      AI->setAlignment(Alignment);
      Arg.replaceAllUsesWith(AI);

      uint64_t AllocSize = DL.getTypeAllocSize(Ty);
      IRB.CreateMemCpy(AI, Alignment, &Arg, Alignment, AllocSize);
			return AI;
    }
  //}
	return NULL;
}


static void
addUnsafeAllocas(Function &F, Value *Node,
	DenseSet<AllocaInst*> &UnsafeAllocas,
	DenseSet<std::pair<Value*, Value*>> &NewAllocas)
{
  SmallPtrSet<Value *, 4> Visited;
  SmallVector<Value *, 4> Worklist;
  Worklist.push_back(Node);

	assert(isa<SelectInst>(Node) || isa<PHINode>(Node));

  while (!Worklist.empty())
	{
    Value *P = Worklist.pop_back_val();

    if (!Visited.insert(P).second)
      continue;

		auto I = cast<Instruction>(P);

		for (unsigned i = 0; i < I->getNumOperands(); i++) {
			auto Op = I->getOperand(i);
			Op = Op->stripPointerCasts();
			if (isa<AllocaInst>(Op)) {
				UnsafeAllocas.insert(cast<AllocaInst>(Op));
			}
			else if (isa<Argument>(Op)) {
				AllocaInst *AI = copyArgsByValToAllocas1(F, *(cast<Argument>(Op)));
				if (AI) {
					UnsafeAllocas.insert(AI);
					NewAllocas.insert(std::make_pair(AI, Op));
				}
			}
			else if (isa<PHINode>(Op) || isa<SelectInst>(Op)) {
				Worklist.push_back(Op);
			}
		}
	}
}

static bool optimizeLimitLoopHeader(Function &F, CallInst *CI, DominatorTree *DT, LoopInfo *LI, PostDominatorTree &PDT)
{
	auto Base = CI->getArgOperand(0);
	assert(!isa<BitCastInst>(Base));


	auto L2 = LI->getLoopFor(CI->getParent());
	if (L2 == NULL) {
		return false;
	}
	auto Header = L2->getLoopPreheader();
	if (Header == NULL) {
		Header = L2->getLoopPredecessor();
		if (Header == NULL) {
			assert(!L2->isLoopInvariant(Base));
			return false;
		}
	}
	assert(L2 != LI->getLoopFor(Header));

	if (!L2->isLoopInvariant(Base)) {
		bool Changed;
		bool Ret = L2->makeLoopInvariant(Base, Changed, NULL, NULL);
		if (!Ret) {
			return false;
		}
	}


	if (PDT.dominates(CI->getParent(), Header)) {
		auto InsertPt = Header->getFirstNonPHI();
		auto BaseI = dyn_cast<Instruction>(Base);
		BasicBlock *BaseBB = (BaseI) ? BaseI->getParent() : NULL;
		if (Header == BaseBB) {
			assert(BaseI);
			if (isa<PHINode>(BaseI)) {
				InsertPt = BaseI->getParent()->getFirstNonPHI();
			}
			else {
				InsertPt = BaseI->getNextNode();
			}
		}
  	CI->removeFromParent();
		CI->insertBefore(InsertPt);
		return true;
	}
	return false;
}

static void optimizeLimitLoop(Function &F, CallInst *CI, DominatorTree *DT, LoopInfo *LI)
{
	auto Base = CI->getArgOperand(0);
	assert(!isa<BitCastInst>(Base));

	auto L2 = LI->getLoopFor(CI->getParent());
	if (L2 == NULL) {
		return;
	}

	if (!L2->isLoopInvariant(Base)) {
		return;
	}

	createCondCall(F, CI, Base, DT, LI);
}

static void optimizeFLimit(Function &F, CallInst *Call, DominatorTree *DT, LoopInfo *LI)
{
  BasicBlock *CondBlock = Call->getParent();
	auto Base = Call->getArgOperand(0);
	assert(!isa<BitCastInst>(Base));
	IRBuilder<> IRB(Call);
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int64Ty = IRB.getInt64Ty();
	Base = IRB.CreateBitCast(Base, Int8PtrTy);
	auto HighVal = IRB.CreateIntToPtr(ConstantInt::get(Int64Ty, ((1ULL<<48)-1)), Int8PtrTy);
  auto Cmp = IRB.CreateICmp(ICmpInst::ICMP_UGT, Base, HighVal);
	Instruction *Term = SplitBlockAndInsertIfThen(Cmp, Call, false, NULL, DT, LI);
	auto IfEnd = Call->getNextNode();
  Call->removeFromParent();
	Call->insertBefore(Term);

	IRB.SetInsertPoint(IfEnd);
  PHINode *PHI = IRB.CreatePHI(Int8PtrTy, 2);
  PHI->addIncoming(Base, CondBlock);
  BasicBlock *ThenBlock = Term->getParent();
	Call->replaceAllUsesWith(PHI);
  PHI->addIncoming(Call, ThenBlock);
}

static CallInst* optimizeLimit(Function &F, CallInst *CI, bool MayNull)
{
	auto M = F.getParent();
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	FunctionCallee Fn;
	if (!MayNull) {
		Fn = M->getOrInsertFunction("fasan_limit", CI->getType(), Base->getType());
	}
	else {
		Fn = M->getOrInsertFunction("fasan_limit_check", CI->getType(), Base->getType());
	}
	auto Call = IRB.CreateCall(Fn, {Base});
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::NoCallerSaved);
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::InaccessibleMemOnly);
	//MDNode *N = MDNode::get(Call->getContext(), {});
	//Call->setMetadata("fasansize", N);
	CI->replaceAllUsesWith(Call);
	CI->eraseFromParent();
	return Call;

#if 0
	assert(!Call->uses().empty());
	IRBuilder<> IRB(Call);
	auto Base = Call->getArgOperand(0);
	auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int64Ty = IRB.getInt64Ty();
	auto Int32Ty = IRB.getInt32Ty();
	auto Int32PtrTy = Int32Ty->getPointerTo();

	auto BaseInt = IRB.CreatePtrToInt(Base, Int64Ty);
	auto Offset = IRB.CreateLShr(BaseInt, 49);

  auto SlowPath = IRB.CreateICmp(ICmpInst::ICMP_UGE, Offset, ConstantInt::get(Int64Ty, ((1ULL<<15)-1)));
	Instruction *IfTerm, *ElseTerm, *EndElse;
	EndElse = Call->getNextNode();

  SplitBlockAndInsertIfThenElse(SlowPath, CI, &IfTerm, &ElseTerm);
	IRB.SetInsertPoint(IfTerm);

	Call->removeFromParent();
  Call->insertBefore(IfTerm);

	IRB.SetInsertPoint(ElseTerm);

	auto NewBase = IRB.CreateAnd(BaseInt, ConstantInt::get(Int64Ty, (0x1ULL<<49)-1));
	NewBase = IRB.CreateSub(NewBase, Offset);
	NewBase = IRB.CreateIntToPtr(NewBase, Int8PtrTy);

	IRB.SetInsertPoint(EndTerm);

  PHINode *PHI = IRB.CreatePHI(Int8PtrTy, 2);

  BasicBlock *IfBlock = IfTerm->getParent();
  BasicBlock *ElseBlock = ElseTerm->getParent();
  PHI->addIncoming(NewBase, ElseBlock);
	Call->replaceAllUsesWith(PHI);
  PHI->addIncoming(Call, IfBlock);
#endif
}


static CallInst* optimizeInterior(Function &F, CallInst *CI, DenseMap<Value*, Value*> &LimitToRealBase)
{
	assert(!CI->uses().empty());

	auto M = F.getParent();
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto Limit = CI->getArgOperand(4);
	bool Static = false;
	if (!isa<Constant>(Limit)) {
		assert(LimitToRealBase.count(Limit));
		Base = LimitToRealBase[Limit];
		assert(Base);
	}
	else {
		Static = true;
	}

	FunctionCallee Fn;
	if (!Static) {
		Ptr = buildNoInterior(F, IRB, Ptr);
		Fn = M->getOrInsertFunction("fasan_interior", CI->getType(), Base->getType(), Ptr->getType());
	}
	else {
		Fn = M->getOrInsertFunction("fasan_interior1", CI->getType(), Base->getType(), Ptr->getType());
	}
	auto Call = IRB.CreateCall(Fn, {Base, Ptr});
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::NoCallerSaved);
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::InaccessibleMemOnly);
	CI->replaceAllUsesWith(Call);
	CI->eraseFromParent();
	return Call;


#if 0
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto Int64Ty = IRB.getInt64Ty();
	auto MaxOffset = ConstantInt::get(Int64Ty, ((1ULL<<15)-1));
	auto PtrMask = ConstantInt::get(Int64Ty, (0x1ULL<<49)-1);
	auto RetTy = CI->getType();
	auto OrigBlock = CI->getParent();

	auto RetPtr = IRB.CreateBitCast(Ptr, RetTy);
	auto BaseInt = IRB.CreatePtrToInt(Base, Int64Ty);
	auto Offset = IRB.CreateLShr(BaseInt, 49);

  auto SlowPath = IRB.CreateICmp(ICmpInst::ICMP_ULT, Offset, MaxOffset);
	Instruction *IfTerm;

  IfTerm = SplitBlockAndInsertIfThen(SlowPath, CI, false);
	IRB.SetInsertPoint(IfTerm);

	auto PtrInt = IRB.CreatePtrToInt(Ptr, Int64Ty);
	auto Diff = IRB.CreateSub(PtrInt, BaseInt);
	auto NewOffset = IRB.CreateAdd(Offset, Diff);
  auto Cmp = IRB.CreateICmp(ICmpInst::ICMP_ULT, NewOffset, MaxOffset);
	auto FinalOffset = IRB.CreateSelect(Cmp, NewOffset, MaxOffset);
	FinalOffset = IRB.CreateShl(FinalOffset, 49);

	auto RetVal = IRB.CreateAnd(PtrInt, PtrMask);
	RetVal = IRB.CreateOr(RetVal, FinalOffset);
	RetVal = IRB.CreateIntToPtr(RetVal, RetTy);

	IRB.SetInsertPoint(CI);

  PHINode *PHI = IRB.CreatePHI(RetTy, 2);

  PHI->addIncoming(RetPtr, OrigBlock);
  BasicBlock *IfBlock = IfTerm->getParent();
  PHI->addIncoming(RetVal, IfBlock);

	CI->replaceAllUsesWith(PHI);
	CI->eraseFromParent();
#endif
}

static CallInst* optimizeCheckSize(Function &F, CallInst *CI, DenseMap<Value*, Value*> &LimitToRealBase)
{
	assert(!CI->uses().empty());

	auto M = F.getParent();
	IRBuilder<> IRB(CI);
	auto Ptr = CI->getArgOperand(0);
	auto PtrSz = CI->getArgOperand(1);
	auto Limit = CI->getArgOperand(2);

	auto Fn = M->getOrInsertFunction("fasan_check_size", CI->getType(), Ptr->getType(), PtrSz->getType(), Limit->getType());
	auto Call = IRB.CreateCall(Fn, {Ptr, PtrSz, Limit});
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::NoCallerSaved);
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::InaccessibleMemOnly);
	CI->replaceAllUsesWith(Call);
	CI->eraseFromParent();
	return Call;
#if 0
	assert(!CI->uses().empty());
	IRBuilder<> IRB(CI);
	auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Ptr = CI->getArgOperand(0);
	auto PtrSz = CI->getArgOperand(1);
	auto Limit = CI->getArgOperand(2);
	auto Int64Ty = IRB.getInt64Ty();
	auto RetTy = CI->getType();

	auto Ptr8 = IRB.CreateBitCast(Ptr, Int8PtrTy);
	auto PtrLimit = IRB.CreateGEP(Int8Ty, Ptr8, PtrSz);
	auto IsInvalid = IRB.CreateICmp(ICmpInst::ICMP_UGT, PtrLimit, Limit);

	auto PtrInt = IRB.CreatePtrToInt(Ptr, Int64Ty);
	auto PtrVal = IRB.CreateOr(PtrInt, IRB.CreateShl(IRB.CreateZExt(IsInvalid, Int64Ty), 48));
	PtrVal = IRB.CreateIntToPtr(PtrVal, RetTy);

	CI->replaceAllUsesWith(PtrVal);
	CI->eraseFromParent();
#endif
}

static BasicBlock* getTrapBB(Function *Fn)
{
  auto TrapBB = BasicBlock::Create(Fn->getContext(), "trap", Fn);
  IRBuilder<> IRB(TrapBB);

  auto *F = Intrinsic::getDeclaration(Fn->getParent(), Intrinsic::trap);
  CallInst *TrapCall = IRB.CreateCall(F, {});
  TrapCall->setDoesNotReturn();
  TrapCall->setDoesNotThrow();
  IRB.CreateUnreachable();
	return TrapBB;
}

static bool
isIndVarArith(Instruction *I, Value *IndVar, Loop *L)
{
	auto Opcode = I->getOpcode();
	if (!(Opcode == Instruction::Add || Opcode == Instruction::Sub)) {
		return false;
	}
	if (I->getOperand(0) == IndVar && L->isLoopInvariant(I->getOperand(1))) {
		return true;
	}
	if (I->getOperand(1) == IndVar && L->isLoopInvariant(I->getOperand(0))) {
		return true;
	}
	return false;
}

static bool
canMoveOutsideLoop(Value *V, Loop *L, ScalarEvolution &SE,
	BasicBlock *Header, Instruction* &Lo, Instruction* &Hi,
	DominatorTree *DT)
{
	V = V->stripPointerCasts();
	auto GEP = dyn_cast<GetElementPtrInst>(V);
	if (!GEP) {
		return false;
	}

	if (!L->isLoopSimplifyForm()) {
		//errs() << "Not In Simplyfy Form\n";
		return false;
	}

	//errs() << "V:: " << *V << "\n";
	auto IndVar = L->getInductionVariable(SE);
	if (IndVar == NULL) {
		//errs() << "No IndVar\n";
		return false;
	}

	auto Bounds = L->getBounds(SE);
	if (Bounds == None) {
		//errs() << "Bounds are not available\n";
		//errs() << *L << "\n";
		return false;
	}
	auto Dir = Bounds->getDirection();
	if (Dir == Loop::LoopBounds::Direction::Unknown) {
		//errs() << "Direction is unknown\n";
		return false;
	}
	Value* Initial = &Bounds->getInitialIVValue();
	Value* Final = &Bounds->getFinalIVValue();

	if (isa<Instruction>(Initial)) {
		auto Inst = cast<Instruction>(Initial);
		if (!DT->dominates(Inst->getParent(), Header)) {
			return false;
		}
	}

	if (isa<Instruction>(Final)) {
		auto Inst = cast<Instruction>(Final);
		if (!DT->dominates(Inst->getParent(), Header)) {
			return false;
		}
	}

	//Loop::LoopBounds::Direction::Increasing
	//errs() << "Initial: " << *Initial << "\n";
	//errs() << "Final: " << *Final << "\n";
	bool StepInst;
	auto Pred = Bounds->getPredicate1(StepInst);
	bool Equals = CmpInst::isTrueWhenEqual(Pred);
	//assert(Equals == 0);
	//errs() << "Equals:: " << Equals << "\n";
	//errs() << "Pred:: " << Pred << "\n";

	int NumOperands = GEP->getNumOperands();
	int i;

  for (i = 0; i < NumOperands; i++) {
    auto *Op = dyn_cast<Instruction>(GEP->getOperand(i));
		if (Op && !L->isLoopInvariant(Op)) {
			if (Op != IndVar) {
				if (!isIndVarArith(cast<Instruction>(Op), IndVar, L)) {
					return false;
				}
				errs() << "IndVarArith:: " << *Op << "\n";
				//auto Aux = dyn_cast<PHINode>(Op);
				//if (!Aux || !L->isAuxiliaryInductionVariable(*Aux, SE)) {
				//}
				//errs() << "Aux-OP:: " << *Aux << "\n";
			}
		}
  }
	auto InsertPt = Header->getTerminator();

	if (StepInst) {
		if (Equals == 0) {
			IRBuilder<> IRB(InsertPt);
			auto StepValue = Bounds->getStepValue();
			if (!StepValue) {
				return false;
			}
			assert(StepValue);
			Final = IRB.CreateSub(Final, StepValue);
		}
	}
	else {
		if (Equals) {
			IRBuilder<> IRB(InsertPt);
			auto StepValue = Bounds->getStepValue();
			assert(StepValue);
			if (!StepValue) {
				return false;
			}
			Final = IRB.CreateAdd(Final, StepValue);
		}
	}

	//auto StepI = &Bounds->getStepInst();
	//errs() << "StepI:: " << *StepI << "\n";

	Lo = GEP->clone();
	Lo->insertBefore(InsertPt);
	Hi = GEP->clone();
	Hi->insertBefore(InsertPt);

	Value *LoVal = (Dir == Loop::LoopBounds::Direction::Increasing) ? Initial : Final;
	Value *HiVal = (Dir == Loop::LoopBounds::Direction::Increasing) ? Final : Initial;

	//errs() << "LoVal:: " << *LoVal << "\n";
	//errs() << "HiVal:: " << *HiVal << "\n";
	bool HasInv = false;

  for (i = 0; i < NumOperands; i++) {
    auto *Op = dyn_cast<Instruction>(Lo->getOperand(i));
		if (Op && !L->isLoopInvariant(Op)) {
			//errs() << "Op:: " << *Op << "\n";
			//assert(Op == IndVar || L->isAuxiliaryInductionVariable(*(cast<PHINode>(Op)), SE));
			if (isIndVarArith(Op, IndVar, L)) {
				auto NewLow = Op->clone();
				auto NewHi = Op->clone();
				NewLow->insertBefore(Lo);
				NewHi->insertBefore(Hi);
				if (NewLow->getOperand(0) == IndVar) {
					NewLow->setOperand(0, LoVal);
					NewHi->setOperand(0, HiVal);
				}
				else {
					assert(NewLow->getOperand(1) == IndVar);
					NewLow->setOperand(1, LoVal);
					NewHi->setOperand(1, HiVal);
				}
				Lo->setOperand(i, NewLow);
				Hi->setOperand(i, NewHi);
			}
			else {
				assert(Op == IndVar);
				Lo->setOperand(i, LoVal);
				Hi->setOperand(i, HiVal);
			}
			HasInv = true;
		}
  }
	assert(HasInv);
	//errs() << "Lo:: " << *Lo << "\n";
	//errs() << "Hi:: " << *Hi << "\n";
	//errs() << "IndVar:: " << *IndVar << "\n";

	return true;
}

static void optimizeAbortLoopHeaderHelper(Function &F, CallInst *CI, PostDominatorTree &PDT,
	Instruction *Hi, Instruction *Lo, LoopInfo *LI)
{
	auto L2 = LI->getLoopFor(CI->getParent());
	if (L2 == NULL) {
		return;
	}

	bool Changed;
	bool Ret = L2->makeLoopInvariant(Hi, Changed, NULL, NULL);
	Ret &= L2->makeLoopInvariant(Lo, Changed, NULL, NULL);

	if (Ret == false) {
		return;
	}

	auto Header = L2->getLoopPreheader();
	if (Header == NULL) {
		return;
	}

	if (PDT.dominates(CI->getParent(), Header)) {
		auto InsertPt = Header->getTerminator();
  	CI->removeFromParent();
		CI->insertBefore(InsertPt);
		optimizeAbortLoopHeaderHelper(F, CI, PDT, Hi, Lo, LI);
		errs() << "NewMove:: " << *CI << "\n";
	}
}

static bool optimizeAbortLoopHeader(Function &F, CallInst *CI, DominatorTree *DT, LoopInfo *LI, PostDominatorTree &PDT,
	ScalarEvolution &SE)
{
	Instruction *Lo;
	Instruction *Hi;

	auto Ptr = CI->getArgOperand(1);
	Ptr = Ptr->stripPointerCasts();
	auto TySize = CI->getArgOperand(3);

	//%37 = bitcast %union.tree_node** %type4.i to i64**
	//assert(!isa<BitCastInst>(Ptr) || isa<IntToPtrInst>(Ptr));

	auto L2 = LI->getLoopFor(CI->getParent());
	if (L2 == NULL) {
		return false;
	}

	auto Header = L2->getLoopPreheader();

	if (Header == NULL) {
		Header = L2->getLoopPredecessor();
		if (Header == NULL) {
			assert(!L2->isLoopInvariant(Ptr));
			return false;
		}
	}
	assert(L2 != LI->getLoopFor(Header));

	if (!L2->isLoopInvariant(TySize)) {
		return false;
	}

	if (!L2->isLoopInvariant(Ptr)) {

		if (PDT.dominates(CI->getParent(), Header)) {

			if (canMoveOutsideLoop(Ptr, L2, SE, Header, Lo, Hi, DT)) {
				errs() << "Moving Abort:: " << *CI << "\n";
				auto InsertPt = Header->getTerminator();
  			CI->removeFromParent();
				CI->insertBefore(InsertPt);
				auto OrigPtr = CI->getArgOperand(1);
				if (OrigPtr->getType() != Lo->getType()) {
					IRBuilder<> IRB(CI);
					Lo = cast<Instruction>(IRB.CreateBitCast(Lo, OrigPtr->getType()));
				}
				CI->setArgOperand(1, Lo);
				IRBuilder<> IRB(CI);
				auto TySize = CI->getArgOperand(3);
				Hi = cast<Instruction>(IRB.CreateGEP(IRB.CreateBitCast(Hi, IRB.getInt8PtrTy()), TySize));
				CI->setArgOperand(6, Hi);
				CI->setArgOperand(4, ConstantInt::get(IRB.getInt64Ty(), 0));
				MDNode* N = MDNode::get(CI->getContext(), {});
				CI->setMetadata("san_loopind", N);
				optimizeAbortLoopHeaderHelper(F, CI, PDT, Hi, Lo, LI);
			}
		}

		return false;
	}


	if (PDT.dominates(CI->getParent(), Header)) {
		auto InsertPt = Header->getTerminator();
  	CI->removeFromParent();
		CI->insertBefore(InsertPt);
		return true;
	}
	return false;
}

#if 0
static bool
canMoveOutsideLoop(Value *V, Loop *L, ScalarEvolution &SE)
{

	auto Bounds = L->getBounds(SE);
	if (Bounds == None) {
		errs() << "Bounds are not available\n";
		errs() << *L << "\n";
		return false;
	}
	auto Dir = Bounds->getDirection();
	if (Dir == Loop::LoopBounds::Direction::Unknown) {
		errs() << "Direction is unknown\n";
		return false;
	}
	Value* Initial = &Bounds->getInitialIVValue();
	Value* Final = &Bounds->getFinalIVValue();
	//Loop::LoopBounds::Direction::Increasing
	errs() << "Initial: " << *Initial << "\n";
	errs() << "Final: " << *Final << "\n";
	//errs() << "Dir: " << Dir << "\n";

	V = V->stripPointerCasts();
	errs() << "Checking : " << *V << "\n";
	auto GEP = dyn_cast<GetElementPtrInst>(V);
	if (!GEP) {
		return false;
	}
	int NumOperands = GEP->getNumOperands();
	int i;

  for (i = 0; i < NumOperands; i++) {
    auto *Op = dyn_cast<Instruction>(GEP->getOperand(i));
		if (Op && !L->isLoopInvariant(Op)) {
			if (Op != L->getInductionVariable(SE)) {
				errs() << "Op - non-ind: " << *Op << "\n";
				return false;
			}
		}
  }
	return true;
}
#endif

static void optimizeAbortLoop(Function &F, CallInst *CI, DominatorTree *DT, LoopInfo *LI/*, ScalarEvolution &SE*/)
{
	auto Ptr = CI->getArgOperand(1);
	auto SP = Ptr->stripPointerCasts();
	auto PtrLimit = CI->getArgOperand(6);
	//assert(!isa<BitCastInst>(Ptr) || isa<IntToPtrInst>(Ptr));

	auto L2 = LI->getLoopFor(CI->getParent());
	if (L2 == NULL) {
		return;
	}

	/*if (canMoveOutsideLoop(SP, L2, SE)) {
		errs() << "CAN MOVE: " << *CI << "\n";
	}*/

	if (!L2->isLoopInvariant(SP) || !L2->isLoopInvariant(PtrLimit)) {
		return;
	}
	//assert(isa<Constant>(PtrLimit));
	auto InsertPt = isa<Instruction>(SP) ? cast<Instruction>(SP)->getNextNode() : cast<Instruction>(F.begin()->getFirstInsertionPt());
	callOnceInLoopAfterDef(F, CI, InsertPt, DT, LI);
}

static bool checkLowerBound(Function &F, Value *Base, Value *Ptr)
{
	Base = Base->stripPointerCasts();
	Ptr = Ptr->stripPointerCasts();

  const DataLayout &DL = F.getParent()->getDataLayout();
	int64_t Offset;
	Value *PBase = GetPointerBaseWithConstantOffset(Ptr, Offset, DL);
	if (PBase == Base && Offset >= 0 && Offset < (4LL<<20)) {
		return false;
	}
	return true;
}

static void optimizeFBound(Function &F, CallInst *CI, BasicBlock *TrapBB)
{
	//return;
	auto InsertPt = CI->getNextNode();
	IRBuilder<> IRB(InsertPt);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto PtrLimit = CI->getArgOperand(2);
	auto Limit = CI->getArgOperand(3);
	auto Int8PtrTy = IRB.getInt8PtrTy();

	bool checkLower = checkLowerBound(F, Base, Ptr);

	if (Base->getType() != Int8PtrTy) {
		Base = IRB.CreateBitCast(Base, Int8PtrTy);
	}

	if (Ptr->getType() != Int8PtrTy) {
		Ptr = IRB.CreateBitCast(Ptr, Int8PtrTy);
	}
	assert(PtrLimit->getType() == Int8PtrTy);
	assert(Limit->getType() == Int8PtrTy);
	Value *Cmp;

	if (checkLower) {
		auto Cmp1 = IRB.CreateICmpULT(Ptr, Base);
		auto Cmp2 = IRB.CreateICmpULT(Limit, PtrLimit);
		Cmp = IRB.CreateOr(Cmp1, Cmp2);

		if (CI->hasMetadata("san_loopind")) {
			auto Cmp3 = IRB.CreateICmpULT(PtrLimit, Base);
			Cmp = IRB.CreateOr(Cmp, Cmp3);
		}
	}
	else {
		errs() << "Saving Lower\n";
		Cmp = IRB.CreateICmpULT(Limit, PtrLimit);

		if (CI->hasMetadata("san_loopind")) {
			auto Cmp3 = IRB.CreateICmpULT(PtrLimit, Base);
			Cmp = IRB.CreateOr(Cmp, Cmp3);
		}
	}


	Instruction *Then = SplitBlockAndInsertIfThen(Cmp, InsertPt, false);
	IRB.SetInsertPoint(Then);
	IRB.CreateBr(TrapBB);
	Then->eraseFromParent();
	CI->eraseFromParent();
}

static void optimizeFInterior(Function &F, CallInst *CI, AAResults *AA)
{
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto Int64Ty = IRB.getInt64Ty();
	auto MaxOffset = ConstantInt::get(Int64Ty, ((1ULL<<15)-1));

	assert(AA->alias(MemoryLocation(Base), MemoryLocation(Ptr)) != MustAlias);

	auto PtrInt = IRB.CreatePtrToInt(Ptr, Int64Ty);
	auto BaseInt = IRB.CreatePtrToInt(Base, Int64Ty);
	auto Diff = IRB.CreateSub(PtrInt, BaseInt);
  auto Cmp = IRB.CreateICmp(ICmpInst::ICMP_ULT, Diff, MaxOffset);
	auto FinalOffset = IRB.CreateSelect(Cmp, Diff, MaxOffset);
	FinalOffset = IRB.CreateShl(FinalOffset, 49);
	auto RetVal = IRB.CreateOr(PtrInt, FinalOffset);
	RetVal = IRB.CreateIntToPtr(RetVal, CI->getType());
	CI->replaceAllUsesWith(RetVal);
	CI->eraseFromParent();
}


static void optimizeFInteriorCheck(Function &F, CallInst *CI, AAResults *AA)
{

	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto PtrSz = CI->getArgOperand(2);
	auto Limit = CI->getArgOperand(3);
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int8Ty = IRB.getInt8Ty();
	auto Int64Ty = IRB.getInt64Ty();

	assert(AA->alias(MemoryLocation(Base), MemoryLocation(Ptr)) != MustAlias);

	if (Base->getType() != Int8PtrTy) {
		Base = IRB.CreateBitCast(Base, Int8PtrTy);
	}

	if (Ptr->getType() != Int8PtrTy) {
		Ptr = IRB.CreateBitCast(Ptr, Int8PtrTy);
	}
	assert(Limit->getType() == Int8PtrTy);
	assert(PtrSz->getType()->isIntegerTy());

	auto PtrLimit = IRB.CreateGEP(Int8Ty, Ptr, PtrSz);

	auto Cmp1 = IRB.CreateICmpULT(Ptr, Base);
	auto Cmp2 = IRB.CreateICmpULT(Limit, PtrLimit);
	auto Invalid = IRB.CreateOr(Cmp1, Cmp2);


	auto MaxOffset = ConstantInt::get(Int64Ty, ((1ULL<<15)-1));


	auto PtrInt = IRB.CreatePtrToInt(Ptr, Int64Ty);
	auto BaseInt = IRB.CreatePtrToInt(Base, Int64Ty);
	auto Diff = IRB.CreateSub(PtrInt, BaseInt);
  auto Cmp = IRB.CreateICmp(ICmpInst::ICMP_ULT, Diff, MaxOffset);
	auto FinalOffset = IRB.CreateSelect(Cmp, Diff, MaxOffset);
	FinalOffset = IRB.CreateShl(FinalOffset, 49);
	auto RetVal = IRB.CreateOr(PtrInt, FinalOffset);
	RetVal = IRB.CreateOr(RetVal, IRB.CreateShl(IRB.CreateZExt(Invalid, Int64Ty), 48));
	RetVal = IRB.CreateIntToPtr(RetVal, CI->getType());
	CI->replaceAllUsesWith(RetVal);
	CI->eraseFromParent();
}

static void optimizeFCheckSize(Function &F, CallInst *CI)
{

	IRBuilder<> IRB(CI);
	auto Ptr = CI->getArgOperand(0);
	auto PtrSz = CI->getArgOperand(1);
	auto Limit = CI->getArgOperand(2);
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int8Ty = IRB.getInt8Ty();
	auto Int64Ty = IRB.getInt64Ty();


	if (Ptr->getType() != Int8PtrTy) {
		Ptr = IRB.CreateBitCast(Ptr, Int8PtrTy);
	}
	assert(Limit->getType() == Int8PtrTy);
	assert(PtrSz->getType()->isIntegerTy());


	auto PtrLimit = IRB.CreateGEP(Int8Ty, Ptr, PtrSz);
	auto PtrBase = Ptr->stripPointerCasts();

	if (!isa<AllocaInst>(PtrBase) && !isa<GlobalVariable>(PtrBase)) {
		PtrLimit = buildNoInterior(F, IRB, PtrLimit);
	}
	auto Invalid = IRB.CreateICmpULT(Limit, PtrLimit);
	Invalid = IRB.CreateShl(IRB.CreateZExt(Invalid, Int64Ty), 48);

	auto Fn = Intrinsic::getDeclaration(F.getParent(), Intrinsic::ptrunmask, {Int8PtrTy, Int8PtrTy, Int64Ty});
	Ptr = IRB.CreateCall(Fn, {Ptr, Invalid});

	CI->replaceAllUsesWith(Ptr);
	CI->eraseFromParent();
}



static CallInst* optimizeAbort(Function &F, CallInst *CI, bool Abort2, BasicBlock *TrapBB, DenseMap<Value*, Value*> &LimitToRealBase)
{
	auto M = F.getParent();
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto Limit = CI->getArgOperand(2);
	auto TySize = CI->getArgOperand(3);
	auto Padding = CI->getArgOperand(4);
	FunctionCallee Fn;
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int8Ty = IRB.getInt8Ty();
	Value *RealBase;
	bool Static = false;

	auto PaddingSz = cast<ConstantInt>(Padding)->getSExtValue();
	assert(PaddingSz <= 0);

	if (Limit->getType()->isIntegerTy()) {
		auto Base8 = IRB.CreateBitCast(Base, Int8PtrTy);
		Limit = IRB.CreateGEP(Int8Ty, Base8, Limit);
		RealBase = Base;
		Static = true;
	}
	else {
		if (!LimitToRealBase.count(Limit)) {
			errs() << "Limit : " << *Limit << "\n";
			errs() << F << "\n";
		}
		assert(LimitToRealBase.count(Limit));
		RealBase = LimitToRealBase[Limit];
		assert(RealBase);
		Ptr = buildNoInterior(F, IRB, Ptr);
	}

	assert(Limit->getType() == Int8PtrTy);

	Value* PtrLimit = CI->getArgOperand(6);
	auto Ptr8 = IRB.CreateBitCast(Ptr, Int8PtrTy);

	if (isa<Constant>(PtrLimit)) {
		assert(cast<Constant>(PtrLimit)->isNullValue());
		PtrLimit = IRB.CreateGEP(Int8Ty, Ptr8, TySize);
	}
	else {
		if (!Static) {
			PtrLimit = buildNoInterior(F, IRB, PtrLimit);
		}
	}

	if (PaddingSz != 0) {
		Ptr8 = IRB.CreateGEP(Int8Ty, Ptr8, Padding);
	}


	if (!Static) {
		Fn = M->getOrInsertFunction("fasan_bounds",
			CI->getType(), RealBase->getType(), Ptr8->getType(), PtrLimit->getType(), Limit->getType());
	}
	else {
		Fn = M->getOrInsertFunction("fasan_bounds1",
			CI->getType(), RealBase->getType(), Ptr8->getType(), PtrLimit->getType(), Limit->getType());
	}

	auto Call = IRB.CreateCall(Fn, {RealBase, Ptr8, PtrLimit, Limit});
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::NoCallerSaved);
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::InaccessibleMemOnly);

	if (CI->hasMetadata("san_loopind")) {
		MDNode* N = MDNode::get(Call->getContext(), {});
		Call->setMetadata("san_loopind", N);
	}

	if (F.getSubprogram()) {
    if (auto DL = CI->getDebugLoc()) {
      Call->setDebugLoc(DL);
		}
  }

	CI->eraseFromParent();
	return Call;

#if 0
	auto M = F.getParent();
	IRBuilder<> IRB(CI);

	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto Limit = CI->getArgOperand(2);
	auto TySize = CI->getArgOperand(3);
	auto Padding = CI->getArgOperand(4);

	auto CallSite = CI->getArgOperand(5);

	auto PaddingSz = cast<ConstantInt>(Padding)->getSExtValue();
	assert(PaddingSz <= 0);

	auto PtrSz = cast<ConstantInt>(TySize)->getZExtValue();
	auto Int64Ty = IRB.getInt64Ty();
	auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();

	auto Base8 = IRB.CreateBitCast(Base, Int8PtrTy);
	auto BaseOffset = getPtrOffset(F, IRB, Base8);
	BaseOffset = IRB.CreateNeg(BaseOffset);
	auto NewBase = IRB.CreateGEP(Base8, BaseOffset);

	auto Ptr8 = IRB.CreateBitCast(Ptr, Int8PtrTy);
	Value *PtrLimit = IRB.CreateGEP(Int8Ty, Ptr8, TySize);

	if (PaddingSz != 0) {
		Ptr8 = IRB.CreateGEP(Int8Ty, Ptr8, Padding);
	}

	if (Limit->getType()->isIntegerTy()) {
		Limit = IRB.CreateGEP(Int8Ty, Base8, Limit);
	}
	assert(Limit->getType() == Int8PtrTy);

	auto Cmp1 = IRB.CreateICmpULT(Ptr8, NewBase);
	auto Cmp2 = IRB.CreateICmpULT(Limit, PtrLimit);
	auto Cmp = IRB.CreateOr(Cmp1, Cmp2);

	auto Intrinsic = dyn_cast<IntrinsicInst>(Base);
	if (Intrinsic && Intrinsic->getIntrinsicID() != Intrinsic::safe_load) {
		assert(0);
	}

	Instruction *Then = SplitBlockAndInsertIfThen(Cmp, CI, false);
	IRB.SetInsertPoint(Then);

	FunctionCallee Fn;
	Limit = IRB.CreateGEP(Limit, ConstantInt::get(Int64Ty, -PtrSz));
	if (Abort2) {
		Fn = M->getOrInsertFunction("san_abort2_fast", IRB.getVoidTy(), Int8PtrTy, Int8PtrTy, Int8PtrTy, CallSite->getType());
	}
	else {
		Fn = M->getOrInsertFunction("san_abort3_fast", IRB.getVoidTy(), Int8PtrTy, Int8PtrTy, Int8PtrTy, CallSite->getType());
	}
	auto Call = IRB.CreateCall(Fn, {Base8, Ptr8, Limit, CallSite});
	//Call->addAttribute(AttributeList::FunctionIndex, Attribute::NoCallerSaved);
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::InaccessibleMemOnly);
	CI->eraseFromParent();
#endif
}



static CallInst* optimizeCheckSizeOffset(Function &F, CallInst *CI, DenseMap<Value*, Value*> &LimitToRealBase)
{
	assert(!CI->uses().empty());

	auto M = F.getParent();
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Ptr = CI->getArgOperand(1);
	auto PtrSz = CI->getArgOperand(2);
	auto Limit = CI->getArgOperand(3);
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int8Ty = IRB.getInt8Ty();
	Value *RealBase;
	bool Static = false;

	if (Limit->getType()->isIntegerTy()) {
		auto Base8 = IRB.CreateBitCast(Base, Int8PtrTy);
		Limit = IRB.CreateGEP(Int8Ty, Base8, Limit);
		RealBase = Base;
		Static = true;
	}
	else {
		if (!LimitToRealBase.count(Limit)) {
			errs() << "Limit : " << *Limit << "\n";
			errs() << F << "\n";
		}
		assert(LimitToRealBase.count(Limit));
		RealBase = LimitToRealBase[Limit];
		assert(RealBase);
	}

	FunctionCallee Fn;

	if (!Static) {
		Ptr = buildNoInterior(F, IRB, Ptr);
		Fn = M->getOrInsertFunction("fasan_check_interior",
			CI->getType(), RealBase->getType(), Ptr->getType(), PtrSz->getType(), Limit->getType());
	}
	else {
		Fn = M->getOrInsertFunction("fasan_check_interior1",
			CI->getType(), RealBase->getType(), Ptr->getType(), PtrSz->getType(), Limit->getType());
	}
	auto Call = IRB.CreateCall(Fn, {RealBase, Ptr, PtrSz, Limit});
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::NoCallerSaved);
	Call->addAttribute(AttributeList::FunctionIndex, Attribute::InaccessibleMemOnly);
	CI->replaceAllUsesWith(Call);
	CI->eraseFromParent();
	return Call;


#if 0
	assert(!CI->uses().empty());
	IRBuilder<> IRB(CI);
	auto Base = CI->getArgOperand(0);
	auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Ptr = CI->getArgOperand(1);
	auto PtrSz = CI->getArgOperand(2);
	auto Limit = CI->getArgOperand(3);
	auto Int64Ty = IRB.getInt64Ty();
	auto MaxOffset = ConstantInt::get(Int64Ty, ((1ULL<<15)-1));
	auto PtrMask = ConstantInt::get(Int64Ty, (0x1ULL<<49)-1);
	auto RetTy = CI->getType();
	auto OrigBlock = CI->getParent();

	auto PtrInt = IRB.CreatePtrToInt(Ptr, Int64Ty);
	auto BaseInt = IRB.CreatePtrToInt(Base, Int64Ty);
	auto Offset = IRB.CreateLShr(BaseInt, 49);
  auto SlowPath = IRB.CreateICmp(ICmpInst::ICMP_ULT, Offset, MaxOffset);
	Instruction *IfTerm;

  IfTerm = SplitBlockAndInsertIfThen(SlowPath, CI, false);
	IRB.SetInsertPoint(IfTerm);

	auto Diff = IRB.CreateSub(PtrInt, BaseInt);
	auto NewOffset = IRB.CreateAdd(Offset, Diff);
  auto Cmp = IRB.CreateICmp(ICmpInst::ICMP_ULT, NewOffset, MaxOffset);
	auto FinalOffset = IRB.CreateSelect(Cmp, NewOffset, MaxOffset);
	FinalOffset = IRB.CreateShl(FinalOffset, 49);

	auto RetVal = IRB.CreateAnd(PtrInt, PtrMask);
	RetVal = IRB.CreateOr(RetVal, FinalOffset);

	IRB.SetInsertPoint(CI);

  PHINode *PHI = IRB.CreatePHI(Int64Ty, 2);

  PHI->addIncoming(PtrInt, OrigBlock);
  BasicBlock *IfBlock = IfTerm->getParent();
  PHI->addIncoming(RetVal, IfBlock);


	auto Ptr8 = IRB.CreateBitCast(Ptr, Int8PtrTy);
	auto PtrLimit = IRB.CreateGEP(Int8Ty, Ptr8, PtrSz);
	auto IsInvalid = IRB.CreateICmp(ICmpInst::ICMP_UGT, PtrLimit, Limit);

	auto PtrVal = IRB.CreateOr(PHI, IRB.CreateShl(IRB.CreateZExt(IsInvalid, Int64Ty), 48));
	PtrVal = IRB.CreateIntToPtr(PtrVal, RetTy);

	CI->replaceAllUsesWith(PtrVal);
	CI->eraseFromParent();
#endif
}

static bool
canReplaceHelper(CallInst *Call1, CallInst *Call2,
	AAResults *AA
)
{
	auto Call1Ptr = Call1->getArgOperand(1)->stripPointerCasts();
	auto Call2Ptr = Call2->getArgOperand(1)->stripPointerCasts();
	auto AR = (Call1Ptr == Call2Ptr) ? MustAlias : MayAlias;
	if (AR != MustAlias) {
		AR = AA->alias(MemoryLocation(Call1Ptr), MemoryLocation(Call2Ptr));
	}

	if (AR == MustAlias) {
		auto Call1PtrSz = cast<ConstantInt>(Call1->getArgOperand(2))->getZExtValue();
		auto Call2PtrSz = cast<ConstantInt>(Call2->getArgOperand(2))->getZExtValue();
		if (Call1PtrSz >= Call2PtrSz) {
			errs() << "Replacing: " << *Call1 << " Size1:" << Call1PtrSz << "\n";
			errs() << "With: " << *Call2 << " Size2:" << Call2PtrSz << "\n";
			return true;
		}
	}
	return false;
}


static CallInst*
canReplace(DominatorTree &DT,
	CallInst *Call1, CallInst *Call2,
	AAResults *AA
	)
{
	if (DT.dominates(Call1, Call2)) {
		if (canReplaceHelper(Call1, Call2, AA)) {
			Call2->replaceAllUsesWith(Call1);
			return Call2;
		}
	}
	else if (DT.dominates(Call2, Call1)) {
		if (canReplaceHelper(Call2, Call1, AA)) {
			Call1->replaceAllUsesWith(Call2);
			return Call1;
		}
	}
	return NULL;
}

static bool
getGEPDiff(Function &F, Value *V1, Value *V2, BasicAAResult *BAR,
	DominatorTree *DT, AssumptionCache *AC, int64_t &Result, AAResults *AA)
{
  const DataLayout &DL = F.getParent()->getDataLayout();
	BasicAAResult::DecomposedGEP DecompGEP1, DecompGEP2;

	V1 = V1->stripPointerCasts();
	V2 = V2->stripPointerCasts();

	if (V1 == V2) {
		Result = 0;
		return true;
	}

	auto AR = AA->alias(MemoryLocation(V1), MemoryLocation(V2));
	if (AR == MustAlias) {
		Result = 0;
		return true;
	}

	if (!isa<GEPOperator>(V1) && !isa<GEPOperator>(V2)) {
		return false;
	}

	unsigned MaxPointerSize = DL.getMaxPointerSizeInBits();
  DecompGEP1.StructOffset = DecompGEP1.OtherOffset = APInt(MaxPointerSize, 0);
  DecompGEP2.StructOffset = DecompGEP2.OtherOffset = APInt(MaxPointerSize, 0);

 	bool GEP1MaxLookupReached =
    BAR->DecomposeGEPExpression(V1, DecompGEP1, DL, AC, DT);
  bool GEP2MaxLookupReached =
    BAR->DecomposeGEPExpression(V2, DecompGEP2, DL, AC, DT);

	if (GEP1MaxLookupReached || GEP2MaxLookupReached) {
		return false;
	}
	if (DecompGEP1.Base != DecompGEP2.Base) {
		return false;
	}

  APInt GEP1BaseOffset = DecompGEP1.StructOffset + DecompGEP1.OtherOffset;
  APInt GEP2BaseOffset = DecompGEP2.StructOffset + DecompGEP2.OtherOffset;

	GEP1BaseOffset -= GEP2BaseOffset;
	BAR->GetIndexDifference(DecompGEP1.VarIndices, DecompGEP2.VarIndices);
	if (DecompGEP1.VarIndices.empty()) {
		Result = GEP1BaseOffset.getSExtValue();
		return true;
	}
	return false;
}

static bool
removeCall2(CallInst *Call1, CallInst *Call2, int64_t Diff, PostDominatorTree &PDT, Value *Base, LoopInfo &LI)
{
	if (!isa<ConstantInt>(Call1->getArgOperand(3)) || !isa<ConstantInt>(Call2->getArgOperand(3))) {
		return false;
	}

	int64_t Call1TySz = cast<ConstantInt>(Call1->getArgOperand(3))->getZExtValue();
	int64_t Call2TySz = cast<ConstantInt>(Call2->getArgOperand(3))->getZExtValue();

	int64_t Call1Padding = cast<ConstantInt>(Call1->getArgOperand(4))->getSExtValue();
	int64_t Call2Padding = cast<ConstantInt>(Call2->getArgOperand(4))->getSExtValue();

	assert(Call1Padding <= 0);
	assert(Call2Padding <= 0);

	assert(Call1TySz > 0);
	assert(Call2TySz > 0);

	int64_t DiffLo = Diff + (Call1Padding - Call2Padding);
	int64_t DiffHi = Diff + (Call1TySz - Call2TySz);

	if (DiffLo > 0 || DiffHi < 0) {
		if (!PDT.dominates(Call2->getParent(), Call1->getParent())) {
			return false;
		}
		if (!inSameLoop1(Base, Call1, Call2, LI)) {
			return false;
		}
	}

	if (DiffLo > 0) {
		auto SizeTy = Call1->getArgOperand(4)->getType();
		int64_t NewPadding = Call1Padding - DiffLo;
		assert(NewPadding < (4<<20) && -NewPadding < (4<<20));
		Call1->setArgOperand(4, ConstantInt::get(SizeTy, NewPadding));
	}

	if (DiffHi < 0) {
		auto SizeTy = Call1->getArgOperand(3)->getType();
		int64_t NewSize = Call1TySz - DiffHi;
		assert(NewSize < (4<<20) && -NewSize < (4<<20));
		Call1->setArgOperand(3, ConstantInt::get(SizeTy, NewSize));
	}
	//errs() << "Call1: " << *Call1 << "\n";
	//errs() << "Call2: " << *Call2 << "\n";
	return true;
}

static void removeDuplicatesAborts(Function &F,
	DenseSet<CallInst*> &Aborts,
	DenseSet<CallInst*> &Abort2Calls,
	DenseSet<CallInst*> &Abort3Calls,
	AAResults *AA,
	AssumptionCache *AC,
	const TargetLibraryInfo *TLI
	)
{

	//errs() << "duplicate-aborts1: " << F << "\n";
	DominatorTree DT(F);
	LoopInfo LI(DT);
	PostDominatorTree PDT(F);
	DenseSet<CallInst*> ToDelete;
	int64_t Result;
  const DataLayout &DL = F.getParent()->getDataLayout();
  auto BAR = new BasicAAResult(DL, F, *TLI, *AC);

	for (auto itr1 = Aborts.begin(); itr1 != Aborts.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != Aborts.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			if (ToDelete.count(Call1) || ToDelete.count(Call2)) {
				continue;
			}
			auto Ptr1 = Call1->getArgOperand(1);
			auto Ptr2 = Call2->getArgOperand(1);

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);
			bool Ret;

			if (isa<BitCastInst>(Base1)) {
				errs() << F << "\n";
				errs() << "Base1:: " << *Base1 << "\n";
			}
			if (isa<BitCastInst>(Base2)) {
				errs() << F << "\n";
				errs() << "Base2:: " << *Base2 << "\n";
			}

			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));

			if (Base1 == Base2) {
				bool Found = getGEPDiff(F, Ptr1, Ptr2, BAR, &DT, AC, Result, AA);
				if (Found) {
					//bool Removed = false;


					if (DT.dominates(Call1->getParent(), Call2->getParent())) {
						Ret = removeCall2(Call1, Call2, Result, PDT, Base1, LI);
						if (Ret) {
							ToDelete.insert(Call2);
						}
						//Removed = true;
					}
					else if (DT.dominates(Call2->getParent(), Call1->getParent())) {
						Ret = removeCall2(Call2, Call1, -Result, PDT, Base1, LI);
						if (Ret) {
							ToDelete.insert(Call1);
						}
						//Removed = true;
					}
					/*if (Removed) {
						errs() << "Ptr1: " << *Ptr1 << "\n";
						errs() << "Ptr2: " << *Ptr2 << "\n";
						errs() << "DIFF is: " << Result << "\n";
						errs() << "Call1: " << *Call1 << "\n";
						errs() << "Call2: " << *Call2 << "\n";
					}*/
				}
			}
		}
	}

	for (auto Call : ToDelete) {
		if (Abort2Calls.count(Call)) {
			Abort2Calls.erase(Call);
		}
		else if (Abort3Calls.count(Call)) {
			Abort3Calls.erase(Call);
		}
		else {
			assert(0);
		}
		Aborts.erase(Call);
		Call->eraseFromParent();
	}
	//errs() << "Printing Function:\n" << F << "\n";
	//errs() << "duplicate-aborts2: " << F << "\n";
}


static void removeDuplicatesInterior(Function &F,
	DenseSet<CallInst*> &Interiors,
	DenseSet<CallInst*> &InteriorCalls,
	DenseSet<CallInst*> &CheckSizeOffset,
	AAResults *AA
	)
{
	DominatorTree DT(F);
	DenseSet<CallInst*> ToDelete;

	for (auto itr1 = Interiors.begin(); itr1 != Interiors.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != Interiors.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			if (ToDelete.count(Call1) || ToDelete.count(Call2)) {
				continue;
			}

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);
			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));

			if (Base1 == Base2) {
				auto Replaced = canReplace(DT, Call1, Call2, AA);
				if (Replaced) {
					ToDelete.insert(Replaced);
				}
			}
		}
	}

	for (auto Call : ToDelete) {
		if (InteriorCalls.count(Call)) {
			InteriorCalls.erase(Call);
		}
		else if (CheckSizeOffset.count(Call)) {
			CheckSizeOffset.erase(Call);
		}
		else {
			assert(0);
		}
		Interiors.erase(Call);
		Call->eraseFromParent();
	}
}

static CallInst *replaceLimit(Function &F, CallInst *Call)
{
	IRBuilder<> IRB(Call);
	auto Base = Call->getArgOperand(0);
	auto Int32Ty = IRB.getInt32Ty();
	auto Fn = F.getParent()->getOrInsertFunction("san_page_fault_limit",
		IRB.getInt8PtrTy(), Base->getType(), Int32Ty, Int32Ty);
	auto Zero = ConstantInt::get(Int32Ty, 0);
	auto NewCall = IRB.CreateCall(Fn, {Base, Zero, Zero});
	Call->replaceAllUsesWith(NewCall);
	return NewCall;
}

static void optimizeLimits(Function &F, DenseSet<CallInst*> &Limits, DenseSet<CallInst*> &LimitCalls)
{
	DominatorTree DT(F);
	LoopInfo LI(DT);
	PostDominatorTree PDT(F);
	DenseSet<CallInst*> ToDelete;
	DenseSet<CallInst*> Replaced;

	for (auto itr1 = Limits.begin(); itr1 != Limits.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != Limits.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			if (ToDelete.count(Call1) || ToDelete.count(Call2)) {
				continue;
			}

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);

			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));

			if (Base1 == Base2) {

				if (DT.dominates(Call1, Call2)) {
					Call2->replaceAllUsesWith(Call1);
					ToDelete.insert(Call2);
					if (!LimitCalls.count(Call1) && LimitCalls.count(Call2) && PDT.dominates(Call2, Call1)) {
						if (inSameLoop1(Base1, Call1, Call2, LI)) {
							LimitCalls.insert(Call1);
							Replaced.insert(Call1);
						}
					}
				}
				else if (DT.dominates(Call2, Call1)) {
					Call1->replaceAllUsesWith(Call2);
					ToDelete.insert(Call1);
					if (!LimitCalls.count(Call2) && LimitCalls.count(Call1) && PDT.dominates(Call1, Call2)) {
						if (inSameLoop1(Base1, Call2, Call1, LI)) {
							LimitCalls.insert(Call2);
							Replaced.insert(Call2);
						}
					}
				}

			}
		}
	}

	for (auto Call : ToDelete) {
		assert(Limits.count(Call));
		Limits.erase(Call);
		if (LimitCalls.count(Call)) {
			LimitCalls.erase(Call);
		}
		if (Replaced.count(Call)) {
			Replaced.erase(Call);
		}
		Call->eraseFromParent();
	}

	for (auto Call : Replaced) {
		CallInst *NewCall = replaceLimit(F, Call);
		assert(Limits.count(Call));
		assert(LimitCalls.count(Call));
		Limits.erase(Call);
		LimitCalls.erase(Call);
		Limits.insert(NewCall);
		LimitCalls.insert(NewCall);
		Call->eraseFromParent();
	}
}

static void assertLimits(Function &F, DenseSet<CallInst*> &Limits)
{
	DominatorTree DT(F);

	for (auto itr1 = Limits.begin(); itr1 != Limits.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != Limits.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);

			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));

			if (Base1 == Base2) {

				if (DT.dominates(Call1, Call2)) {
					assert(0);
				}
				else if (DT.dominates(Call2, Call1)) {
					assert(0);
				}

			}
		}
	}

}


static void removeDuplicatesSizeCalls(Function &F,
	DenseSet<CallInst*> &CheckSize)
{
	DominatorTree DT(F);
	DenseSet<CallInst*> ToDelete;

	for (auto itr1 = CheckSize.begin(); itr1 != CheckSize.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != CheckSize.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			if (ToDelete.count(Call1) || ToDelete.count(Call2)) {
				continue;
			}

			auto Ptr1 = Call1->getArgOperand(0);
			auto Ptr2 = Call2->getArgOperand(0);

			assert(!isa<BitCastInst>(Ptr1));
			assert(!isa<BitCastInst>(Ptr2));

			if (Ptr1 == Ptr2) {

				if (DT.dominates(Call1, Call2)) {
					auto Size1 = cast<ConstantInt>(Call1->getArgOperand(1))->getZExtValue();
					auto Size2 = cast<ConstantInt>(Call2->getArgOperand(1))->getZExtValue();
					if (Size1 >= Size2) {
						errs() << "Relplacing Size: " << *Call2 << "  SIZE: " << Size2 << "\n";
						errs() << "With: " << *Call1 << " SIZE: " << Size1 << "\n";
						Call2->replaceAllUsesWith(Call1);
						ToDelete.insert(Call2);
					}
				}
				else if (DT.dominates(Call2, Call1)) {
					auto Size1 = cast<ConstantInt>(Call1->getArgOperand(1))->getZExtValue();
					auto Size2 = cast<ConstantInt>(Call2->getArgOperand(1))->getZExtValue();
					if (Size2 >= Size1) {
						errs() << "Relplacing Size: " << *Call1 << "  SIZE: " << Size1 << "\n";
						errs() << "With: " << *Call2 << " SIZE: " << Size2 << "\n";
						Call1->replaceAllUsesWith(Call2);
						ToDelete.insert(Call1);
					}
				}

			}
		}
	}

	for (auto Call : ToDelete) {
		assert(CheckSize.count(Call));
		CheckSize.erase(Call);
		Call->eraseFromParent();
	}
}

static CallInst* ReplaceInterior(Function &F, CallInst *Call)
{
	IRBuilder<> IRB(Call);
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int64Ty = IRB.getInt64Ty();
	auto Base = Call->getArgOperand(0);
	auto Ptr = Call->getArgOperand(1);
	auto TySize = Call->getArgOperand(2);
	auto Fn = F.getParent()->getOrInsertFunction("san_interior",
		Call->getType(), Base->getType(), Ptr->getType(), TySize->getType(), Int64Ty, Int8PtrTy);
	auto Ret = IRB.CreateCall(Fn, {Base, Ptr, TySize, ConstantInt::get(Int64Ty, 0), Constant::getNullValue(Int8PtrTy)});
	Call->replaceAllUsesWith(Ret);
	errs() << "Replacing Interior -- \n";
	errs() << "Orig: " << *Call << "\n";
	errs() << "New: " << *Ret << "\n";
	return Ret;
}

static void addLimitToInterior(Function &F,
	DenseSet<CallInst*> &InteriorCalls,
	DenseSet<CallInst*> &Limits,
	DenseMap<Value*, Value*> &BaseToLenMap
	)
{
	DominatorTree DT(F);
	bool Found;

	for (auto itr1 = InteriorCalls.begin(); itr1 != InteriorCalls.end(); itr1++) {
		Found = false;
		auto *Call1 = dyn_cast<CallInst>(*itr1);
		auto Base1 = Call1->getArgOperand(0);
		for (auto itr2 = Limits.begin(); itr2 != Limits.end(); itr2++) {

      auto *Call2 = dyn_cast<CallInst>(*itr2);

			auto Base2 = Call2->getArgOperand(0);
			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));
			if (Base1 == Base2) {
				if (DT.dominates(Call2->getParent(), Call1->getParent())) {
					if (!DT.dominates(Call2, Call1)) {
						Call2->removeFromParent();
						Call2->insertBefore(Call1);
					}
					auto Limit = Call1->getArgOperand(4);
					assert(cast<Constant>(Limit)->isNullValue());
					Call1->setArgOperand(4, Call2);
					Found = true;
					break;
				}
			}
		}
		if (!Found) {
			if (!BaseToLenMap.count(Base1)) {
				errs() << "No Prior length: " << *Call1 << "\n";
				errs() << F << "\n";
				assert(BaseToLenMap.count(Base1));
			}
			auto Lim = BaseToLenMap[Base1];
			if (!Lim->getType()->isIntegerTy()) {
				errs() << "Base1:" << *Base1 << "\n";
				errs() << F << "\n";
				errs() << "Lim:" << *Lim << "\n";
				assert(0);
			}
		}
	}
}


static void optimizeInteriorCalls(Function &F,
	DenseSet<CallInst*> &Interiors,
	DenseSet<CallInst*> &InteriorCalls,
	DenseSet<CallInst*> &CheckSizeOffset,
	DenseSet<CallInst*> &Aborts,
	AssumptionCache *AC,
	AAResults *AA,
	const TargetLibraryInfo *TLI
	)
{
	DominatorTree DT(F);
	DenseSet<CallInst*> ToReplace;

	int64_t Result;
  const DataLayout &DL = F.getParent()->getDataLayout();
  auto BAR = new BasicAAResult(DL, F, *TLI, *AC);



	for (auto itr1 = CheckSizeOffset.begin(); itr1 != CheckSizeOffset.end(); itr1++) {
		for (auto itr2 = Aborts.begin(); itr2 != Aborts.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);
			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));

			if (Base1 == Base2) {

				auto Ptr1 = Call1->getArgOperand(1);
				auto Ptr2 = Call2->getArgOperand(1);


				if (DT.dominates(Call2->getParent(), Call1->getParent())) {
					bool HasDiff = getGEPDiff(F, Ptr2, Ptr1, BAR, &DT, AC, Result, AA);
					if (HasDiff && isa<ConstantInt>(Call2->getArgOperand(3))) {
						int64_t Ptr1Sz = cast<ConstantInt>(Call1->getArgOperand(2))->getZExtValue();
						int64_t Ptr2Sz = cast<ConstantInt>(Call2->getArgOperand(3))->getZExtValue();
						assert(Ptr1Sz > 0 && Ptr2Sz > 0);

						int64_t LowDiff = Result;
						int64_t HiDiff = LowDiff + Ptr2Sz - Ptr1Sz;
						if (LowDiff >= 0 && HiDiff >= 0) {
							ToReplace.insert(Call1);
							break;
						}
					}
				}

			}
		}
	}

	for (auto Call : ToReplace) {
		auto NewCall = ReplaceInterior(F, Call);
		assert(CheckSizeOffset.count(Call));
		CheckSizeOffset.erase(Call);
		assert(Interiors.count(Call));
		Interiors.erase(Call);
		InteriorCalls.insert(NewCall);
		Interiors.insert(NewCall);
		Call->eraseFromParent();
	}
}

static void optimizeSizeCalls(Function &F,
	DenseSet<CallInst*> &CheckSize,
	DenseSet<CallInst*> &Aborts,
	AssumptionCache *AC,
	AAResults *AA,
	const TargetLibraryInfo *TLI
	)
{
	DominatorTree DT(F);
	DenseSet<CallInst*> ToDelete;

	int64_t Result;
  const DataLayout &DL = F.getParent()->getDataLayout();
  auto BAR = new BasicAAResult(DL, F, *TLI, *AC);



	for (auto itr1 = CheckSize.begin(); itr1 != CheckSize.end(); itr1++) {
		for (auto itr2 = Aborts.begin(); itr2 != Aborts.end(); itr2++) {

			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);

			assert(!isa<BitCastInst>(Base1));
			assert(!isa<BitCastInst>(Base2));

			if (Base1 == Base2) {

				auto Ptr1 = Base1;
				auto Ptr2 = Call2->getArgOperand(1);


				if (DT.dominates(Call2->getParent(), Call1->getParent())) {
					bool HasDiff = getGEPDiff(F, Ptr2, Ptr1, BAR, &DT, AC, Result, AA);
					if (HasDiff && isa<ConstantInt>(Call2->getArgOperand(3))) {
						int64_t Ptr1Sz = cast<ConstantInt>(Call1->getArgOperand(1))->getZExtValue();
						int64_t Ptr2Sz = cast<ConstantInt>(Call2->getArgOperand(3))->getZExtValue();
						assert(Ptr1Sz > 0 && Ptr2Sz > 0);

						int64_t LowDiff = Result;
						int64_t HiDiff = LowDiff + Ptr2Sz - Ptr1Sz;
						if (LowDiff >= 0 && HiDiff >= 0) {
							ToDelete.insert(Call1);
							break;
						}
					}
				}

			}
		}
	}

	for (auto Call : ToDelete) {
		IRBuilder<> IRB(Call);
		auto Base = Call->getArgOperand(0);
		auto Ret = IRB.CreateBitCast(Base, Call->getType());
		Call->replaceAllUsesWith(Ret);
		assert(CheckSize.count(Call));
		CheckSize.erase(Call);
		Call->eraseFromParent();
	}
}

static Instruction*
inlineLimit(Function &F, CallInst *Call)
{
	IRBuilder<> IRB(Call);
	auto Base = Call->getArgOperand(0);
	//auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();
	auto Int64Ty = IRB.getInt64Ty();
	//auto Int32Ty = IRB.getInt32Ty();
	//auto Int32PtrTy = Int32Ty->getPointerTo();

	auto BaseInt = IRB.CreatePtrToInt(Base, Int64Ty);
	auto Offset = IRB.CreateLShr(BaseInt, 49);

  auto SlowPath = IRB.CreateICmp(ICmpInst::ICMP_UGE, Offset, ConstantInt::get(Int64Ty, ((1ULL<<15)-1)));
	Instruction *IfTerm, *ElseTerm, *EndElse;
	EndElse = Call->getNextNode();

  SplitBlockAndInsertIfThenElse(SlowPath, Call, &IfTerm, &ElseTerm);
	IRB.SetInsertPoint(IfTerm);

	Call->removeFromParent();
  Call->insertBefore(IfTerm);

	IRB.SetInsertPoint(ElseTerm);

	auto NewBase = IRB.CreateAnd(BaseInt, ConstantInt::get(Int64Ty, (0x1ULL<<49)-1));
	NewBase = IRB.CreateSub(NewBase, Offset);
	NewBase = IRB.CreateIntToPtr(NewBase, Int8PtrTy);

	IRB.SetInsertPoint(EndElse);

  PHINode *PHI = IRB.CreatePHI(Int8PtrTy, 2);

  BasicBlock *IfBlock = IfTerm->getParent();
  BasicBlock *ElseBlock = ElseTerm->getParent();
  PHI->addIncoming(NewBase, ElseBlock);
  PHI->addIncoming(Call, IfBlock);
	return PHI;
}

static void
transformLimit(Function &F, CallInst *Lim, bool MayNull, DenseMap<Value*, Value*> &LimitToRealBase)
{
	Instruction *InsertPt = Lim->getNextNode();
	IRBuilder<> IRB(InsertPt);
	auto Int32Ty = IRB.getInt32Ty();
	auto Int32PtrTy = Int32Ty->getPointerTo();
	auto Int8Ty = IRB.getInt8Ty();
	auto Int8PtrTy = IRB.getInt8PtrTy();
	//auto Base = Lim->getArgOperand(0);
	Value *Size;
	//MDNode *N;

	auto Lim32 = IRB.CreateBitCast(Lim, Int32PtrTy);

	if (!MayNull) {
		auto LimAddr = IRB.CreateGEP(Int32Ty, Lim32, ConstantInt::get(Int32Ty, -1));
		Size = IRB.CreateLoad(LimAddr);

		//N = MDNode::get(Size->getContext(), {});
		//cast<Instruction>(Size)->setMetadata("fasansize", N);

		auto Base8 = IRB.CreateBitCast(Lim32, Int8PtrTy);
		auto Limit = IRB.CreateGEP(Int8Ty, Base8, Size);
		Lim->replaceAllUsesWith(Limit);
		cast<Instruction>(Lim32)->setOperand(0, Lim);
		LimitToRealBase[Limit] = Lim;
		//auto PHI = inlineLimit(F, Lim);
		//cast<Instruction>(Lim32)->setOperand(0, PHI);
		//LimitToRealBase[Limit] = PHI;
		//errs() << "ADDING: " << *Limit << "  LIM: " << *Lim << "\n"; 

		return;
	}

	auto Cmp = IRB.CreateICmpNE(Lim32, Constant::getNullValue(Int32PtrTy));
	Instruction *IfTerm = SplitBlockAndInsertIfThen(Cmp, InsertPt, false);
	IRB.SetInsertPoint(IfTerm);
	auto LimAddr = IRB.CreateGEP(Int32Ty, Lim32, ConstantInt::get(Int32Ty, -1));
	Size = IRB.CreateLoad(LimAddr);
	//N = MDNode::get(Size->getContext(), {});
	//cast<Instruction>(Size)->setMetadata("fasansize", N);
	IRB.SetInsertPoint(InsertPt);
  PHINode *PHI = IRB.CreatePHI(Int32Ty, 2);
  BasicBlock *CondBlock = cast<Instruction>(Cmp)->getParent();
  PHI->addIncoming(ConstantInt::get(Int32Ty, 0), CondBlock);
  BasicBlock *ThenBlock = IfTerm->getParent();
  PHI->addIncoming(Size, ThenBlock);

	auto Base8 = IRB.CreateBitCast(Lim32, Int8PtrTy);
	auto Limit = IRB.CreateGEP(Int8Ty, Base8, PHI);
	Lim->replaceAllUsesWith(Limit);
	cast<Instruction>(Lim32)->setOperand(0, Lim);
	LimitToRealBase[Limit] = Lim;
	//errs() << "ADDING: " << *Limit << "  LIM: " << *Lim << "\n"; 
}

static void
optimizePtrMask(Function &F, AAResults *AA)
{
	DenseSet<IntrinsicInst*> IntrinSet;
  for (auto &BB : F) {
    for (auto &Inst : BB) {
			auto Intrin = dyn_cast<IntrinsicInst>(&Inst);
			if (Intrin && Intrin->getIntrinsicID() == Intrinsic::ptrmask) {
				IntrinSet.insert(Intrin);
			}
		}
	}

	DominatorTree DT(F);
	DenseSet<CallInst*> ToDelete;

	for (auto itr1 = IntrinSet.begin(); itr1 != IntrinSet.end(); itr1++) {
		for (auto itr2 = std::next(itr1); itr2 != IntrinSet.end(); itr2++) {
			auto *Call1 = dyn_cast<CallInst>(*itr1);
      auto *Call2 = dyn_cast<CallInst>(*itr2);

			if (ToDelete.count(Call1) || ToDelete.count(Call2)) {
				continue;
			}

			auto Base1 = Call1->getArgOperand(0);
			auto Base2 = Call2->getArgOperand(0);

			auto Mask1 = cast<ConstantInt>(Call1->getArgOperand(1))->getZExtValue();
			auto Mask2 = cast<ConstantInt>(Call2->getArgOperand(1))->getZExtValue();

			if (Mask1 != Mask2) {
				continue;
			}

			auto AR = AA->alias(MemoryLocation(Base1), MemoryLocation(Base2));
			Value *Replacement;

			if (AR == MustAlias) {

				if (DT.dominates(Call1, Call2)) {
					ToDelete.insert(Call2);
					if (Call1->getType() != Call2->getType()) {
						IRBuilder<> IRB(Call1->getNextNode());
						Replacement = IRB.CreateBitCast(Call1, Call2->getType());
					}
					else {
						Replacement = Call1;
					}
					Call2->replaceAllUsesWith(Replacement);
				}
				else if (DT.dominates(Call2, Call1)) {
					ToDelete.insert(Call1);
					if (Call1->getType() != Call2->getType()) {
						IRBuilder<> IRB(Call2->getNextNode());
						Replacement = IRB.CreateBitCast(Call2, Call1->getType());
					}
					else {
						Replacement = Call2;
					}
					Call1->replaceAllUsesWith(Replacement);
				}

			}
		}
	}

	for (auto Call : ToDelete) {
		Call->eraseFromParent();
	}
}



static void optimizeHandlers(Function &F,
	std::map<Value*, std::pair<const Value*, int64_t>> &UnsafeMap, AAResults *AA,
	AssumptionCache *AC, const TargetLibraryInfo *TLI,
	DenseMap<Value*, Value*> &BaseToLenMap)
{
	DenseSet<CallInst*> Limits;
	DenseSet<CallInst*> LimitsMayNull;
	DenseSet<CallInst*> LimitChecked;
	DenseSet<CallInst*> LimitCalls;
	DenseSet<CallInst*> InteriorCalls;
	DenseSet<CallInst*> CheckSize;
	DenseSet<CallInst*> CheckSizeOffset;
	DenseSet<CallInst*> Interiors;
	DenseSet<CallInst*> Abort2Calls;
	DenseSet<CallInst*> Abort3Calls;
	DenseSet<CallInst*> Aborts;

	for (auto &BB : F) {
		for (auto &II : BB) {
			auto CI = dyn_cast<CallInst>(&II);
			if (CI) {
				auto Target = CI->getCalledValue()->stripPointerCasts();
				if (Target) {
					auto Name = Target->getName();
					if (Name  == "san_page_fault_limit") {
						LimitCalls.insert(CI);
						Limits.insert(CI);
					}
					else if (Name == "san_interior") {
						InteriorCalls.insert(CI);
						Interiors.insert(CI);
					}
					else if (Name == "san_check_size_limit") {
						CheckSize.insert(CI);
					}
					else if (Name == "san_interior_limit") {
						CheckSizeOffset.insert(CI);
						Interiors.insert(CI);
					}
					else if (Name == "san_abort2") {
						Abort2Calls.insert(CI);
						Aborts.insert(CI);
					}
					else if (Name == "san_abort3") {
						Abort3Calls.insert(CI);
						Aborts.insert(CI);
					}
					else if (Name == "san_get_limit") {
						Limits.insert(CI);
					}
					else if (Name == "san_get_limit_must_check") {
						Limits.insert(CI);
						LimitsMayNull.insert(CI);
					}
					else if (Name == "san_get_limit_check") {
						Limits.insert(CI);
						LimitsMayNull.insert(CI);
						LimitChecked.insert(CI);
					}

				}
			}
		}
	}


	removeDuplicatesAborts(F, Aborts, Abort2Calls, Abort3Calls, AA, AC, TLI);
	removeDuplicatesInterior(F, Interiors, InteriorCalls, CheckSizeOffset, AA);
	optimizeInteriorCalls(F, Interiors, InteriorCalls, CheckSizeOffset, Aborts, AC, AA, TLI);
	optimizeSizeCalls(F, CheckSize, Aborts, AC, AA, TLI);
	// FIXME: remove only if same size
	removeDuplicatesSizeCalls(F, CheckSize);
	optimizeLimits(F, Limits, LimitCalls);

	assertLimits(F, Limits);



	DominatorTree DT(F);
	PostDominatorTree PDT(F);
	LoopInfo LI(DT);
	TargetLibraryInfo *_TLI = const_cast<TargetLibraryInfo*>(TLI);
	ScalarEvolution SE(F, *_TLI, *AC, DT, LI);

	for (auto LC : Abort2Calls) {
		while (optimizeAbortLoopHeader(F, LC, &DT, &LI, PDT, SE)) {
		}
	}

	for (auto LC : Abort3Calls) {
		while (optimizeAbortLoopHeader(F, LC, &DT, &LI, PDT, SE)) {
		}
	}

	for (auto Lim : Limits) {
		while (optimizeLimitLoopHeader(F, Lim, &DT, &LI, PDT)) {
		}
	}

	//errs() << "Before: " << F << "\n";
	if (!Abort2Calls.empty() || !Abort3Calls.empty()) {
		//BasicBlock *TrapBB = getTrapBB(&F);

		for (auto LC : Abort2Calls) {
			optimizeAbortLoop(F, LC, &DT, &LI/*, SE*/);
		}

		for (auto LC : Abort3Calls) {
			optimizeAbortLoop(F, LC, &DT, &LI/*, SE*/);
		}

	}
	//errs() << "After: " << F << "\n";

	for (auto Lim : LimitCalls) {
		auto NewLim = optimizeLimit(F, Lim, false);
		assert(Limits.count(Lim));
		Limits.erase(Lim);
		Limits.insert(NewLim);
	}

	for (auto Lim : LimitChecked) {
		if (Limits.count(Lim)) {
			auto NewLim = optimizeLimit(F, Lim, true);
			Limits.erase(Lim);
			Limits.insert(NewLim);
			assert(LimitsMayNull.count(Lim));
			LimitsMayNull.erase(Lim);
			LimitsMayNull.insert(NewLim);
		}
	}

	addLimitToInterior(F, InteriorCalls, Limits, BaseToLenMap);

	
	DenseMap<Value*, Value*> LimitToRealBase;

	for (auto Lim : Limits) {
		if (!LimitsMayNull.count(Lim)) {
			transformLimit(F, Lim, false, LimitToRealBase);
		}
		else {
			transformLimit(F, Lim, true, LimitToRealBase);
		}
	}

	DenseSet<CallInst*> FBounds;
	DenseSet<CallInst*> FInteriors;
	DenseSet<CallInst*> FCheckInteriors;
	DenseSet<CallInst*> FCheckSizes;

	for (auto LC : Abort2Calls) {
		auto FBound = optimizeAbort(F, LC, true, NULL, LimitToRealBase);
		FBounds.insert(FBound);
	}

	for (auto LC : Abort3Calls) {
		auto FBound = optimizeAbort(F, LC, false, NULL, LimitToRealBase);
		FBounds.insert(FBound);
	}

	for (auto LC : InteriorCalls) {
		auto Interior = optimizeInterior(F, LC, LimitToRealBase);
		FInteriors.insert(Interior);
	}
	for (auto LC : CheckSize) {
		auto CI = optimizeCheckSize(F, LC, LimitToRealBase);
		FCheckSizes.insert(CI);
	}
	for (auto LC : CheckSizeOffset) {
		auto Interior = optimizeCheckSizeOffset(F, LC, LimitToRealBase);
		FCheckInteriors.insert(Interior);
	}

	for (auto Lim : Limits) {
		optimizeLimitLoop(F, Lim, &DT, &LI);
	}


	for (auto Lim : Limits) {
		if (!LimitsMayNull.count(Lim)) {
			optimizeFLimit(F, Lim, &DT, &LI);
		}
	}

	if (verifyFunction(F, &errs())) {
    F.dump();
    report_fatal_error("verification of newFunction failed11!");
  }

	optimizePtrMask(F, AA);

	if (!FBounds.empty()) {
		BasicBlock *TrapBB = getTrapBB(&F);
		for (auto FBound : FBounds) {
			optimizeFBound(F, FBound, TrapBB);
		}
	}

	for (auto Interior : FInteriors) {
		optimizeFInterior(F, Interior, AA);
		
	}
	for (auto Interior : FCheckInteriors) {
		optimizeFInteriorCheck(F, Interior, AA);
	}

	for (auto CI : FCheckSizes) {
		optimizeFCheckSize(F, CI);
	}
}

static void
simplifyAll(Function &F, const TargetLibraryInfo *TLI, AssumptionCache *AC)
{
	DominatorTree DT(F);
	LoopInfo LI(DT);
	TargetLibraryInfo *_TLI = const_cast<TargetLibraryInfo*>(TLI);
	ScalarEvolution SE(F, *_TLI, *AC, DT, LI);
	
	for (auto &L : LI) {
    simplifyLoop(L, &DT, &LI, &SE, AC, nullptr, false /* PreserveLCSSA */);
		//formLCSSARecursively(*L, DT, &LI, &SE);
	}
}

void
FastAddressSanitizer::insertChecksForMemCalls(Function &F,
	DenseMap<Value*, Value*> &PtrToBaseMap,
	DenseMap<Value*, Value*> &BaseToLenMap,
	DenseMap<Value*, Value*> &LenToBaseMap,
	DenseMap<Value*, Value*> &PtrUseToLenMap,
	DenseSet<Value*> &GetLengths,
	CallInst *CI, Value *Ptr, Value *Len,
	const TargetLibraryInfo *TLI, bool After)
{
	if (isa<Constant>(Ptr) && cast<Constant>(Ptr)->isNullValue()) {
		return;
	}

	//auto Int32Ty = Type::getInt32Ty(F.getParent()->getContext());


	Value *Base;
	if (isa<ConstantExpr>(Ptr)) {
		Base = cast<ConstantExpr>(Ptr)->getOperand(0);
		if (!isa<GlobalVariable>(Base)) {
			return;
		}
	}
	else {
		assert(PtrToBaseMap.count(Ptr));
		Base = PtrToBaseMap[Ptr];
	}

	//errs() << "Base:: " << *Base << "\n";
	//errs() << "Ptr:: " << *Ptr << "\n";
	//errs() << "CI:: " << *CI << "\n";

	if (isa<ConstantInt>(Len)) {
		int64_t PtrLen = cast<ConstantInt>(Len)->getZExtValue();
		int64_t Offset = 0;
  	const DataLayout &DL = F.getParent()->getDataLayout();
		Value *OtherBase = GetPointerBaseWithConstantOffset(Ptr, Offset, DL);
		if (Base == OtherBase && Offset >= 0) {
			PtrLen += Offset;
			bool Static = false;
			int64_t BaseSize = getKnownObjSize(Base, DL, Static, TLI);
			assert(!Static || PtrLen <= BaseSize);
			if (PtrLen <= BaseSize) {
				return;
			}
		}
	}

	if (!Len->getType()->isIntegerTy()) {
		errs() << "Len:: " << *Len << "\n";
		assert(0);
	}

	if (!BaseToLenMap.count(Base)) {
		const DataLayout &DL = F.getParent()->getDataLayout();
		auto Size = getStaticBaseSize(F, Base, DL, TLI);
		if (Size) {
			BaseToLenMap[Base] = Size;
		}
	}

	auto InsertPt = (After) ? CI->getNextNode() : CI;

	if (BaseToLenMap.count(Base)) {
		auto Limit = BaseToLenMap[Base];
		abortIfTrue(F, InsertPt, Base, Ptr, Limit, Len, ConstantInt::get(Int32Ty, 0));
	}
	else {
		assert(!PtrUseToLenMap.count(CI));
		auto Limit = addLengthAtPtrUseHelper(F, Base, PtrUseToLenMap, GetLengths, LenToBaseMap, CI);
		PtrUseToLenMap.erase(CI);
		abortIfTrue(F, InsertPt, Base, Ptr, Limit, Len, ConstantInt::get(Int32Ty, 0));
	}
}


static void initializeAllocasAndMalloc(Function &F, const TargetLibraryInfo *TLI)
{
	DenseSet<std::pair<Instruction*, Value*>> AllocSet;
  const DataLayout &DL = F.getParent()->getDataLayout();
	auto M = F.getParent();
	auto Int64Ty = Type::getInt64Ty(M->getContext());

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			auto AI = dyn_cast<AllocaInst>(&Inst);
			if (AI) {
				if (AI->isStaticAlloca()) {
					uint64_t Size = getAllocaSizeInBytes1(*AI);
					AllocSet.insert(std::make_pair(AI, ConstantInt::get(Int64Ty, Size)));
				}
				else {
  				Value *Size = getAllocaSize(AI);
					AllocSet.insert(std::make_pair(AI, Size));
				}
			}
			else if (auto CI = dyn_cast<CallInst>(&Inst)) {
				LibFunc Func;
				if (TLI->getLibFunc(ImmutableCallSite(CI), Func)) {
					auto Name = CI->getCalledFunction()->getName();
					if (Name == "malloc") {
						AllocSet.insert(std::make_pair(CI, CI->getArgOperand(0)));
					}
				}
			}
		}
	}

	for (auto Pair : AllocSet) {
		Instruction *I = Pair.first;
		auto Size = Pair.second;
		SmallVector<LLT, 8> ValueVTs;
    SmallVector<uint64_t, 8> Offsets;
		Type *PTy = NULL;

		if (isa<AllocaInst>(I)) {
			PTy = I->getType()->getPointerElementType();
		}
		else {
			for (const Use &UI : I->uses()) {
	  		auto I = cast<Instruction>(UI.getUser());
				if (isa<BitCastInst>(I)) {
					PTy = I->getType()->getPointerElementType();
					break;
				}
			}
		}
		if (PTy == NULL) {
			return;
		}

		auto Int64PtrTy = Type::getInt64PtrTy(F.getParent()->getContext());
		int NumberOfPtrs = 0, NumberOfBits = 0;
		unsigned long long BitIdx = 0;
		unsigned long long BitMap = 0;
		auto TySize = DL.getTypeAllocSize(PTy);

    computeValueLLTs(DL, *PTy, ValueVTs, &Offsets);

    for (unsigned i = 0; i < ValueVTs.size(); i++)
    {
			assert(Offsets[i] < TySize * 8);
      if (ValueVTs[i].isPointer())
      {
				NumberOfPtrs++;
				BitIdx = (Offsets[i] / 64) % 64;
				if (!((BitMap >> BitIdx) & 1)) {
					NumberOfBits++;
				}
				BitMap |= (1ULL << BitIdx);
      }
    }

		if (NumberOfPtrs) {
			IRBuilder<> IRB(I->getNextNode());

			auto StaticSize = (isa<ConstantInt>(Size)) ? cast<ConstantInt>(Size)->getZExtValue() : 0;
			if (StaticSize == TySize && TySize <= 512) {
				if (NumberOfPtrs <= 8) {
					auto Ptr8 = IRB.CreateBitCast(I, IRB.getInt8PtrTy());
					for (unsigned i = 0; i < 64 && NumberOfPtrs; i++) {
						if ((BitMap >> i) & 1) {
							NumberOfPtrs--;
							size_t offset = (i * 8);
							auto GEP = IRB.CreateGEP(Ptr8, ConstantInt::get(IRB.getInt64Ty(), offset));
							IRB.CreateStore(ConstantInt::getNullValue(Int64Ty), IRB.CreateBitCast(GEP, Int64PtrTy));
						}
					}
				}
				else {
					unsigned i;
					for (i = 63; i > 0; i--) {
						if ((BitMap >> i) & 1) {
							break;
						}
					}
					assert(i > 0);
					size_t TotalSize = (i+1)*8;
					size_t PtrSize = NumberOfPtrs * 8;
					assert(TotalSize <= TySize);
					if (TotalSize < PtrSize * 2) {
						auto Ptr8 = IRB.CreateBitCast(I, IRB.getInt8PtrTy());
						IRB.CreateMemSet(Ptr8, ConstantInt::get(IRB.getInt8Ty(), 0), 
							ConstantInt::get(Int64Ty, TotalSize), Align::None());
					}
					else {
						auto Fn = M->getOrInsertFunction("san_typeset",
							IRB.getVoidTy(), I->getType(), Size->getType(), Int64Ty, Int64Ty);
						IRB.CreateCall(Fn, {I, Size, ConstantInt::get(Int64Ty, TySize), 
							ConstantInt::get(Int64Ty, BitMap)});
					}
				}
			}
			else {
				if (((NumberOfPtrs * 80) >= ((int)TySize * 7)) || NumberOfBits >= 48) {
					auto Ptr8 = IRB.CreateBitCast(I, IRB.getInt8PtrTy());
					IRB.CreateMemSet(Ptr8, ConstantInt::get(IRB.getInt8Ty(), 0), Size, Align::None());
				}
				else {
					auto Fn = M->getOrInsertFunction("san_typeset",
						IRB.getVoidTy(), I->getType(), Size->getType(), Int64Ty, Int64Ty);
					IRB.CreateCall(Fn, {I, Size, ConstantInt::get(Int64Ty, TySize), 
						ConstantInt::get(Int64Ty, BitMap)});
				}
			}
		}
	}

}

static bool checkIfRegisterationIsRequired(DenseSet<AllocaInst*> &UnsafeAllocas, const TargetLibraryInfo *TLI)
{
	for (auto AI : UnsafeAllocas) {
		if (!isAllocaCallSafe(AI, TLI)) {
			return true;
		}
	}
	errs() << "Save Enter\n";
	return false;
}

bool FastAddressSanitizer::instrumentFunctionNew(Function &F,
                                                 const TargetLibraryInfo *TLI,
																								 AAResults *AA,
																								 AssumptionCache *AC) {
	simplifyAll(F, TLI, AC);
	//FIXME: only if used in phi
	//copyArgsByValToAllocas1(F);
	//errs() << "Printing function\n" << F << "\n";
	//createInteriorFn(&F);

	DenseSet<Value*> UnsafeUses;
	DenseMap<Value*, uint64_t> UnsafePointers;
  const DataLayout &DL = F.getParent()->getDataLayout();
	std::map<Value*, std::pair<const Value*, int64_t>> UnsafeMap;
	DenseMap<Value*, Value*> BaseToLenMap;
	DenseMap<Value*, Value*> LenToBaseMap;
	DenseSet<Value*> TmpSet;
	DenseSet<CallBase*> CallSites;
	DenseSet<ReturnInst*> RetSites;
	DenseSet<StoreInst*> Stores;
	DenseSet<Instruction*> FnPtrs;
	DenseSet<AllocaInst*> UnsafeAllocas;
	DenseSet<Value*> InteriorPointers;
	int callsites = 0;
	DenseMap<Value*, Value*> ReplacementMap;
	DenseMap<Value*, Value*> PtrToBaseMap;
	DenseSet<Value*> GetLengths;
	DenseSet<Value*> GetLengthsCond;
	DenseSet<Instruction*> ICmpOrSub;
	DenseSet<Instruction*> IntToPtr;
	DenseSet<Instruction*> PtrToInt;
	DenseSet<Instruction*> GEPs;
	DenseSet<Value*> PtrMayBeNull;
	DenseSet<Instruction*> RestorePoints;
	DenseSet<Value*> SafePtrs;

	DenseSet<Value*> InteriorPointersSet;
	DenseSet<Value*> LargerThanBase;
	DenseSet<CallInst*> MemCalls;
	bool HasIndefiniteBase = false;

	createReplacementMap(&F, ReplacementMap);

	enableMasking(F);
	//setBoundsForArgv(F);

  if (!ClDebugFunc.empty() && F.getName().startswith(ClDebugFunc)) {
		errs() << "Before San\n" << F << "\n";
	}

	recordAllUnsafeAccesses(F, UnsafeUses, UnsafePointers, CallSites,
		RetSites, Stores, UnsafeAllocas, ICmpOrSub, IntToPtr, PtrToInt, RestorePoints, 
		InteriorPointersSet, GEPs, LargerThanBase, MemCalls, FnPtrs, TLI);

	//if (UnsafePointers.empty()) {
	//	return true;
	//}

	DominatorTree DT(F);
	//LoopInfo LI(DT);

	findAllBaseAndOffsets(F, UnsafePointers, UnsafeMap, PtrToBaseMap, TmpSet, DT, ReplacementMap, TLI, InteriorPointersSet, LargerThanBase);
	removeRedundentAccesses(F, UnsafeMap, TmpSet, DT, AA);


	DenseSet<Value*> PhiAndSelectNodes;
	DenseMap<Value*, Value*> PhiAndSelectMap;

	for (auto It : PtrToBaseMap) {
		Value *Base = It.second;
		if (isa<PHINode>(Base) || isa<SelectInst>(Base)) {
			if (!PhiAndSelectNodes.count(Base)) {
				PhiAndSelectNodes.insert(Base);
			}
		}
	}

	findPhiAndSelectBases(F, PhiAndSelectNodes, PhiAndSelectMap, ReplacementMap);

	DenseMap<Value*, Value*> PhiOrSelBaseToOrig;

	DenseSet<std::pair<Value*, Value*>> NewAllocas;

	for (auto It : PtrToBaseMap) {
		Value *Base = It.second;
		if (isa<PHINode>(Base) || isa<SelectInst>(Base)) {
			assert(PhiAndSelectMap.count(Base));
			PtrToBaseMap[It.first] = PhiAndSelectMap[Base];
			PhiOrSelBaseToOrig[PhiAndSelectMap[Base]] = Base;
			addUnsafeAllocas(F, PhiAndSelectMap[Base], UnsafeAllocas, NewAllocas);
			//errs() << "SRC: " << *It.first << "  BASE: " << *PhiAndSelectMap[Base] << "\n";
		}
	}

	for (auto Itr : NewAllocas) {
		auto AI = Itr.first;
		auto ByVal = Itr.second;
		PtrToBaseMap[AI] = AI;
		for (auto It : PtrToBaseMap) {
			Value *Base = It.second;
			if (Base == ByVal) {
				PtrToBaseMap[It.first] = AI;
			}
		}
	}

	//removeOnlyNonAccessPtrs(F, TmpSet, UnsafeUses);


	DT.recalculate(F);

	LoopInfo LI(DT);
	PostDominatorTree PDT(F);


	DenseMap<Value*, DenseSet<Value*>> BaseToPtrsMap;

	for (auto Ptr : TmpSet) {

		bool MayNull = false;
		auto PtrI = dyn_cast<Instruction>(Ptr);
		assert(PtrI && "Ptr is not an Instruction");
		if (!postDominatesAnyUse(F, PtrI, PDT, UnsafeUses, LI, TLI)) {
			PtrMayBeNull.insert(Ptr);
			MayNull = true;
		}

		assert(PtrToBaseMap.count(Ptr));
		Value* Base = PtrToBaseMap[Ptr];
		if (BaseToLenMap.count(Base)) {
			continue;
		}
		if (BaseToPtrsMap.count(Base)) {
			if (!MayNull) {
				BaseToPtrsMap[Base].insert(Ptr);
			}
		}
		else {
			auto Size = getStaticBaseSize(F, Base, DL, TLI);
			if (Size) {
				BaseToLenMap[Base] = Size;
			}
			else {
				if (!MayNull) {
					BaseToPtrsMap[Base].insert(Ptr);
				}
			}
		}

	}

	DenseMap<Value*, Value*> LoopUsages;
	DenseSet<Value*> CondLoop;
	DenseSet<Value*> SafeBases;

	for (auto &It : BaseToPtrsMap) {
		Value* Base = It.first;
		DenseSet<Value*> &ValSet = It.second;
		Instruction *BaseI = dyn_cast<Instruction>(Base);
		if (!BaseI) {
			BaseI = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
			assert(BaseI);
		}
		if (isa<SelectInst>(BaseI) || isa<PHINode>(BaseI)) {
			assert(PhiOrSelBaseToOrig.count(BaseI));
			BaseI = cast<Instruction>(PhiOrSelBaseToOrig[BaseI]);
		}

		bool Recurrance;
		if (postDominatesAnyPtrDef(F, BaseI, PDT, ValSet, LI, LoopUsages, CondLoop, Recurrance)) {
			SafeBases.insert(Base);
		}

		if (!HasIndefiniteBase && indefiniteBase(Base, DL)) {
			HasIndefiniteBase = true;
		}
	}




	DenseSet<Value*> SafeInteriors;
	DenseSet<Value*> SafeLargerThan;

	collectSafeEscapes(F, CallSites, RetSites, Stores, InteriorPointersSet, TLI, SafeInteriors, PDT, LI);
	collectSafeEscapes(F, CallSites, RetSites, Stores, LargerThanBase, TLI, SafeLargerThan, PDT, LI);

	DenseSet<Value*> NonAccessSet;

	for (auto Ptr : InteriorPointersSet) {
		NonAccessSet.insert(Ptr);
	}
	for (auto Ptr : LargerThanBase) {
		NonAccessSet.insert(Ptr);
		if (!PtrToBaseMap.count(Ptr)) {
			PtrToBaseMap[Ptr] = Ptr->stripPointerCasts();
		}
	}

	DenseMap<Value*, DenseSet<Value*>> IBaseToPtrMap;

	for (auto Ptr : NonAccessSet) {
		assert(PtrToBaseMap.count(Ptr));
		Value* Base = PtrToBaseMap[Ptr];
		if (BaseToLenMap.count(Base)) {
			continue;
		}
		auto Size = getStaticBaseSize(F, Base, DL, TLI);
		if (Size) {
			BaseToLenMap[Base] = Size;
		}
		else {
			if (isa<Instruction>(Ptr)) {
				if (SafeInteriors.count(Ptr) || SafeLargerThan.count(Ptr)) {
					IBaseToPtrMap[Base].insert(Ptr);
				}
			}
		}
	}

	DenseMap<Value*, Value*> ILoopUsages;
	DenseSet<Value*> ICondLoop;
	DenseSet<Value*> ISafeBases;

	for (auto &It : IBaseToPtrMap) {
		Value* Base = It.first;
		DenseSet<Value*> &ValSet = It.second;
		if (ValSet.size() <= 1) {
			//continue;
		}
		Instruction *BaseI = dyn_cast<Instruction>(Base);
		if (!BaseI) {
			BaseI = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
			assert(BaseI);
		}
		if (isa<SelectInst>(BaseI) || isa<PHINode>(BaseI)) {
			assert(PhiOrSelBaseToOrig.count(BaseI));
			BaseI = cast<Instruction>(PhiOrSelBaseToOrig[BaseI]);
		}

		bool Recurrance = false;
		if (postDominatesAnyPtrDef(F, BaseI, PDT, ValSet, LI, ILoopUsages, ICondLoop, Recurrance)) {
			ISafeBases.insert(Base);
		}
		/*else if (Recurrance) {
			ISafeBases.insert(Base);
		}*/
		if (!HasIndefiniteBase && indefiniteBase(Base, DL)) {
			HasIndefiniteBase = true;
		}
	}




	for (auto Base : SafeBases) {
		assert(!BaseToLenMap.count(Base));
		BaseToLenMap[Base] = getLimit(F, Base, DL, TLI);
		GetLengths.insert(BaseToLenMap[Base]);
	}


	for (auto Base : ISafeBases) {
		if (!BaseToLenMap.count(Base)) {
			BaseToLenMap[Base] = getLimitSafe(F, Base, DL, TLI);
			GetLengths.insert(BaseToLenMap[Base]);
		}
	}


	DenseMap<Value*, Value*> PtrToLenMap;
	DenseMap<Value*, Value*> PtrUseToLenMap;

	for (auto Ptr : TmpSet) {
		assert(PtrToBaseMap.count(Ptr));
		Value* Base = PtrToBaseMap[Ptr];
		bool MayNull = PtrMayBeNull.count(Ptr) > 0;

		if (!BaseToLenMap.count(Base)) {
			if (!MayNull) {
				addLengthAtPtr(F, Base, Ptr, PtrToLenMap, GetLengths,
					GetLengthsCond, LenToBaseMap, LoopUsages, CondLoop);
				assert(PtrToLenMap.count(Ptr));
			}
			else {
				addLengthAtPtrUse(F, Base, Ptr, PtrUseToLenMap, UnsafeUses, GetLengths, LenToBaseMap);
			}
		}
	}


	for (auto Ptr : TmpSet) {
		assert(PtrToBaseMap.count(Ptr));
		Value* Base = PtrToBaseMap[Ptr];
		uint64_t TypeSize = UnsafePointers[Ptr];
		auto TySize = ConstantInt::get(Int64Ty, (int)TypeSize);
		bool MayNull = PtrMayBeNull.count(Ptr) > 0;

		if (!MayNull) {
			SafePtrs.insert(Ptr);
		}

		if (!BaseToLenMap.count(Base)) {
			if (!MayNull) {
				assert(PtrToLenMap.count(Ptr));
				auto Limit = PtrToLenMap[Ptr];
				addBoundsCheck(F, Base, Ptr, Limit, TySize, UnsafeUses, callsites, MayNull);
			}
			else {
				addBoundsCheckWithLenAtUse(F, Base, Ptr, TySize, UnsafeUses,
					callsites, PtrUseToLenMap);
			}
		}
		else {
			auto Limit = BaseToLenMap[Base];
			addBoundsCheck(F, Base, Ptr, Limit, TySize, UnsafeUses, callsites, MayNull);
		}
	}

	for (auto MC : MemCalls) {
		if (isa<MemIntrinsic>(MC)) {
			auto Ptr1 = MC->getArgOperand(0);
			auto Ptr2 = MC->getArgOperand(1);
			auto Len = MC->getArgOperand(2);
			assert(Ptr1->getType()->isPointerTy());
			insertChecksForMemCalls(F, PtrToBaseMap, BaseToLenMap, LenToBaseMap,
				PtrUseToLenMap, GetLengths, MC, Ptr1, Len, TLI, false);
			if (Ptr2->getType()->isPointerTy()) {
				insertChecksForMemCalls(F, PtrToBaseMap, BaseToLenMap, LenToBaseMap,
					PtrUseToLenMap, GetLengths, MC, Ptr2, Len, TLI, false);
			}
		}
		else {
			LibFunc Func;
			if (TLI->getLibFunc(ImmutableCallSite(MC), Func)) {
				if (Func == LibFunc_strlen || Func == LibFunc_sprintf || Func == LibFunc_vsprintf) {
					auto Ptr1 = MC->getArgOperand(0);
					insertChecksForMemCalls(F, PtrToBaseMap, BaseToLenMap, LenToBaseMap,
						PtrUseToLenMap, GetLengths, MC, Ptr1, MC, TLI, true);
				}
				else if (Func == LibFunc_snprintf || Func == LibFunc_vsnprintf) {
					auto Ptr1 = MC->getArgOperand(0);
					auto Len = MC->getArgOperand(1);
					insertChecksForMemCalls(F, PtrToBaseMap, BaseToLenMap, LenToBaseMap,
						PtrUseToLenMap, GetLengths, MC, Ptr1, Len, TLI, false);
				}
				else {
					assert(0);
				}
			}
			else {
				assert(0);
			}
		}
	}


	/*if (verifyFunction(F, &errs())) {
    F.dump();
    report_fatal_error("verification of newFunction failed!");
  }*/


	removeRedundentLengths(F, GetLengths, LenToBaseMap);

	DenseMap<Value*, DenseSet<Value*>> BaseToLenSetMap;

	for (auto itr1 = GetLengths.begin(); itr1 != GetLengths.end(); itr1++) {
		Instruction *len1 = cast<Instruction>(*itr1);
		if (LenToBaseMap.count(len1)) {
			auto Base = LenToBaseMap[len1];
			BaseToLenSetMap[Base].insert(len1);
		}
	}



	//DenseSet<Value*> IGetLengths;
	//DenseMap<Value*, Value*> ILenToBaseMap;

	handleInteriors(F, ReplacementMap, CallSites, RetSites, Stores,
		InteriorPointersSet, TLI, SafePtrs, PtrToBaseMap,
		SafeInteriors, BaseToLenMap, BaseToLenSetMap, ILoopUsages, ICondLoop,
		GetLengths, LenToBaseMap);

	handleLargerBase(F, CallSites, RetSites, Stores,
		LargerThanBase, TLI, SafePtrs, PtrToBaseMap,
		SafeLargerThan, BaseToLenMap, BaseToLenSetMap, ILoopUsages, ICondLoop,
		GetLengths, LenToBaseMap);


	//removeRedundentLengths(F, GetLengths, LenToBaseMap);
	instrumentPageFaultHandler(F, GetLengths, GetLengthsCond, Stores, CallSites);

	for (auto Limit : GetLengths) {
		auto Call = dyn_cast<CallBase>(Limit);
		if (Call && ICondLoop.count(Call))  {
			assert(0);
			assert(LenToBaseMap.count(Call));
			auto Base = LenToBaseMap[Call];
			createCondCall(F, Call, Base, NULL, NULL);
		}
	}


	initializeAllocasAndMalloc(F, TLI);

	/*if (verifyFunction(F, &errs())) {
    F.dump();
    report_fatal_error("verification of newFunction failed1!");
  }*/

	optimizeHandlers(F, UnsafeMap, AA, AC, TLI, BaseToLenMap);


	if (!UnsafeAllocas.empty()) {
		//DominatorTree DT(F);
		//PostDominatorTree PDT(F);
		DenseSet<AllocaInst*> ToDelete;
		bool DallocaReg = false;
		for (auto AI : UnsafeAllocas) {
			auto Mem = allocaToMalloc(&F, AI, DallocaReg);
			if (Mem) {
				ToDelete.insert(AI);
			}
		}
		for (auto AI : ToDelete) {
			UnsafeAllocas.erase(AI);
		}
	}

	Value *StackBase = NULL;
	int MaxRecordIndex = (int)UnsafeAllocas.size();
	bool NeedRegisteration = !RestorePoints.empty();

	if (!NeedRegisteration && !UnsafeAllocas.empty()) {
		if (HasIndefiniteBase) {
			NeedRegisteration = true;
		}
		else {
			NeedRegisteration = checkIfRegisterationIsRequired(UnsafeAllocas, TLI);
		}
	}

	if (NeedRegisteration) {
		StackBase = enterScope(&F, MaxRecordIndex);
	}

	int RecordIndex = 0;

	for (auto AI : UnsafeAllocas) {
		MDNode* N = MDNode::get(AI->getContext(), {});
		AI->setMetadata("san_sizeinfo", N);
		if (AI->isStaticAlloca()) {
			patchStaticAlloca(F, AI, StackBase, RecordIndex);
		}
		else {
			patchDynamicAlloca(F, AI, StackBase, RecordIndex);
		}
	}


	if (StackBase) {
		assert(RecordIndex == MaxRecordIndex);
		if (RestorePoints.empty() && !RecordIndex) {
			errs() << "Removing Stack Base\n";
			cast<CallInst>(StackBase)->eraseFromParent();
		}
		else {
			if (RecordIndex != MaxRecordIndex) {
				auto Call = cast<CallInst>(StackBase);
				auto Int32Ty = Call->getArgOperand(0)->getType();
				Call->setArgOperand(0, ConstantInt::get(Int32Ty, RecordIndex));
			}
			exitScope(&F, StackBase);
		}
	}


	//instrumentPtrToInt(F, PtrToInt, GEPs, DL);
	//instrumentOtherPointerUsage(F, ICmpOrSub, IntToPtr, PtrToInt, DL);


	if (!RestorePoints.empty()) {
		restoreStack(F, RestorePoints, StackBase);
	}

	for (auto Ptr : FnPtrs) {
		auto SI = dyn_cast<StoreInst>(Ptr);
		if (SI) {
			auto V = SI->getValueOperand();
			V = buildInvalid(F, V, SI);
			SI->setOperand(0, V);
		}
		else if (auto CS = dyn_cast<CallInst>(Ptr)) {
			LibFunc Func;
			if (!TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
				for (auto ArgIt = CS->arg_begin(), End = CS->arg_end(), Start = CS->arg_begin(); ArgIt != End; ++ArgIt) {
        	Value *A = *ArgIt;
        	if (A->getType()->isPointerTy()) {
						auto ElemTy = A->getType()->getPointerElementType();
						if (!ElemTy->isSized()) {
							A = buildInvalid(F, A, CS);
							CS->setArgOperand(ArgIt - Start, A);
						}
					}
				}
			}
		}
		else if (auto RI = dyn_cast<ReturnInst>(Ptr)) {
			auto *V = RI->getReturnValue();
			V = buildInvalid(F, V, RI);
			RI->setOperand(0, V);
		}
	}



  if (!ClDebugFunc.empty() && F.getName().startswith(ClDebugFunc)) {
		errs() << "After San\n" << F << "\n";
	}

	if (verifyFunction(F, &errs())) {
    F.dump();
    report_fatal_error("verification of newFunction failed!");
  }

	return true;
}

bool FastAddressSanitizer::instrumentFunction(Function &F,
                                          const TargetLibraryInfo *TLI,
																					AAResults *AA,
																					AssumptionCache *AC) {
	instrumentFunctionNew(F, TLI, AA, AC);
	if (!CompileKernel)
		return false;

  if (F.getLinkage() == GlobalValue::AvailableExternallyLinkage) return false;
  if (!ClDebugFunc.empty() && ClDebugFunc == F.getName()) return false;
  if (F.getName().startswith("__asan_")) return false;

  bool FunctionModified = false;

  // If needed, insert __asan_init before checking for SanitizeAddress attr.
  // This function needs to be called even if the function body is not
  // instrumented.
  if (maybeInsertAsanInitAtFunctionEntry(F))
    FunctionModified = true;

  // Leave if the function doesn't need instrumentation.
  if (!F.hasFnAttribute(Attribute::SanitizeAddress)) return FunctionModified;

  LLVM_DEBUG(dbgs() << "ASAN instrumenting:\n" << F << "\n");

  initializeCallbacks(*F.getParent());

  FunctionStateRAII CleanupObj(this);

  maybeInsertDynamicShadowAtFunctionEntry(F);

  // We can't instrument allocas used with llvm.localescape. Only static allocas
  // can be passed to that intrinsic.
  markEscapedLocalAllocas(F);

  // We want to instrument every address only once per basic block (unless there
  // are calls between uses).
  SmallPtrSet<Value *, 16> TempsToInstrument;
  SmallVector<Instruction *, 16> ToInstrument;
  SmallVector<Instruction *, 8> NoReturnCalls;
  SmallVector<BasicBlock *, 16> AllBlocks;
  SmallVector<Instruction *, 16> PointerComparisonsOrSubtracts;
  int NumAllocas = 0;
  bool IsWrite;
  unsigned Alignment;
  uint64_t TypeSize;

  // Fill the set of memory operations to instrument.
  for (auto &BB : F) {
    AllBlocks.push_back(&BB);
    TempsToInstrument.clear();
    int NumInsnsPerBB = 0;
    for (auto &Inst : BB) {
      if (LooksLikeCodeInBug11395(&Inst)) return false;
      Value *MaybeMask = nullptr;
      if (Value *Addr = isInterestingMemoryAccess(&Inst, &IsWrite, &TypeSize,
                                                  &Alignment, &MaybeMask)) {
        if (ClOpt && ClOptSameTemp) {
          // If we have a mask, skip instrumentation if we've already
          // instrumented the full object. But don't add to TempsToInstrument
          // because we might get another load/store with a different mask.
          if (MaybeMask) {
            if (TempsToInstrument.count(Addr))
              continue; // We've seen this (whole) temp in the current BB.
          } else {
            if (!TempsToInstrument.insert(Addr).second)
              continue; // We've seen this temp in the current BB.
          }
        }
      } else if (((ClInvalidPointerPairs || ClInvalidPointerCmp) &&
                  isInterestingPointerComparison(&Inst)) ||
                 ((ClInvalidPointerPairs || ClInvalidPointerSub) &&
                  isInterestingPointerSubtraction(&Inst))) {
        PointerComparisonsOrSubtracts.push_back(&Inst);
        continue;
      } else if (isa<MemIntrinsic>(Inst)) {
        // ok, take it.
      } else {
        if (isa<AllocaInst>(Inst)) NumAllocas++;
        CallSite CS(&Inst);
        if (CS) {
          // A call inside BB.
          TempsToInstrument.clear();
          if (CS.doesNotReturn() && !CS->hasMetadata("nosanitize"))
            NoReturnCalls.push_back(CS.getInstruction());
        }
        if (CallInst *CI = dyn_cast<CallInst>(&Inst))
          maybeMarkSanitizerLibraryCallNoBuiltin(CI, TLI);
        continue;
      }
      ToInstrument.push_back(&Inst);
      NumInsnsPerBB++;
      if (NumInsnsPerBB >= ClMaxInsnsToInstrumentPerBB) break;
    }
  }

  bool UseCalls =
      (ClInstrumentationWithCallsThreshold >= 0 &&
       ToInstrument.size() > (unsigned)ClInstrumentationWithCallsThreshold);
  const DataLayout &DL = F.getParent()->getDataLayout();
  ObjectSizeOpts ObjSizeOpts;
  ObjSizeOpts.RoundToAlign = true;
  ObjectSizeOffsetVisitor ObjSizeVis(DL, TLI, F.getContext(), ObjSizeOpts);

  // Instrument.
  int NumInstrumented = 0;
  for (auto Inst : ToInstrument) {
    if (ClDebugMin < 0 || ClDebugMax < 0 ||
        (NumInstrumented >= ClDebugMin && NumInstrumented <= ClDebugMax)) {
      if (isInterestingMemoryAccess(Inst, &IsWrite, &TypeSize, &Alignment))
        instrumentMop(ObjSizeVis, Inst, UseCalls,
                      F.getParent()->getDataLayout());
      else
        instrumentMemIntrinsic(cast<MemIntrinsic>(Inst));
    }
    NumInstrumented++;
  }

  FunctionStackPoisoner FSP(F, *this);
  bool ChangedStack = FSP.runOnFunction();

  // We must unpoison the stack before NoReturn calls (throw, _exit, etc).
  // See e.g. https://github.com/google/sanitizers/issues/37
  for (auto CI : NoReturnCalls) {
    IRBuilder<> IRB(CI);
    IRB.CreateCall(AsanHandleNoReturnFunc, {});
  }

  for (auto Inst : PointerComparisonsOrSubtracts) {
    instrumentPointerComparisonOrSubtraction(Inst);
    NumInstrumented++;
  }

  if (NumInstrumented > 0 || ChangedStack || !NoReturnCalls.empty())
    FunctionModified = true;

  LLVM_DEBUG(dbgs() << "ASAN done instrumenting: " << FunctionModified << " "
                    << F << "\n");

  return FunctionModified;
}

// Workaround for bug 11395: we don't want to instrument stack in functions
// with large assembly blobs (32-bit only), otherwise reg alloc may crash.
// FIXME: remove once the bug 11395 is fixed.
bool FastAddressSanitizer::LooksLikeCodeInBug11395(Instruction *I) {
  if (LongSize != 32) return false;
  CallInst *CI = dyn_cast<CallInst>(I);
  if (!CI || !CI->isInlineAsm()) return false;
  if (CI->getNumArgOperands() <= 5) return false;
  // We have inline assembly with quite a few arguments.
  return true;
}

void FunctionStackPoisoner::initializeCallbacks(Module &M) {
  IRBuilder<> IRB(*C);
  for (int i = 0; i <= kMaxAsanStackMallocSizeClass; i++) {
    std::string Suffix = itostr(i);
    AsanStackMallocFunc[i] = M.getOrInsertFunction(
        kAsanStackMallocNameTemplate + Suffix, IntptrTy, IntptrTy);
    AsanStackFreeFunc[i] =
        M.getOrInsertFunction(kAsanStackFreeNameTemplate + Suffix,
                              IRB.getVoidTy(), IntptrTy, IntptrTy);
  }
  if (ASan.UseAfterScope) {
    AsanPoisonStackMemoryFunc = M.getOrInsertFunction(
        kAsanPoisonStackMemoryName, IRB.getVoidTy(), IntptrTy, IntptrTy);
    AsanUnpoisonStackMemoryFunc = M.getOrInsertFunction(
        kAsanUnpoisonStackMemoryName, IRB.getVoidTy(), IntptrTy, IntptrTy);
  }

  for (size_t Val : {0x00, 0xf1, 0xf2, 0xf3, 0xf5, 0xf8}) {
    std::ostringstream Name;
    Name << kAsanSetShadowPrefix;
    Name << std::setw(2) << std::setfill('0') << std::hex << Val;
    AsanSetShadowFunc[Val] =
        M.getOrInsertFunction(Name.str(), IRB.getVoidTy(), IntptrTy, IntptrTy);
  }

  AsanAllocaPoisonFunc = M.getOrInsertFunction(
      kAsanAllocaPoison, IRB.getVoidTy(), IntptrTy, IntptrTy);
  AsanAllocasUnpoisonFunc = M.getOrInsertFunction(
      kAsanAllocasUnpoison, IRB.getVoidTy(), IntptrTy, IntptrTy);
}

void FunctionStackPoisoner::copyToShadowInline(ArrayRef<uint8_t> ShadowMask,
                                               ArrayRef<uint8_t> ShadowBytes,
                                               size_t Begin, size_t End,
                                               IRBuilder<> &IRB,
                                               Value *ShadowBase) {
  if (Begin >= End)
    return;

  const size_t LargestStoreSizeInBytes =
      std::min<size_t>(sizeof(uint64_t), ASan.LongSize / 8);

  const bool IsLittleEndian = F.getParent()->getDataLayout().isLittleEndian();

  // Poison given range in shadow using larges store size with out leading and
  // trailing zeros in ShadowMask. Zeros never change, so they need neither
  // poisoning nor up-poisoning. Still we don't mind if some of them get into a
  // middle of a store.
  for (size_t i = Begin; i < End;) {
    if (!ShadowMask[i]) {
      assert(!ShadowBytes[i]);
      ++i;
      continue;
    }

    size_t StoreSizeInBytes = LargestStoreSizeInBytes;
    // Fit store size into the range.
    while (StoreSizeInBytes > End - i)
      StoreSizeInBytes /= 2;

    // Minimize store size by trimming trailing zeros.
    for (size_t j = StoreSizeInBytes - 1; j && !ShadowMask[i + j]; --j) {
      while (j <= StoreSizeInBytes / 2)
        StoreSizeInBytes /= 2;
    }

    uint64_t Val = 0;
    for (size_t j = 0; j < StoreSizeInBytes; j++) {
      if (IsLittleEndian)
        Val |= (uint64_t)ShadowBytes[i + j] << (8 * j);
      else
        Val = (Val << 8) | ShadowBytes[i + j];
    }

    Value *Ptr = IRB.CreateAdd(ShadowBase, ConstantInt::get(IntptrTy, i));
    Value *Poison = IRB.getIntN(StoreSizeInBytes * 8, Val);
    IRB.CreateAlignedStore(
        Poison, IRB.CreateIntToPtr(Ptr, Poison->getType()->getPointerTo()), 1);

    i += StoreSizeInBytes;
  }
}

void FunctionStackPoisoner::copyToShadow(ArrayRef<uint8_t> ShadowMask,
                                         ArrayRef<uint8_t> ShadowBytes,
                                         IRBuilder<> &IRB, Value *ShadowBase) {
  copyToShadow(ShadowMask, ShadowBytes, 0, ShadowMask.size(), IRB, ShadowBase);
}

void FunctionStackPoisoner::copyToShadow(ArrayRef<uint8_t> ShadowMask,
                                         ArrayRef<uint8_t> ShadowBytes,
                                         size_t Begin, size_t End,
                                         IRBuilder<> &IRB, Value *ShadowBase) {
  assert(ShadowMask.size() == ShadowBytes.size());
  size_t Done = Begin;
  for (size_t i = Begin, j = Begin + 1; i < End; i = j++) {
    if (!ShadowMask[i]) {
      assert(!ShadowBytes[i]);
      continue;
    }
    uint8_t Val = ShadowBytes[i];
    if (!AsanSetShadowFunc[Val])
      continue;

    // Skip same values.
    for (; j < End && ShadowMask[j] && Val == ShadowBytes[j]; ++j) {
    }

    if (j - i >= ClMaxInlinePoisoningSize) {
      copyToShadowInline(ShadowMask, ShadowBytes, Done, i, IRB, ShadowBase);
      IRB.CreateCall(AsanSetShadowFunc[Val],
                     {IRB.CreateAdd(ShadowBase, ConstantInt::get(IntptrTy, i)),
                      ConstantInt::get(IntptrTy, j - i)});
      Done = j;
    }
  }

  copyToShadowInline(ShadowMask, ShadowBytes, Done, End, IRB, ShadowBase);
}

// Fake stack allocator (asan_fake_stack.h) has 11 size classes
// for every power of 2 from kMinStackMallocSize to kMaxAsanStackMallocSizeClass
static int StackMallocSizeClass(uint64_t LocalStackSize) {
  assert(LocalStackSize <= kMaxStackMallocSize);
  uint64_t MaxSize = kMinStackMallocSize;
  for (int i = 0;; i++, MaxSize *= 2)
    if (LocalStackSize <= MaxSize) return i;
  llvm_unreachable("impossible LocalStackSize");
}

void FunctionStackPoisoner::copyArgsPassedByValToAllocas() {
  Instruction *CopyInsertPoint = &F.front().front();
  if (CopyInsertPoint == ASan.LocalDynamicShadow) {
    // Insert after the dynamic shadow location is determined
    CopyInsertPoint = CopyInsertPoint->getNextNode();
    assert(CopyInsertPoint);
  }
  IRBuilder<> IRB(CopyInsertPoint);
  const DataLayout &DL = F.getParent()->getDataLayout();
  for (Argument &Arg : F.args()) {
    if (Arg.hasByValAttr()) {
      Type *Ty = Arg.getType()->getPointerElementType();
      const Align Alignment =
          DL.getValueOrABITypeAlignment(Arg.getParamAlign(), Ty);

      AllocaInst *AI = IRB.CreateAlloca(
          Ty, nullptr,
          (Arg.hasName() ? Arg.getName() : "Arg" + Twine(Arg.getArgNo())) +
              ".byval");
      AI->setAlignment(Alignment);
      Arg.replaceAllUsesWith(AI);

      uint64_t AllocSize = DL.getTypeAllocSize(Ty);
      IRB.CreateMemCpy(AI, Alignment, &Arg, Alignment, AllocSize);
    }
  }
}

PHINode *FunctionStackPoisoner::createPHI(IRBuilder<> &IRB, Value *Cond,
                                          Value *ValueIfTrue,
                                          Instruction *ThenTerm,
                                          Value *ValueIfFalse) {
  PHINode *PHI = IRB.CreatePHI(IntptrTy, 2);
  BasicBlock *CondBlock = cast<Instruction>(Cond)->getParent();
  PHI->addIncoming(ValueIfFalse, CondBlock);
  BasicBlock *ThenBlock = ThenTerm->getParent();
  PHI->addIncoming(ValueIfTrue, ThenBlock);
  return PHI;
}

Value *FunctionStackPoisoner::createAllocaForLayout(
    IRBuilder<> &IRB, const ASanStackFrameLayout &L, bool Dynamic) {
  AllocaInst *Alloca;
  if (Dynamic) {
    Alloca = IRB.CreateAlloca(IRB.getInt8Ty(),
                              ConstantInt::get(IRB.getInt64Ty(), L.FrameSize),
                              "MyAlloca");
  } else {
    Alloca = IRB.CreateAlloca(ArrayType::get(IRB.getInt8Ty(), L.FrameSize),
                              nullptr, "MyAlloca");
    assert(Alloca->isStaticAlloca());
  }
  assert((ClRealignStack & (ClRealignStack - 1)) == 0);
  size_t FrameAlignment = std::max(L.FrameAlignment, (size_t)ClRealignStack);
  Alloca->setAlignment(MaybeAlign(FrameAlignment));
  return IRB.CreatePointerCast(Alloca, IntptrTy);
}

void FunctionStackPoisoner::createDynamicAllocasInitStorage() {
  BasicBlock &FirstBB = *F.begin();
  IRBuilder<> IRB(dyn_cast<Instruction>(FirstBB.begin()));
  DynamicAllocaLayout = IRB.CreateAlloca(IntptrTy, nullptr);
  IRB.CreateStore(Constant::getNullValue(IntptrTy), DynamicAllocaLayout);
  DynamicAllocaLayout->setAlignment(Align(32));
}

void FunctionStackPoisoner::processDynamicAllocas() {
  if (!ClInstrumentDynamicAllocas || DynamicAllocaVec.empty()) {
    assert(DynamicAllocaPoisonCallVec.empty());
    return;
  }

  // Insert poison calls for lifetime intrinsics for dynamic allocas.
  for (const auto &APC : DynamicAllocaPoisonCallVec) {
    assert(APC.InsBefore);
    assert(APC.AI);
    assert(ASan.isInterestingAlloca(*APC.AI));
    assert(!APC.AI->isStaticAlloca());

    IRBuilder<> IRB(APC.InsBefore);
    poisonAlloca(APC.AI, APC.Size, IRB, APC.DoPoison);
    // Dynamic allocas will be unpoisoned unconditionally below in
    // unpoisonDynamicAllocas.
    // Flag that we need unpoison static allocas.
  }

  // Handle dynamic allocas.
  createDynamicAllocasInitStorage();
  for (auto &AI : DynamicAllocaVec)
    handleDynamicAllocaCall(AI);
  unpoisonDynamicAllocas();
}

void FunctionStackPoisoner::processStaticAllocas() {
  if (AllocaVec.empty()) {
    assert(StaticAllocaPoisonCallVec.empty());
    return;
  }

  int StackMallocIdx = -1;
  DebugLoc EntryDebugLocation;
  if (auto SP = F.getSubprogram())
    EntryDebugLocation = DebugLoc::get(SP->getScopeLine(), 0, SP);

  Instruction *InsBefore = AllocaVec[0];
  IRBuilder<> IRB(InsBefore);

  // Make sure non-instrumented allocas stay in the entry block. Otherwise,
  // debug info is broken, because only entry-block allocas are treated as
  // regular stack slots.
  auto InsBeforeB = InsBefore->getParent();
  assert(InsBeforeB == &F.getEntryBlock());
  for (auto *AI : StaticAllocasToMoveUp)
    if (AI->getParent() == InsBeforeB)
      AI->moveBefore(InsBefore);

  // If we have a call to llvm.localescape, keep it in the entry block.
  if (LocalEscapeCall) LocalEscapeCall->moveBefore(InsBefore);

  SmallVector<ASanStackVariableDescription, 16> SVD;
  SVD.reserve(AllocaVec.size());
  for (AllocaInst *AI : AllocaVec) {
    ASanStackVariableDescription D = {AI->getName().data(),
                                      ASan.getAllocaSizeInBytes(*AI),
                                      0,
                                      AI->getAlignment(),
                                      AI,
                                      0,
                                      0};
    SVD.push_back(D);
  }

  // Minimal header size (left redzone) is 4 pointers,
  // i.e. 32 bytes on 64-bit platforms and 16 bytes in 32-bit platforms.
  size_t Granularity = 1ULL << Mapping.Scale;
  size_t MinHeaderSize = std::max((size_t)ASan.LongSize / 2, Granularity);
  const ASanStackFrameLayout &L =
      ComputeASanStackFrameLayout(SVD, Granularity, MinHeaderSize);

  // Build AllocaToSVDMap for ASanStackVariableDescription lookup.
  DenseMap<const AllocaInst *, ASanStackVariableDescription *> AllocaToSVDMap;
  for (auto &Desc : SVD)
    AllocaToSVDMap[Desc.AI] = &Desc;

  // Update SVD with information from lifetime intrinsics.
  for (const auto &APC : StaticAllocaPoisonCallVec) {
    assert(APC.InsBefore);
    assert(APC.AI);
    assert(ASan.isInterestingAlloca(*APC.AI));
    assert(APC.AI->isStaticAlloca());

    ASanStackVariableDescription &Desc = *AllocaToSVDMap[APC.AI];
    Desc.LifetimeSize = Desc.Size;
    if (const DILocation *FnLoc = EntryDebugLocation.get()) {
      if (const DILocation *LifetimeLoc = APC.InsBefore->getDebugLoc().get()) {
        if (LifetimeLoc->getFile() == FnLoc->getFile())
          if (unsigned Line = LifetimeLoc->getLine())
            Desc.Line = std::min(Desc.Line ? Desc.Line : Line, Line);
      }
    }
  }

  auto DescriptionString = ComputeASanStackFrameDescription(SVD);
  LLVM_DEBUG(dbgs() << DescriptionString << " --- " << L.FrameSize << "\n");
  uint64_t LocalStackSize = L.FrameSize;
  bool DoStackMalloc = ClUseAfterReturn && !ASan.CompileKernel &&
                       LocalStackSize <= kMaxStackMallocSize;
  bool DoDynamicAlloca = ClDynamicAllocaStack;
  // Don't do dynamic alloca or stack malloc if:
  // 1) There is inline asm: too often it makes assumptions on which registers
  //    are available.
  // 2) There is a returns_twice call (typically setjmp), which is
  //    optimization-hostile, and doesn't play well with introduced indirect
  //    register-relative calculation of local variable addresses.
  DoDynamicAlloca &= !HasNonEmptyInlineAsm && !HasReturnsTwiceCall;
  DoStackMalloc &= !HasNonEmptyInlineAsm && !HasReturnsTwiceCall;

  Value *StaticAlloca =
      DoDynamicAlloca ? nullptr : createAllocaForLayout(IRB, L, false);

  Value *FakeStack;
  Value *LocalStackBase;
  Value *LocalStackBaseAlloca;
  uint8_t DIExprFlags = DIExpression::ApplyOffset;

  if (DoStackMalloc) {
    LocalStackBaseAlloca =
        IRB.CreateAlloca(IntptrTy, nullptr, "asan_local_stack_base");
    // void *FakeStack = __asan_option_detect_stack_use_after_return
    //     ? __asan_stack_malloc_N(LocalStackSize)
    //     : nullptr;
    // void *LocalStackBase = (FakeStack) ? FakeStack : alloca(LocalStackSize);
    Constant *OptionDetectUseAfterReturn = F.getParent()->getOrInsertGlobal(
        kAsanOptionDetectUseAfterReturn, IRB.getInt32Ty());
    Value *UseAfterReturnIsEnabled = IRB.CreateICmpNE(
        IRB.CreateLoad(IRB.getInt32Ty(), OptionDetectUseAfterReturn),
        Constant::getNullValue(IRB.getInt32Ty()));
    Instruction *Term =
        SplitBlockAndInsertIfThen(UseAfterReturnIsEnabled, InsBefore, false);
    IRBuilder<> IRBIf(Term);
    StackMallocIdx = StackMallocSizeClass(LocalStackSize);
    assert(StackMallocIdx <= kMaxAsanStackMallocSizeClass);
    Value *FakeStackValue =
        IRBIf.CreateCall(AsanStackMallocFunc[StackMallocIdx],
                         ConstantInt::get(IntptrTy, LocalStackSize));
    IRB.SetInsertPoint(InsBefore);
    FakeStack = createPHI(IRB, UseAfterReturnIsEnabled, FakeStackValue, Term,
                          ConstantInt::get(IntptrTy, 0));

    Value *NoFakeStack =
        IRB.CreateICmpEQ(FakeStack, Constant::getNullValue(IntptrTy));
    Term = SplitBlockAndInsertIfThen(NoFakeStack, InsBefore, false);
    IRBIf.SetInsertPoint(Term);
    Value *AllocaValue =
        DoDynamicAlloca ? createAllocaForLayout(IRBIf, L, true) : StaticAlloca;

    IRB.SetInsertPoint(InsBefore);
    LocalStackBase = createPHI(IRB, NoFakeStack, AllocaValue, Term, FakeStack);
    IRB.CreateStore(LocalStackBase, LocalStackBaseAlloca);
    DIExprFlags |= DIExpression::DerefBefore;
  } else {
    // void *FakeStack = nullptr;
    // void *LocalStackBase = alloca(LocalStackSize);
    FakeStack = ConstantInt::get(IntptrTy, 0);
    LocalStackBase =
        DoDynamicAlloca ? createAllocaForLayout(IRB, L, true) : StaticAlloca;
    LocalStackBaseAlloca = LocalStackBase;
  }

  // Replace Alloca instructions with base+offset.
  for (const auto &Desc : SVD) {
    AllocaInst *AI = Desc.AI;
    replaceDbgDeclareForAlloca(AI, LocalStackBaseAlloca, DIB, DIExprFlags,
                               Desc.Offset);
    Value *NewAllocaPtr = IRB.CreateIntToPtr(
        IRB.CreateAdd(LocalStackBase, ConstantInt::get(IntptrTy, Desc.Offset)),
        AI->getType());
    AI->replaceAllUsesWith(NewAllocaPtr);
  }

  // The left-most redzone has enough space for at least 4 pointers.
  // Write the Magic value to redzone[0].
  Value *BasePlus0 = IRB.CreateIntToPtr(LocalStackBase, IntptrPtrTy);
  IRB.CreateStore(ConstantInt::get(IntptrTy, kCurrentStackFrameMagic),
                  BasePlus0);
  // Write the frame description constant to redzone[1].
  Value *BasePlus1 = IRB.CreateIntToPtr(
      IRB.CreateAdd(LocalStackBase,
                    ConstantInt::get(IntptrTy, ASan.LongSize / 8)),
      IntptrPtrTy);
  GlobalVariable *StackDescriptionGlobal =
      createPrivateGlobalForString(*F.getParent(), DescriptionString,
                                   /*AllowMerging*/ true, kAsanGenPrefix);
  Value *Description = IRB.CreatePointerCast(StackDescriptionGlobal, IntptrTy);
  IRB.CreateStore(Description, BasePlus1);
  // Write the PC to redzone[2].
  Value *BasePlus2 = IRB.CreateIntToPtr(
      IRB.CreateAdd(LocalStackBase,
                    ConstantInt::get(IntptrTy, 2 * ASan.LongSize / 8)),
      IntptrPtrTy);
  IRB.CreateStore(IRB.CreatePointerCast(&F, IntptrTy), BasePlus2);

  const auto &ShadowAfterScope = GetShadowBytesAfterScope(SVD, L);

  // Poison the stack red zones at the entry.
  Value *ShadowBase = ASan.memToShadow(LocalStackBase, IRB);
  // As mask we must use most poisoned case: red zones and after scope.
  // As bytes we can use either the same or just red zones only.
  copyToShadow(ShadowAfterScope, ShadowAfterScope, IRB, ShadowBase);

  if (!StaticAllocaPoisonCallVec.empty()) {
    const auto &ShadowInScope = GetShadowBytes(SVD, L);

    // Poison static allocas near lifetime intrinsics.
    for (const auto &APC : StaticAllocaPoisonCallVec) {
      const ASanStackVariableDescription &Desc = *AllocaToSVDMap[APC.AI];
      assert(Desc.Offset % L.Granularity == 0);
      size_t Begin = Desc.Offset / L.Granularity;
      size_t End = Begin + (APC.Size + L.Granularity - 1) / L.Granularity;

      IRBuilder<> IRB(APC.InsBefore);
      copyToShadow(ShadowAfterScope,
                   APC.DoPoison ? ShadowAfterScope : ShadowInScope, Begin, End,
                   IRB, ShadowBase);
    }
  }

  SmallVector<uint8_t, 64> ShadowClean(ShadowAfterScope.size(), 0);
  SmallVector<uint8_t, 64> ShadowAfterReturn;

  // (Un)poison the stack before all ret instructions.
  for (auto Ret : RetVec) {
    IRBuilder<> IRBRet(Ret);
    // Mark the current frame as retired.
    IRBRet.CreateStore(ConstantInt::get(IntptrTy, kRetiredStackFrameMagic),
                       BasePlus0);
    if (DoStackMalloc) {
      assert(StackMallocIdx >= 0);
      // if FakeStack != 0  // LocalStackBase == FakeStack
      //     // In use-after-return mode, poison the whole stack frame.
      //     if StackMallocIdx <= 4
      //         // For small sizes inline the whole thing:
      //         memset(ShadowBase, kAsanStackAfterReturnMagic, ShadowSize);
      //         **SavedFlagPtr(FakeStack) = 0
      //     else
      //         __asan_stack_free_N(FakeStack, LocalStackSize)
      // else
      //     <This is not a fake stack; unpoison the redzones>
      Value *Cmp =
          IRBRet.CreateICmpNE(FakeStack, Constant::getNullValue(IntptrTy));
      Instruction *ThenTerm, *ElseTerm;
      SplitBlockAndInsertIfThenElse(Cmp, Ret, &ThenTerm, &ElseTerm);

      IRBuilder<> IRBPoison(ThenTerm);
      if (StackMallocIdx <= 4) {
        int ClassSize = kMinStackMallocSize << StackMallocIdx;
        ShadowAfterReturn.resize(ClassSize / L.Granularity,
                                 kAsanStackUseAfterReturnMagic);
        copyToShadow(ShadowAfterReturn, ShadowAfterReturn, IRBPoison,
                     ShadowBase);
        Value *SavedFlagPtrPtr = IRBPoison.CreateAdd(
            FakeStack,
            ConstantInt::get(IntptrTy, ClassSize - ASan.LongSize / 8));
        Value *SavedFlagPtr = IRBPoison.CreateLoad(
            IntptrTy, IRBPoison.CreateIntToPtr(SavedFlagPtrPtr, IntptrPtrTy));
        IRBPoison.CreateStore(
            Constant::getNullValue(IRBPoison.getInt8Ty()),
            IRBPoison.CreateIntToPtr(SavedFlagPtr, IRBPoison.getInt8PtrTy()));
      } else {
        // For larger frames call __asan_stack_free_*.
        IRBPoison.CreateCall(
            AsanStackFreeFunc[StackMallocIdx],
            {FakeStack, ConstantInt::get(IntptrTy, LocalStackSize)});
      }

      IRBuilder<> IRBElse(ElseTerm);
      copyToShadow(ShadowAfterScope, ShadowClean, IRBElse, ShadowBase);
    } else {
      copyToShadow(ShadowAfterScope, ShadowClean, IRBRet, ShadowBase);
    }
  }

  // We are done. Remove the old unused alloca instructions.
  for (auto AI : AllocaVec) AI->eraseFromParent();
}

void FunctionStackPoisoner::poisonAlloca(Value *V, uint64_t Size,
                                         IRBuilder<> &IRB, bool DoPoison) {
  // For now just insert the call to ASan runtime.
  Value *AddrArg = IRB.CreatePointerCast(V, IntptrTy);
  Value *SizeArg = ConstantInt::get(IntptrTy, Size);
  IRB.CreateCall(
      DoPoison ? AsanPoisonStackMemoryFunc : AsanUnpoisonStackMemoryFunc,
      {AddrArg, SizeArg});
}

// Handling llvm.lifetime intrinsics for a given %alloca:
// (1) collect all llvm.lifetime.xxx(%size, %value) describing the alloca.
// (2) if %size is constant, poison memory for llvm.lifetime.end (to detect
//     invalid accesses) and unpoison it for llvm.lifetime.start (the memory
//     could be poisoned by previous llvm.lifetime.end instruction, as the
//     variable may go in and out of scope several times, e.g. in loops).
// (3) if we poisoned at least one %alloca in a function,
//     unpoison the whole stack frame at function exit.
void FunctionStackPoisoner::handleDynamicAllocaCall(AllocaInst *AI) {
  IRBuilder<> IRB(AI);

  const unsigned Align = std::max(kAllocaRzSize, AI->getAlignment());
  const uint64_t AllocaRedzoneMask = kAllocaRzSize - 1;

  Value *Zero = Constant::getNullValue(IntptrTy);
  Value *AllocaRzSize = ConstantInt::get(IntptrTy, kAllocaRzSize);
  Value *AllocaRzMask = ConstantInt::get(IntptrTy, AllocaRedzoneMask);

  // Since we need to extend alloca with additional memory to locate
  // redzones, and OldSize is number of allocated blocks with
  // ElementSize size, get allocated memory size in bytes by
  // OldSize * ElementSize.
  const unsigned ElementSize =
      F.getParent()->getDataLayout().getTypeAllocSize(AI->getAllocatedType());
  Value *OldSize =
      IRB.CreateMul(IRB.CreateIntCast(AI->getArraySize(), IntptrTy, false),
                    ConstantInt::get(IntptrTy, ElementSize));

  // PartialSize = OldSize % 32
  Value *PartialSize = IRB.CreateAnd(OldSize, AllocaRzMask);

  // Misalign = kAllocaRzSize - PartialSize;
  Value *Misalign = IRB.CreateSub(AllocaRzSize, PartialSize);

  // PartialPadding = Misalign != kAllocaRzSize ? Misalign : 0;
  Value *Cond = IRB.CreateICmpNE(Misalign, AllocaRzSize);
  Value *PartialPadding = IRB.CreateSelect(Cond, Misalign, Zero);

  // AdditionalChunkSize = Align + PartialPadding + kAllocaRzSize
  // Align is added to locate left redzone, PartialPadding for possible
  // partial redzone and kAllocaRzSize for right redzone respectively.
  Value *AdditionalChunkSize = IRB.CreateAdd(
      ConstantInt::get(IntptrTy, Align + kAllocaRzSize), PartialPadding);

  Value *NewSize = IRB.CreateAdd(OldSize, AdditionalChunkSize);

  // Insert new alloca with new NewSize and Align params.
  AllocaInst *NewAlloca = IRB.CreateAlloca(IRB.getInt8Ty(), NewSize);
  NewAlloca->setAlignment(MaybeAlign(Align));

  // NewAddress = Address + Align
  Value *NewAddress = IRB.CreateAdd(IRB.CreatePtrToInt(NewAlloca, IntptrTy),
                                    ConstantInt::get(IntptrTy, Align));

  // Insert __asan_alloca_poison call for new created alloca.
  IRB.CreateCall(AsanAllocaPoisonFunc, {NewAddress, OldSize});

  // Store the last alloca's address to DynamicAllocaLayout. We'll need this
  // for unpoisoning stuff.
  IRB.CreateStore(IRB.CreatePtrToInt(NewAlloca, IntptrTy), DynamicAllocaLayout);

  Value *NewAddressPtr = IRB.CreateIntToPtr(NewAddress, AI->getType());

  // Replace all uses of AddessReturnedByAlloca with NewAddressPtr.
  AI->replaceAllUsesWith(NewAddressPtr);

  // We are done. Erase old alloca from parent.
  AI->eraseFromParent();
}

// isSafeAccess returns true if Addr is always inbounds with respect to its
// base object. For example, it is a field access or an array access with
// constant inbounds index.
bool FastAddressSanitizer::isSafeAccess(ObjectSizeOffsetVisitor &ObjSizeVis,
                                    Value *Addr, uint64_t TypeSize) const {
  SizeOffsetType SizeOffset = ObjSizeVis.compute(Addr);
  if (!ObjSizeVis.bothKnown(SizeOffset)) return false;
  uint64_t Size = SizeOffset.first.getZExtValue();
  int64_t Offset = SizeOffset.second.getSExtValue();
  // Three checks are required to ensure safety:
  // . Offset >= 0  (since the offset is given from the base ptr)
  // . Size >= Offset  (unsigned)
  // . Size - Offset >= NeededSize  (unsigned)
  return Offset >= 0 && Size >= uint64_t(Offset) &&
         Size - uint64_t(Offset) >= TypeSize / 8;
}
