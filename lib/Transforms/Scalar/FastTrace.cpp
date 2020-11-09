//===- FastTraceimizer.cpp - Optimize use of memcpy and friends -----------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This pass performs various transformations related to eliminating memcpy
// calls, or transforming sets of stores into memset's.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Scalar/FastTrace.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/None.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/MemoryDependenceAnalysis.h"
#include "llvm/Analysis/MemoryLocation.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Operator.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <utility>

using namespace llvm;

#define DEBUG_TYPE "fasttrace"

static cl::opt<bool> ClTrace("fasan-enable-trace", cl::desc("enable trace"), cl::Hidden,
                           cl::init(false));

namespace {

//===----------------------------------------------------------------------===//
//                         MemCpyOptLegacyPass Pass
//===----------------------------------------------------------------------===//

namespace {

class FastTraceLegacyPass : public FunctionPass {
  FastTracePass Impl;

public:
  static char ID; // Pass identification, replacement for typeid
	bool FirstCall;

  FastTraceLegacyPass(bool First = false) : FunctionPass(ID) {
		FirstCall = First;
    initializeFastTraceLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override;

private:
  // This transformation requires dominator postdominator info
  //void getAnalysisUsage(AnalysisUsage &AU) const override {
  //}
};

} // end anonymous namespace
}

char FastTraceLegacyPass::ID = 0;

/// The public interface to this file...
FunctionPass *llvm::createFastTracePass(bool FirstCall) { return new FastTraceLegacyPass(FirstCall); }

INITIALIZE_PASS_BEGIN(FastTraceLegacyPass, "fasttrace", "FastTrace Optimization",
                      false, false)
INITIALIZE_PASS_END(FastTraceLegacyPass, "fasttrace", "FastTrace Optimization",
                    false, false)


static Value* getLineNo(Function &F, Instruction *I, Type *LineTy) {
	int LineNum = 0;
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	return ConstantInt::get(LineTy, LineNum);
}

#define ENTRY_TY 0
#define EXIT_TY 1
#define ICMP_TY 2
#define LOAD_TY 3
#define STORE_TY 4
#define PTR_TO_INT_TY 5
#define	SUB_TY 6

static void insertTraceCall(Function &F, Instruction *I, Value *Val1, Value *Val2, int RecTy, bool InsertAfter)
{
	auto InsertPt = (InsertAfter) ? I->getNextNode() : I;
	IRBuilder<> IRB(InsertPt);
	auto IntTy = IRB.getInt32Ty();
	FunctionCallee Fn;
	auto M = F.getParent();
	auto Name = IRB.CreateGlobalStringPtr(F.getName());
	Value *Line = getLineNo(F, I, IntTy);

	if (Val2 == NULL) {
		Val2 = ConstantInt::get(IntTy, 0);
	}

	Fn = M->getOrInsertFunction("san_trace", IRB.getVoidTy(), Name->getType(), IntTy, IntTy, Val1->getType(), Val2->getType());
	IRB.CreateCall(Fn, {Name, Line, ConstantInt::get(IntTy, RecTy), Val1, Val2});
}

static void traceFunction(Function &F) {
  Instruction *I = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
	auto Int64Ty = Type::getInt64Ty(F.getContext());

	// void san_trace(char *name, int line, int record_ty, int64 val);
	insertTraceCall(F, I, ConstantInt::get(Int64Ty, 0), NULL, ENTRY_TY, false);

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			if (auto RI = dyn_cast<ReturnInst>(&Inst)) {
				Value *RetVal = RI->getReturnValue();
				if (!RetVal) {
					RetVal = ConstantInt::get(Int64Ty, 0);
				}
				insertTraceCall(F, RI, RetVal, NULL, EXIT_TY, false);
			}
			else if (auto ICmp = dyn_cast<ICmpInst>(&Inst)) {
				insertTraceCall(F, ICmp, ICmp, NULL, ICMP_TY, true);
			}
			else if (auto LI = dyn_cast<LoadInst>(&Inst)) {
				insertTraceCall(F, LI, LI, LI->getPointerOperand(), LOAD_TY, true);
			}
			else if (auto SI = dyn_cast<StoreInst>(&Inst)) {
				auto V = SI->getValueOperand();
				insertTraceCall(F, SI, V, SI->getPointerOperand(), STORE_TY, false);
			}
			else if (auto PI = dyn_cast<PtrToIntInst>(&Inst)) {
				insertTraceCall(F, PI, PI, NULL, PTR_TO_INT_TY, true);
			}
			else if (auto BO = dyn_cast<BinaryOperator>(&Inst)) {
        if (BO->getOpcode() == Instruction::Sub) {
					insertTraceCall(F, BO, BO, NULL, SUB_TY, true);
				}
			}
		}
	}
}

/// This is the main transformation entry point for a function.
bool FastTraceLegacyPass::runOnFunction(Function &F) {
	if (ClTrace) {
		traceFunction(F);
	}
	return true;
}
