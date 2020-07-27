//===- FastAddress.cpp --------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This pass implements the stack-coloring optimization that looks for
// lifetime markers machine instructions (LIFESTART_BEGIN and LIFESTART_END),
// which represent the possible lifetime of stack slots. It attempts to
// merge disjoint stack slots and reduce the used stack space.
// NOTE: This pass is not StackSlotColoring, which optimizes spill slots.
//
// TODO: In the future we plan to improve stack coloring in the following ways:
// 1. Allow merging multiple small slots into a single larger slot at different
//    offsets.
// 2. Merge this pass with StackSlotColoring and allow merging of allocas with
//    spill slots.
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/CodeGen/LiveInterval.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFrameInfo.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/CodeGen/MachineOperand.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/SelectionDAGNodes.h"
#include "llvm/CodeGen/SlotIndexes.h"
#include "llvm/CodeGen/TargetOpcodes.h"
#include "llvm/CodeGen/WinEHFuncInfo.h"
#include "llvm/Config/llvm-config.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Use.h"
#include "llvm/IR/Value.h"
#include "llvm/InitializePasses.h"
#include "llvm/Pass.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Compiler.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <cassert>
#include <limits>
#include <memory>
#include <utility>

using namespace llvm;

#define DEBUG_TYPE "fast-address"


namespace {

/// FastAddress - A machine pass for merging disjoint stack allocations,
/// marked by the LIFETIME_START and LIFETIME_END pseudo instructions.
class FastAddress : public MachineFunctionPass {
  MachineFunction *MF;
public:
  static char ID;

  FastAddress() : MachineFunctionPass(ID) {
    initializeFastAddressPass(*PassRegistry::getPassRegistry());
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override;
  bool runOnMachineFunction(MachineFunction &Func) override;
};

} // end anonymous namespace

char FastAddress::ID = 0;

char &llvm::FastAddressID = FastAddress::ID;

INITIALIZE_PASS_BEGIN(FastAddress, DEBUG_TYPE,
                      "Fast address machine pass", false, false)
INITIALIZE_PASS_END(FastAddress, DEBUG_TYPE,
                    "Fast address machine pass", false, false)

void FastAddress::getAnalysisUsage(AnalysisUsage &AU) const {
  MachineFunctionPass::getAnalysisUsage(AU);
}

bool FastAddress::runOnMachineFunction(MachineFunction &Func) {
  MF = &Func;
  return true;
}
