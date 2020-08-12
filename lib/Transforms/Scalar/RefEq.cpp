//===- RefEqimizer.cpp - Optimize use of memcpy and friends -----------===//
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

#include "llvm/Transforms/Scalar/RefEq.h"
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
#include <algorithm>
#include <cassert>
#include <cstdint>
#include <utility>

using namespace llvm;

#define DEBUG_TYPE "referenceequal"

namespace {

//===----------------------------------------------------------------------===//
//                         MemCpyOptLegacyPass Pass
//===----------------------------------------------------------------------===//

namespace {

class RefEqLegacyPass : public FunctionPass {
  RefEqPass Impl;

public:
  static char ID; // Pass identification, replacement for typeid

  RefEqLegacyPass() : FunctionPass(ID) {
    initializeRefEqLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override;

private:
  // This transformation requires dominator postdominator info
  //void getAnalysisUsage(AnalysisUsage &AU) const override {
  //}
};

} // end anonymous namespace
}

char RefEqLegacyPass::ID = 0;

/// The public interface to this file...
FunctionPass *llvm::createRefEqPass() { return new RefEqLegacyPass(); }

INITIALIZE_PASS_BEGIN(RefEqLegacyPass, "refeq", "RefEq Optimization",
                      false, false)
INITIALIZE_PASS_END(RefEqLegacyPass, "refeq", "RefEq Optimization",
                    false, false)

static bool isPtrMask(Value *V) {
	auto I = dyn_cast<IntrinsicInst>(V);
	return (I && I->getIntrinsicID() == Intrinsic::ptrmask);
}


static Value* getNoInterior(Function &F, Instruction *I, Value *V)
{
	if (isa<PtrToIntInst>(V)) {
		auto VI = dyn_cast<PtrToIntInst>(V);
		if (isPtrMask(VI->getPointerOperand())) {
			return NULL;
		}
	}
	else if (isPtrMask(V)) {
		return NULL;
	}

	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);

#if 0
		auto LineTy = IRB.getInt32Ty(); //Line->getType();
		auto Name = IRB.CreateGlobalStringPtr(F.getParent()->getName());
		auto NameTy = Name->getType();

		Value *Op1 = V;
		Value *Op2 = V;
		auto Fn = F.getParent()->getOrInsertFunction("san_icmp", IRB.getVoidTy(), Op1->getType(), Op2->getType(), LineTy, NameTy);
		int LineNum = 0;
		if (F.getSubprogram() && I->getDebugLoc()) {
			//LineNum = I->getDebugLoc()->getLine();
		}

		LineNum = (LineNum << 16) | 0;
		auto *Line = ConstantInt::get(LineTy, LineNum);
		auto Call = IRB.CreateCall(Fn, {Op1, Op2, Line, Name});
		if (F.getSubprogram()) {
    	if (auto DL = I->getDebugLoc()) {
      	Call->setDebugLoc(DL);
			}
  	}
#endif


	Type *Ty = NULL;

	if (isa<PtrToIntInst>(V)) {
		Ty = V->getType();
		V = IRB.CreateIntToPtr(V, IRB.getInt8PtrTy());
	}
	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrinsic::ptrmask, {V->getType(), V->getType(), IRB.getInt64Ty()});
	V = IRB.CreateCall(TheFn, {V, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<48)-1)});
	if (Ty) {
		V = IRB.CreatePtrToInt(V, Ty);
	}
	return V;

	//auto VInt = IRB.CreatePtrToInt(V, IRB.getInt64Ty());
	//auto Interior = IRB.CreateAnd(VInt, (1ULL << 63) - 1);
	//return IRB.CreateIntToPtr(Interior, V->getType());
}

/*
static Value* getNoInterior(Function &F, Instruction *I, Value *V)
{
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);

	if (isa<PtrToIntInst>(V)) {
		return IRB.CreateAnd(V, (1ULL << 63) - 1);
	}

	auto VInt = IRB.CreatePtrToInt(V, IRB.getInt64Ty());
	auto Interior = IRB.CreateAnd(VInt, (1ULL << 63) - 1);
	return IRB.CreateIntToPtr(Interior, V->getType());
}
*/
static bool isPointerOperand(Value *V) {
  if (V->getType()->isPointerTy() || isa<PtrToIntInst>(V)) {
		return true;
	}
	auto CE = dyn_cast<ConstantExpr>(V);
	if (CE && CE->getOpcode() == Instruction::PtrToInt) {
		return true;
	}
	return false;
}

static void instrumentOtherPointerUsage(Function &F, DenseSet<Instruction*> &ICmpOrSub,
	const DataLayout &DL) {

	for (auto I : ICmpOrSub) {
		Value *Op1 = I->getOperand(0);
		Value *Op2 = I->getOperand(1);
		bool IsOp1Ptr = isPointerOperand(Op1);
		bool IsOp2Ptr = isPointerOperand(Op2);

		if (IsOp1Ptr) {
			if (!isa<AllocaInst>(Op1) && !isa<Constant>(Op1)) {
				Value *Base1 = GetUnderlyingObject(Op1, DL, 0);
				if (!isa<AllocaInst>(Base1)) {
					auto NoInt = getNoInterior(F, I, Op1);
					if (NoInt) {
						I->setOperand(0, NoInt);
					}
				}
			}
		}

		if (IsOp2Ptr) {
			if (!isa<AllocaInst>(Op2) && !isa<Constant>(Op2)) {
				Value *Base2 = GetUnderlyingObject(Op2, DL, 0);
				if (!isa<AllocaInst>(Base2)) {
					auto NoInt = getNoInterior(F, I, Op2);
					if (NoInt) {
						I->setOperand(1, NoInt);
					}
				}
			}
		}
	}
}

static bool isInteriorConstant(Value *V) {
	auto I = dyn_cast<ConstantExpr>(V);
	if (I) {
		V = I->getOperand(0);
	}
	//errs() << "Checking: " << *V << "\n";
	auto C = dyn_cast<ConstantInt>(V);
	if (!C) {
		return false;
	}
	//errs() << "Constant: " << C->getZExtValue() << "\n";
	return (C->getZExtValue() >> 48) > 0;
}

/// This is the main transformation entry point for a function.
bool RefEqLegacyPass::runOnFunction(Function &F) {
  const DataLayout &DL = F.getParent()->getDataLayout();
	DenseSet<Instruction*> ICmpOrSub;
	//dbgs() << "Before Ref::\n" << F << "\n";

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			if (auto Ret = dyn_cast<ICmpInst>(&Inst)) {
				//errs() << "Looking at " << *Ret << "\n";
				Value *Op1 = Ret->getOperand(0);
				Value *Op2 = Ret->getOperand(1);
				if (isInteriorConstant(Op1) || isInteriorConstant(Op2)) {
					continue;
				}
				if (isPointerOperand(Op1) || isPointerOperand(Op2)) {
					ICmpOrSub.insert(Ret);
				}
			}
			else if (auto BO = dyn_cast<BinaryOperator>(&Inst)) {
				if (BO->getOpcode() == Instruction::Sub) {
					//errs() << "Looking at " << *BO << "\n";
					Value *Op1 = BO->getOperand(0);
					Value *Op2 = BO->getOperand(1);
					if (isInteriorConstant(Op1) || isInteriorConstant(Op2)) {
						continue;
					}
					if (isPointerOperand(Op1) && isPointerOperand(Op2)) {
						ICmpOrSub.insert(BO);
					}
				}
			}
		}
	}
	instrumentOtherPointerUsage(F, ICmpOrSub, DL);
	//dbgs() << "After Ref::\n" << F << "\n";
	return true;
}
