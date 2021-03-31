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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/DebugInfoMetadata.h"
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
	bool FirstCall;

  RefEqLegacyPass(bool First = false) : FunctionPass(ID) {
		FirstCall = First;
    initializeRefEqLegacyPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override;

private:
  // This transformation requires dominator postdominator info
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
  }
};

} // end anonymous namespace
}

char RefEqLegacyPass::ID = 0;

/// The public interface to this file...
FunctionPass *llvm::createRefEqPass(bool FirstCall) { return new RefEqLegacyPass(FirstCall); }

INITIALIZE_PASS_BEGIN(RefEqLegacyPass, "refeq", "RefEq Optimization",
                      false, false)
INITIALIZE_PASS_DEPENDENCY(TargetLibraryInfoWrapperPass)
INITIALIZE_PASS_END(RefEqLegacyPass, "refeq", "RefEq Optimization",
                    false, false)

#if 0
static Value* getLineNo(Function &F, Instruction *I, Type *LineTy) {
	int LineNum = 0;
	if (F.getSubprogram() && I->getDebugLoc()) {
		LineNum = I->getDebugLoc()->getLine();
	}
	return ConstantInt::get(LineTy, LineNum);
}
#endif

static void setBoundsForArgv(Function &F)
{
	if (F.getName() == "main" && F.arg_size() > 0) {
		assert(F.arg_size() > 1 && F.arg_size() <= 3);
		auto argc = F.getArg(0);
		auto argv = F.getArg(1);
		auto IntTy = argc->getType();
		auto Fn = F.getParent()->getOrInsertFunction("san_copy_argv", argv->getType(), IntTy, argv->getType());
  	Instruction *Entry = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
		auto Call = CallInst::Create(Fn, {argc, argv}, "", Entry);
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

#if 0

#define ENTRY_TY 0
#define EXIT_TY 1
#define ICMP_TY 2
#define LOAD_TY 3
#define STORE_TY 4
#define PTR_TO_INT_TY 5
#define	SUB_TY 6

static void insertTraceCall(Function &F, Instruction *I, Value *Val, int RecTy, bool InsertAfter)
{
	auto InsertPt = (InsertAfter) ? I->getNextNode() : I;
	IRBuilder<> IRB(InsertPt);
	auto IntTy = IRB.getInt32Ty();
	FunctionCallee Fn;
	auto M = F.getParent();
	auto Name = IRB.CreateGlobalStringPtr(F.getName());
	Value *Line = getLineNo(F, I, IntTy);

	if (Val->getType()->isPointerTy()) {
		Val = ConstantInt::get(IntTy, 0);
	}
	else if (Val->getType()->isIntegerTy()) {
		Val = IRB.CreateZExtOrTrunc(Val, IRB.getInt64Ty());
	}

	Fn = M->getOrInsertFunction("san_trace", IRB.getVoidTy(), Name->getType(), IntTy, IntTy, Val->getType());
	IRB.CreateCall(Fn, {Name, Line, ConstantInt::get(IntTy, RecTy), Val});
}

static void traceFunction(Function &F) {
  Instruction *I = dyn_cast<Instruction>(F.begin()->getFirstInsertionPt());
	auto Int64Ty = Type::getInt64Ty(F.getContext());

	// void san_trace(char *name, int line, int record_ty, int64 val);
	insertTraceCall(F, I, ConstantInt::get(Int64Ty, 0), ENTRY_TY, false);

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			if (auto RI = dyn_cast<ReturnInst>(&Inst)) {
				Value *RetVal = RI->getReturnValue();
				if (!RetVal) {
					RetVal = ConstantInt::get(Int64Ty, 0);
				}
				insertTraceCall(F, RI, RetVal, EXIT_TY, false);
			}
			else if (auto ICmp = dyn_cast<ICmpInst>(&Inst)) {
				insertTraceCall(F, ICmp, ICmp, ICMP_TY, true);
			}
			else if (auto LI = dyn_cast<LoadInst>(&Inst)) {
				insertTraceCall(F, LI, LI, LOAD_TY, true);
			}
			else if (auto SI = dyn_cast<StoreInst>(&Inst)) {
				auto V = SI->getValueOperand();
				insertTraceCall(F, SI, V, STORE_TY, false);
			}
			else if (auto PI = dyn_cast<PtrToIntInst>(&Inst)) {
				insertTraceCall(F, PI, PI, PTR_TO_INT_TY, true);
			}
			else if (auto BO = dyn_cast<BinaryOperator>(&Inst)) {
        if (BO->getOpcode() == Instruction::Sub) {
					insertTraceCall(F, BO, BO, SUB_TY, true);
				}
			}
		}
	}
}

#endif

static bool isPtrMask(Value *V) {
	auto I = dyn_cast<IntrinsicInst>(V);
	return (I &&
		(I->getIntrinsicID() == Intrinsic::ptrmask ||
		 I->getIntrinsicID() == Intrinsic::ptrmask1));
}

static Value* getNoInterior1(Function &F, Instruction *I, Value *V)
{
	IRBuilder<> IRB(I->getParent());
	IRB.SetInsertPoint(I);
	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrinsic::ptrmask1, {V->getType(), V->getType(), IRB.getInt64Ty()});
	V = IRB.CreateCall(TheFn, {V, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<48)-1)});
	return V;
}

static Value* getNoInterior(Function &F, Instruction *I, Value *V)
{
	if (isPtrMask(V)) {
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

	auto Intrin = (isa<PtrToIntInst>(V)) ? Intrinsic::ptrmask1 : Intrinsic::ptrmask;

	Function *TheFn =
      Intrinsic::getDeclaration(F.getParent(), Intrin, {V->getType(), V->getType(), IRB.getInt64Ty()});
	V = IRB.CreateCall(TheFn, {V, ConstantInt::get(IRB.getInt64Ty(), (1ULL<<48)-1)});

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

static bool maybePointer(Value *V)
{
	auto II = dyn_cast<IntrinsicInst>(V);
  if (II && II->getIntrinsicID() == Intrinsic::ptrmask1) {
		return false;
	}
	V = V->stripPointerCasts();
	auto LI = dyn_cast<LoadInst>(V);
	if (LI) {
		auto PI = LI->getPointerOperand();
		PI = PI->stripPointerCasts();
		auto Ty = PI->getType();
		if (Ty->isPointerTy() && Ty->getPointerElementType()->isPointerTy()) {
			return true;
		}
	}
	else if (isa<PtrToIntInst>(V)) {
		return true;
	}
  for (Use &UI : V->uses()) {
  	auto I = dyn_cast<IntToPtrInst>(UI.getUser());
		if (I) {
			return true;
		}
	}
	return false;
}

static void instrumentOtherPointerUsage(Function &F, DenseSet<Instruction*> &ICmpOrSub,
	DenseSet<Instruction*> &GEPs,
	const DataLayout &DL) {

	for (auto I : ICmpOrSub) {
		Value *Op1 = I->getOperand(0);
		Value *Op2 = I->getOperand(1);
		bool IsOp1Ptr = isPointerOperand(Op1);
		bool IsOp2Ptr = isPointerOperand(Op2);

		if (IsOp1Ptr) {
			if (!isa<AllocaInst>(Op1) && !isa<Constant>(Op1)) {
				Value *Base1 = GetUnderlyingObject(Op1, DL, 0);
				if (!isa<AllocaInst>(Base1) && !isa<GlobalVariable>(Base1)) {
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
				if (!isa<AllocaInst>(Base2) && !isa<GlobalVariable>(Base2)) {
					auto NoInt = getNoInterior(F, I, Op2);
					if (NoInt) {
						I->setOperand(1, NoInt);
					}
				}
			}
		}
	}

	for (auto I : GEPs) {
		for (unsigned i = 0; i < I->getNumOperands(); i++) {
			Value *Op = I->getOperand(i);
			if (!isa<Constant>(Op) && Op->getType()->isIntegerTy()) {
				if (maybePointer(Op)) {
					Value *V = getNoInterior1(F, I, Op);
					I->setOperand(i, V);
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

static void insertCheck1(CallInst *CI, int Idx)
{
	auto Len = CI->getArgOperand(Idx);
	assert(Len->getType()->isIntegerTy());
	IRBuilder<> IRB(CI);

	if (!isa<ConstantInt>(Len)) {
  	Value *ValidLen = IRB.CreateICmpNE(Len, Constant::getNullValue(Len->getType()));
  	Instruction *Term = SplitBlockAndInsertIfThen(ValidLen, CI, false);
		CI->removeFromParent();
		CI->insertBefore(Term);
	}
	else {
		if (cast<ConstantInt>(Len)->getZExtValue() == 0) {
			CI->eraseFromParent();
		}
	}
}

static Value* getReturnValue(CallInst *CI, LibFunc Func)
{
	switch (Func) {
  	case LibFunc_strncpy:
  	case LibFunc_strncat:
  	case LibFunc_stpncpy:
			return CI->getArgOperand(0);
  	case LibFunc_bcopy:
			return NULL;

  	case LibFunc_strncmp:
  	case LibFunc_strncasecmp:
  	case LibFunc_memcmp:
  	case LibFunc_memchr:
  	case LibFunc_memrchr:
  	case LibFunc_bcmp:
  	case LibFunc_bzero:
			return Constant::getNullValue(CI->getType());
		default:
			assert(0);
	}
	return NULL;
}

static void insertCheck2(Function &F, CallInst *CI, LibFunc Func, const TargetLibraryInfo *TLI)
{
	if (Func == LibFunc_strcpy) {
  	const DataLayout &DL = F.getParent()->getDataLayout();
		auto Ptr = CI->getArgOperand(1);
		auto Dst = CI->getArgOperand(0);
		IRBuilder<> IRB(CI);
		auto Len = emitStrLen(Ptr, IRB, DL, TLI);
		Len = IRB.CreateAdd(Len, ConstantInt::get(Len->getType(), 1));
		CallInst *NewCI = IRB.CreateMemCpy(Dst,
			Align::None(), Ptr, Align::None(), Len);
  	NewCI->setAttributes(CI->getAttributes());
		CI->replaceAllUsesWith(Dst);
		CI->eraseFromParent();
		return;
	}

	int LenIdx = TLI->getLengthArgument(Func);
	if (LenIdx == -1) {
		return;
	}
	auto Len = CI->getArgOperand(LenIdx);

	if (isa<ConstantInt>(Len)) {
		auto Sz = cast<ConstantInt>(Len)->getZExtValue();
		if (Sz == 0) {
			auto Ret = getReturnValue(CI, Func);
			if (Ret) {
				assert(CI->getType() == Ret->getType());
				CI->replaceAllUsesWith(Ret);
			}
			CI->eraseFromParent();
			return;
		}
	}
	else {
		IRBuilder<> IRB(CI);
		auto *NextInst = CI->getNextNode();
		auto OrigBlock = CI->getParent();
  	Value *ValidLen = IRB.CreateICmpNE(Len, Constant::getNullValue(Len->getType()));
  	Instruction *Term = SplitBlockAndInsertIfThen(ValidLen, CI, false);
		CI->removeFromParent();
		CI->insertBefore(Term);

		auto IfBlock = Term->getParent();

		auto Ret = getReturnValue(CI, Func);
		if (Ret) {
			assert(CI->getType() == Ret->getType());
			IRB.SetInsertPoint(NextInst);
  		PHINode *PHI = IRB.CreatePHI(CI->getType(), 2);
			CI->replaceAllUsesWith(PHI);
			PHI->addIncoming(Ret, OrigBlock);
			PHI->addIncoming(CI, IfBlock);
		}
	}
}

static void checkAllMemIntrinsics(Function &F, const TargetLibraryInfo *TLI)
{
	DenseSet<MemIntrinsic*> MISet;
	DenseSet<std::pair<CallInst*, unsigned>> CallSet;

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			auto MI = dyn_cast<MemIntrinsic>(&Inst);
			if (MI) {
				MISet.insert(MI);
			}
			else {
				LibFunc Func;
				auto CS = dyn_cast<CallInst>(&Inst);
				if (CS && TLI->getLibFunc(ImmutableCallSite(CS), Func)) {
					CallSet.insert(std::make_pair(CS, Func));
				}
			}
		}
	}

	for (auto MI : MISet) {
		insertCheck1(MI, 2);
	}

	for (auto Iter : CallSet) {
		insertCheck2(F, Iter.first, (LibFunc)Iter.second, TLI);
	}
}

static void replaceLibcalls(Function &F, const TargetLibraryInfo *TLI)
{
	//DenseSet<CallInst*> ShmSet;

  for (auto &BB : F) {
    for (auto &Inst : BB) {
			auto CS = dyn_cast<CallInst>(&Inst);
			if (CS && CS->getCalledFunction()) {
				auto Name = CS->getCalledFunction()->getName();
				if (Name == "__ctype_b_loc") {
					CS->getCalledFunction()->setName("___ctype_b_loc");
				}
				else if (Name == "mmap") {
					CS->getCalledFunction()->setName("san_mmap");
				}
				else if (Name == "unmap") {
					CS->getCalledFunction()->setName("san_unmmap");
				}
				else if (Name == "sigaction") {
					CS->getCalledFunction()->setName("san_sigaction");
				}
				/*else if (Name == "shm_open") {
					ShmSet.insert(CS);
				}
				else if (Name == "shmget") {
					ShmSet.insert(CS);
				}*/
			}
		}
	}
	//auto M = F.getParent();

#if 0
	for (auto MM : MmapSet) {
		IRBuilder<> IRB(MM);
		auto CI = IRB.CreateIntToPtr(ConstantInt::get(IRB.getInt64Ty(), -1), IRB.getInt8PtrTy());

		//auto Len = MM->getArgOperand(1);
		//auto MallocFn = M->getOrInsertFunction("calloc", IRB.getInt8PtrTy(), IRB.getInt64Ty(), IRB.getInt64Ty());
		//auto CI = IRB.CreateCall(MallocFn, {ConstantInt::get(IRB.getInt64Ty(), 1), Len});
		MM->replaceAllUsesWith(CI);
		MM->eraseFromParent();
	}

	for (auto MM : ShmSet) {
		MM->replaceAllUsesWith(ConstantInt::get(MM->getType(), -1));
		MM->eraseFromParent();
	}

	/*for (auto MM : MunmapSet) {
		CallInst::CreateFree(MM->getArgOperand(0), MM);
		MM->eraseFromParent();
	}*/
#endif
}

/// This is the main transformation entry point for a function.
bool RefEqLegacyPass::runOnFunction(Function &F) {
  const TargetLibraryInfo *TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
  const DataLayout &DL = F.getParent()->getDataLayout();
	DenseSet<Instruction*> ICmpOrSub;
	DenseSet<Instruction*> GEPs;

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
			else if (auto GEP = dyn_cast<GetElementPtrInst>(&Inst)) {
				GEPs.insert(GEP);
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
	instrumentOtherPointerUsage(F, ICmpOrSub, GEPs, DL);
	if (FirstCall) {
		setBoundsForArgv(F);
		checkAllMemIntrinsics(F, TLI);
		replaceLibcalls(F, TLI);
	}
	return true;
}
