add_llvm_component_library(LLVMCodeGen
  AggressiveAntiDepBreaker.cpp
  AllocationOrder.cpp
  Analysis.cpp
  AtomicExpandPass.cpp
  BasicTargetTransformInfo.cpp
  BranchFolding.cpp
  BranchRelaxation.cpp
  BreakFalseDeps.cpp
  BuiltinGCs.cpp
  CalcSpillWeights.cpp
  CallingConvLower.cpp
  CFGuardLongjmp.cpp
  CFIInstrInserter.cpp
  CodeGen.cpp
  CodeGenPrepare.cpp
  CriticalAntiDepBreaker.cpp
  DeadMachineInstructionElim.cpp
  DetectDeadLanes.cpp
  DFAPacketizer.cpp
  DwarfEHPrepare.cpp
  EarlyIfConversion.cpp
  EdgeBundles.cpp
  ExecutionDomainFix.cpp
  ExpandMemCmp.cpp
  ExpandPostRAPseudos.cpp
  ExpandReductions.cpp
  FaultMaps.cpp
  FEntryInserter.cpp
  FinalizeISel.cpp
  FuncletLayout.cpp
  GCMetadata.cpp
  GCMetadataPrinter.cpp
  GCRootLowering.cpp
  GCStrategy.cpp
  GlobalMerge.cpp
  HardwareLoops.cpp
  IfConversion.cpp
  ImplicitNullChecks.cpp
  IndirectBrExpandPass.cpp
  InlineSpiller.cpp
  InterferenceCache.cpp
  InterleavedAccessPass.cpp
  InterleavedLoadCombinePass.cpp
  IntrinsicLowering.cpp
  LatencyPriorityQueue.cpp
  LazyMachineBlockFrequencyInfo.cpp
  LexicalScopes.cpp
  LiveDebugValues.cpp
  LiveDebugVariables.cpp
  LiveIntervals.cpp
  LiveInterval.cpp
  LiveIntervalUnion.cpp
  LivePhysRegs.cpp
  LiveRangeCalc.cpp
  LiveRangeEdit.cpp
  LiveRangeShrink.cpp
  LiveRegMatrix.cpp
  LiveRegUnits.cpp
  LiveStacks.cpp
  LiveVariables.cpp
  LLVMTargetMachine.cpp
  LocalStackSlotAllocation.cpp
  LoopTraversal.cpp
  LowLevelType.cpp
  LowerEmuTLS.cpp
  MachineBasicBlock.cpp
  MachineBlockFrequencyInfo.cpp
  MachineBlockPlacement.cpp
  MachineBranchProbabilityInfo.cpp
  MachineCombiner.cpp
  MachineCopyPropagation.cpp
  MachineCSE.cpp
  MachineDominanceFrontier.cpp
  MachineDominators.cpp
  MachineFrameInfo.cpp
  MachineFunction.cpp
  MachineFunctionPass.cpp
  MachineFunctionPrinterPass.cpp
  MachineInstrBundle.cpp
  MachineInstr.cpp
  MachineLICM.cpp
  MachineLoopInfo.cpp
  MachineLoopUtils.cpp
  MachineModuleInfo.cpp
  MachineModuleInfoImpls.cpp
  MachineOperand.cpp
  MachineOptimizationRemarkEmitter.cpp
  MachineOutliner.cpp
  MachinePipeliner.cpp
  MachinePostDominators.cpp
  MachineRegionInfo.cpp
  MachineRegisterInfo.cpp
  MachineScheduler.cpp
  MachineSink.cpp
  MachineSizeOpts.cpp
  MachineSSAUpdater.cpp
  MachineTraceMetrics.cpp
  MachineVerifier.cpp
  ModuloSchedule.cpp
  PatchableFunction.cpp
  MIRPrinter.cpp
  MIRPrintingPass.cpp
  MacroFusion.cpp
  NonRelocatableStringpool.cpp
  OptimizePHIs.cpp
  ParallelCG.cpp
  PeepholeOptimizer.cpp
  PHIElimination.cpp
  PHIEliminationUtils.cpp
  PostRAHazardRecognizer.cpp
  PostRASchedulerList.cpp
  PreISelIntrinsicLowering.cpp
  ProcessImplicitDefs.cpp
  PrologEpilogInserter.cpp
  PseudoSourceValue.cpp
  ReachingDefAnalysis.cpp
  RegAllocBase.cpp
  RegAllocBasic.cpp
  RegAllocFast.cpp
  RegAllocGreedy.cpp
  RegAllocPBQP.cpp
  RegisterClassInfo.cpp
  RegisterCoalescer.cpp
  RegisterPressure.cpp
  RegisterScavenging.cpp
  RenameIndependentSubregs.cpp
  MIRVRegNamerUtils.cpp
  MIRNamerPass.cpp
  MIRCanonicalizerPass.cpp
  RegisterUsageInfo.cpp
  RegUsageInfoCollector.cpp
  RegUsageInfoPropagate.cpp
  ResetMachineFunctionPass.cpp
  SafeStack.cpp
  FastSafeStack.cpp
	FastAddress.cpp
  SafeStackColoring.cpp
  SafeStackLayout.cpp
  ScalarizeMaskedMemIntrin.cpp
  ScheduleDAG.cpp
  ScheduleDAGInstrs.cpp
  ScheduleDAGPrinter.cpp
  ScoreboardHazardRecognizer.cpp
  ShadowStackGCLowering.cpp
  ShrinkWrap.cpp
  SjLjEHPrepare.cpp
  SlotIndexes.cpp
  SpillPlacement.cpp
  SplitKit.cpp
  StackColoring.cpp
  StackMapLivenessAnalysis.cpp
  StackMaps.cpp
  StackProtector.cpp
  StackSlotColoring.cpp
  SwiftErrorValueTracking.cpp
  SwitchLoweringUtils.cpp
  TailDuplication.cpp
  TailDuplicator.cpp
  TargetFrameLoweringImpl.cpp
  TargetInstrInfo.cpp
  TargetLoweringBase.cpp
  TargetLoweringObjectFileImpl.cpp
  TargetOptionsImpl.cpp
  TargetPassConfig.cpp
  TargetRegisterInfo.cpp
  TargetSchedule.cpp
  TargetSubtargetInfo.cpp
  TypePromotion.cpp
  TwoAddressInstructionPass.cpp
  UnreachableBlockElim.cpp
  ValueTypes.cpp
  VirtRegMap.cpp
  WasmEHPrepare.cpp
  WinEHPrepare.cpp
  XRayInstrumentation.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/CodeGen
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/CodeGen/PBQP

  LINK_LIBS ${LLVM_PTHREAD_LIB}

  DEPENDS
  intrinsics_gen
  )

add_subdirectory(SelectionDAG)
add_subdirectory(AsmPrinter)
add_subdirectory(MIRParser)
add_subdirectory(GlobalISel)
