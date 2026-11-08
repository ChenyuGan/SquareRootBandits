/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalVectorInsertion

/-!
# Install the actual first collection renewal sample

For the first collection sampler call, identify the actual renewed checked
sample, its successful local assignment start, the clocked register
installation, and the pre-choice physical selection. The physical post-choice
operation remains the literal recorder/service/confirmation/finish computation.

Sources: `sources/zip4/manuscript/06_interruptions.tex:40-69,399-423`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-215`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalSampleInstallation

open ConstructorDimensions
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalFibreExtension
open ReferenceFirstCollectionRenewalVectorInsertion
open ReferenceActivePhysicalStep
open CoordinatorRoundDispatch
open CoordinatorPhaseClock
open LaterAssignmentStartOperation
open LaterAssignmentStartMeasurability
open AssignmentScoreReconstruction
open CoordinatorAssignmentRegisterInstall
open AssignmentParameterFibreKernel
open CheckedAssignmentSample
open CoordinatorLiveChoiceRecorderStep
open CoordinatorLocalArmChoice

private theorem callPending_eq_empty
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {u t : Fin p.T}
    {z : RenewalCallSource rate rewards C_star C_h u t}
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    d.ledger.pending = ∅ := by
  let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
  have hparam : CoordinatorPhaseClock.proposalParameterValid p rate.eta.val := by
    simpa [ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput] using d.core.clock_parameter_valid
  have hclock : CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock := by
    simpa [clock, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput,
      ReferenceActivePhysicalStep.collectionClock] using d.core.clock_registers_valid
  have htime : CoordinatorPhaseClock.startRoundTimeValid p d.record.input.time clock := by
    simpa [clock, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput,
      ReferenceActivePhysicalStep.collectionClock] using d.core.clock_start_time_valid
  have hdet : CoordinatorPhaseClock.detectCutoff clock d.record.input.time =
      .ok .noCutoff := by
    simp [clock, ReferenceActivePhysicalStep.collectionClock,
      CoordinatorPhaseClock.detectCutoff]
  have hstartEq := d.clock_eq
  change CoordinatorPhaseClock.startRound p rate.eta.val d.record.input.time
      clock d.ledger.pending = .ok d.started at hstartEq
  by_cases hready : CoordinatorPhaseClock.sourceStartTest
      clock.sigma clock.u d.record.input.time d.ledger.pending
  · have hready' : CoordinatorPhaseClock.sourceStartTest
        (some d.old.sigma) (some u) d.record.input.time d.ledger.pending := by
      simpa [clock, ReferenceActivePhysicalStep.collectionClock] using hready
    exact (CoordinatorPhaseClock.sourceStartTest_collection_iff
      d.old.sigma u d.record.input.time d.ledger.pending).mp hready' |>.2
  · simp [CoordinatorPhaseClock.startRound, hparam, hclock, htime, hdet, hready]
      at hstartEq
    have hfield := congrArg CoordinatorPhaseClock.StartRoundResult.assignmentStart
      (Except.ok.inj hstartEq)
    rw [d.instruction_eq] at hfield
    cases hfield

private def canonicalConsistency
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {u t : Fin p.T}
    {z : RenewalCallSource rate rewards C_star C_h u t}
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    LaterAssignmentStartOperation.LocalConsistency
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved).payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
          rate u d.record.input d.old d.ledger d.saved) d.core.payload_n_eq) := by
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell := CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  exact {
    oldStart_eq := by
      simpa [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        CoordinatorRecorderComplementBridge.sourceStart, ell,
        CoordinatorRoundDispatch.collectionOperationLedger] using d.core.ledger_sigma_eq.symm
    oldAssignment_eq := fun i => by
      simpa [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ell, CoordinatorRoundDispatch.collectionOperationLedger] using
        (d.core.assignment_eq i).symm
    oldFreezeAt := d.ledger.freezeAt
    oldFreezeAt_eq := rfl }

private def collectionDispatcherConsistency
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x) :
    LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq) := {
  oldStart_eq := by
    simpa [CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRoundDispatch.collectionOperationLedger] using core.ledger_sigma_eq.symm
  oldAssignment_eq := by
    intro i
    simpa [CoordinatorRoundDispatch.collectionOperationLedger] using
      (core.assignment_eq i).symm
  oldFreezeAt := x.ledger.freezeAt
  oldFreezeAt_eq := rfl }

private theorem collectionDispatcherConsistency_eq
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)) :
    collectionDispatcherConsistency x core = consistent := by
  cases consistent with
  | mk hstart hassignment oldFreeze hfreeze =>
      have hfreeze' : oldFreeze = x.ledger.freezeAt := by
        simpa [CoordinatorRoundDispatch.collectionOperationLedger] using hfreeze
      subst oldFreeze
      rfl

private theorem dispatchCollection_laterChosen
    {p : ConstructorDimensions.Parameters}
    (x : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid x)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time x.clock
      x.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq))
    (output : LaterAssignmentStartOperation.SuccessfulStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row)
    (hlocal : output.localConsistency = consistent)
    (htime : instruction.time = x.time)
    (hfreeze : x.clock.g = output.localConsistency.oldFreezeAt)
    (hpending : x.ledger.pending = ∅)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart x.payload
      (CoordinatorRoundDispatch.collectionOperationLedger x core.payload_n_eq)
      instruction x.row consistent = .success output hlocal) :
    let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
      priorClock := x.clock
      pending := x.ledger.pending
      proposalParameterValid := core.clock_parameter_valid
      priorClockValid := core.clock_registers_valid
      startTimeValid := by rw [htime]; exact core.clock_start_time_valid
      result := started
      startRound_eq := by rw [htime]; exact hstart
      assignmentStart_eq := hassignment
      priorSigma_eq := core.clock_sigma_eq
      priorGrid_eq_freezeAt := hfreeze }
    let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
    (∀ i, installation.retainedBaseScore i ≤ p.T * D p) →
    CoordinatorLocalArmChoice.ChoiceInputsValid installation.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      instruction.time installation.registers.complementWeights →
    installation.registers.complementEnvelopeValid →
    ∃ selection : CoordinatorRoundDispatch.ArmSelection installation.registers.payload
      started instruction.time installation.registers.complementWeights x.row,
      CoordinatorRoundDispatch.dispatchCollection x =
        .laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selection := by
  classical
  dsimp only
  intro hbase hchoice henvelope
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hnotpending : ¬ x.ledger.pending.Nonempty := by
    rw [hpending]
    simp
  have hconsistent := collectionDispatcherConsistency_eq x core consistent
  cases hconsistent
  unfold CoordinatorRoundDispatch.dispatchCollection
  split
  · rename_i failure hactual
    rw [hstart] at hactual
    cases hactual
  · rename_i actual hactual
    have heq : actual = started := Except.ok.inj (hactual.symm.trans hstart)
    subst actual
    simp [core, hnotpending]
    split
    · rename_i hmissing
      rw [hassignment] at hmissing
      cases hmissing
    · rename_i actualInstruction hactualInstruction
      have hi : actualInstruction = instruction :=
        Option.some.inj (hactualInstruction.symm.trans hassignment)
      subst actualInstruction
      simp only [collectionDispatcherConsistency] at hlater
      split
      · rename_i actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualArm actualReason hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i set hactualLater
        rw [hlater] at hactualLater
        cases hactualLater
      · rename_i actualOutput actualLocal hactualLater
        have heq := hactualLater.symm.trans hlater
        cases heq
        rw [ite_eq_left hbase]
        rw [dite_eq_left hchoice]
        rw [ite_eq_left henvelope]
        have hclockEquations := CoordinatorPhaseClock.startRound_assignment_effect p
          x.etaReal x.time x.clock x.ledger.pending started instruction
          core.clock_parameter_valid core.clock_registers_valid
          core.clock_start_time_valid hstart hassignment
        rcases hclockEquations with ⟨htimeActual, _, hnewSigma, _, _, _, _, _⟩
        have hgrid : CoordinatorPhaseClock.clockGridDomain p started.clock := by
          simpa [hnewSigma] using started.gridDomain
        have hgrid' := hgrid
        simp only [CoordinatorPhaseClock.clockGridDomain, hnewSigma] at hgrid'
        have hboundary : started.clock.g ≤ p.T + 1 := hgrid'.2
        have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
          installation.registers.payload started.pending
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          instruction.time installation.registers.complementWeights x.row hchoice
        split
        · rename_i hselected
          exact False.elim (hnonempty hselected)
        · rename_i arm hselected
          refine ⟨{
            arm := arm
            choiceInputsValid := hchoice
            recorderBoundaryValid := hboundary
            armChoice_eq := hselected }, ?_⟩
          rfl

private theorem actual_call_witnesses
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ} {u t : Fin p.T}
    {z : RenewalCallSource rate rewards C_star C_h u t}
    (d : ActualRenewalCall rate rewards C_star C_h u t z) :
    let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
      rate u d.record.input d.old d.ledger d.saved
    let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
      CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
    let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
      x.payload ell d.instruction d.out d.reconstruction_eq
    let v := LaterAssignmentStartOperation.ownAssignmentVector
      d.record.input.row d.instruction.time
    let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
    ∃ consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell,
      ∃ output : LaterAssignmentStartOperation.SuccessfulStart
        x.payload ell d.instruction x.row,
        ∃ hlocal : output.localConsistency = consistent,
          LaterAssignmentStartOperation.laterAssignmentStart
              x.payload ell d.instruction x.row consistent =
            .success output hlocal ∧
          output.assignmentVector = v ∧
          output.reconstruction = d.out ∧
          AssignmentParameterFibreKernel.successfulSlowSet p par v =
            some output.slowSet ∧
          output.payload.slowSet = output.slowSet ∧
          let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
              output := {
            priorClock := x.clock
            pending := x.ledger.pending
            proposalParameterValid := d.core.clock_parameter_valid
            priorClockValid := d.core.clock_registers_valid
            startTimeValid := by
              simpa only [x,
                ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                ReferenceActivePhysicalStep.collectionInput,
                d.instruction_time] using d.core.clock_start_time_valid
            result := d.started
            startRound_eq := by
              simpa only [x,
                ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                ReferenceActivePhysicalStep.collectionInput,
                ReferenceActivePhysicalStep.collectionClock,
                d.instruction_time] using d.clock_eq
            assignmentStart_eq := d.instruction_eq
            priorSigma_eq := d.core.clock_sigma_eq
            priorGrid_eq_freezeAt := by
              calc
                x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
                _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
          let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
          installed.registers.payload = output.payload ∧
          installed.assignmentVector = v ∧
          installed.reconstruction = d.out ∧
          installed.registers.payload.anchor =
            AssignmentScoreReconstruction.currentWeight d.out ∧
          (∀ a, installed.registers.payload.queues a =
            AssignmentScoreReconstruction.initialQueue d.out a) ∧
          (∀ i, installed.retainedBaseScore i =
            AssignmentScoreReconstruction.sourceScore d.out
              (output.payload.assignment.assigned i)) ∧
          ∃ selection : CoordinatorRoundDispatch.ArmSelection
              installed.registers.payload d.started d.instruction.time
              installed.registers.complementWeights d.record.input.row,
            CoordinatorLocalArmChoice.coordinatorArmChoice
                installed.registers.payload d.started.pending
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                d.instruction.time installed.registers.complementWeights d.record.input.row =
              some selection.arm ∧
            CoordinatorRoundDispatch.dispatchCollection x =
              .laterChosen d.core consistent d.started d.clock_eq d.instruction
                d.instruction_eq output hlocal clockData installed selection ∧
            d.record.output.preparation = ReferenceActivePhysicalStep.prepare d.record.input ∧
            d.record.output.preparation.coordinator =
              .collection d.old d.ledger clock u
                (CoordinatorRoundDispatch.dispatchCollection x) ∧
            d.record.output.preparation.coordinator.arm = selection.arm ∧
            d.record.output.coordinator =
              ReferenceActivePhysicalStep.livePostChoice
                (ReferenceActivePhysicalStep.prepare d.record.input)
                installed.registers installed.ownedRegisters installed.retainedBaseScore d.started ∧
            d.record.output.next.coordinator =
              (ReferenceActivePhysicalStep.livePostChoice
                (ReferenceActivePhysicalStep.prepare d.record.input)
                installed.registers installed.ownedRegisters installed.retainedBaseScore
                d.started).configuration := by
  classical
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
    CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
    x.payload ell d.instruction d.out d.reconstruction_eq
  let v := LaterAssignmentStartOperation.ownAssignmentVector
    d.record.input.row d.instruction.time
  let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
  dsimp only [ell, par, v, clock]
  let consistent := canonicalConsistency d
  let hrec := d.reconstruction_eq
  have hpending : d.ledger.pending = ∅ := callPending_eq_empty d
  have hcurrentPos :=
    (LaterAssignmentStartMeasurability.successfulLawSelection
      x.payload ell d.instruction d.out hrec).currentWeightPos
  have hlaw := LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
    x.payload ell d.instruction d.out hrec d.renewal
  have hparams : par =
      ((CanonicalAssignmentVector.productQNormalizedMass p.two_le_m p.m_lt_K
        (AssignmentScoreReconstruction.currentWeight d.out) hcurrentPos).weight,
        AssignmentScoreReconstruction.currentWeight d.out) := by
    apply Prod.ext
    · funext S
      rw [hlaw.2 S]
      rfl
    · exact hlaw.1
  have hsampled : CheckedAssignmentSample.checkedAssignmentSample p par.1 par.2 v =
      .sampled (CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K
        (AssignmentScoreReconstruction.currentWeight d.out)
        (AssignmentScoreReconstruction.currentWeight d.out)
        hcurrentPos hcurrentPos v) := by
    rw [hparams]
    exact CheckedAssignmentSample.productQ_checkedAssignmentSample_eq_sampler
      p (AssignmentScoreReconstruction.currentWeight d.out)
      (AssignmentScoreReconstruction.currentWeight d.out)
      hcurrentPos hcurrentPos v
  have hcode : LaterAssignmentStartMeasurability.laterAssignmentStartCode
      x.payload ell d.instruction d.record.input.row consistent =
      .sampled (CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K
        (AssignmentScoreReconstruction.currentWeight d.out)
        (AssignmentScoreReconstruction.currentWeight d.out)
        hcurrentPos hcurrentPos v) := by
    let input : LaterAssignmentStartMeasurability.LocalStartInput x.payload :=
      Sigma.mk ell (d.instruction, consistent)
    have hdecision : LaterAssignmentStartOperation.decideReconstruction
        x.payload ell d.instruction = .success d.out hrec := by
      unfold LaterAssignmentStartOperation.decideReconstruction
      have hrec' : AssignmentScoreReconstruction.reconstructLaterStart ell d.instruction =
          .success ell d.instruction d.out := by
        change AssignmentScoreReconstruction.reconstructLaterStart ell d.instruction =
          .success ell d.instruction d.out at hrec
        exact hrec
      have hpair :
          (⟨AssignmentScoreReconstruction.reconstructLaterStart ell d.instruction, rfl⟩ :
            LaterAssignmentStartOperation.ReconstructionCall x.payload ell d.instruction) =
          ⟨.success ell d.instruction d.out, hrec'⟩ := by
        apply LaterAssignmentStartOperation.ReconstructionCall.ext
        exact hrec'
      rw [hpair]
      simp [LaterAssignmentStartOperation.decideFromCall]
    calc
      _ = LaterAssignmentStartMeasurability.reconstructedFirstCode
          x.payload input d.record.input.row :=
        (LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_reconstructedFirstCode
          x.payload input d.record.input.row)
      _ = .sampled (CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K
          (AssignmentScoreReconstruction.currentWeight d.out)
          (AssignmentScoreReconstruction.currentWeight d.out)
          hcurrentPos hcurrentPos v) := by
        simp only [LaterAssignmentStartMeasurability.reconstructedFirstCode, input,
          hdecision]
        change LaterAssignmentStartMeasurability.codeOfCheckedSample p
          (CheckedAssignmentSample.checkedAssignmentSample p par.1 par.2 v) = _
        rw [hsampled]
        rfl
  have hsuccessCode :
      LaterAssignmentStartMeasurability.laterAssignmentStartCode
          x.payload ell d.instruction d.record.input.row consistent ∈
        LaterAssignmentStartMeasurability.laterAssignmentStartSuccessCodeSet p := by
    rw [hcode]
    exact Set.mem_range.mpr ⟨_, rfl⟩
  obtain ⟨output, hlocal, hresult⟩ :=
    (LaterAssignmentJointCodeMeasurability.codeOfResult_mem_success_iff
      (LaterAssignmentStartOperation.laterAssignmentStart
        x.payload ell d.instruction d.record.input.row consistent)).mp hsuccessCode
  have houtputRec : output.reconstruction = d.out := by
    have heq := output.reconstruction_eq.symm.trans d.reconstruction_eq
    injection heq with _ _ hvalue
  have houtcome : output.outcome = CanonicalAssignmentVector.sampler p.two_le_m p.m_lt_K
      (AssignmentScoreReconstruction.currentWeight d.out)
      (AssignmentScoreReconstruction.currentWeight d.out) hcurrentPos hcurrentPos v := by
    have hcode' := hcode
    simpa [LaterAssignmentStartMeasurability.laterAssignmentStartCode,
      LaterAssignmentStartMeasurability.codeOfResult, hresult] using hcode'
  have hslow : AssignmentParameterFibreKernel.successfulSlowSet p par v =
      some output.slowSet := by
    unfold AssignmentParameterFibreKernel.successfulSlowSet
    rw [hsampled]
    simp only [CheckedAssignmentSample.successfulSlowSet, houtcome,
      output.slowSet_eq_erasure]
  have htimeRecord : CoordinatorPhaseClock.startRoundTimeValid p
      d.record.input.time clock := by
    simpa only [clock, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput,
      ReferenceActivePhysicalStep.collectionClock] using d.core.clock_start_time_valid
  have htimeInstruction : CoordinatorPhaseClock.startRoundTimeValid p
      d.instruction.time clock := by
    rw [d.instruction_time]
    exact htimeRecord
  have hclockEq : CoordinatorPhaseClock.startRound p rate.eta.val
      d.instruction.time clock d.ledger.pending = .ok d.started := by
    simpa only [clock, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput,
      ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
  have hdispatchClockEq : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending = .ok d.started := by
    simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput,
      ReferenceActivePhysicalStep.collectionClock] using d.clock_eq
  have hclockEquations := CoordinatorPhaseClock.startRound_assignment_effect p
    x.etaReal x.time x.clock x.ledger.pending d.started d.instruction
    d.core.clock_parameter_valid d.core.clock_registers_valid
    d.core.clock_start_time_valid hdispatchClockEq d.instruction_eq
  rcases hclockEquations with ⟨htime, _, _, _, _, _, _, _⟩
  have hfreeze : x.clock.g = output.localConsistency.oldFreezeAt := by
    calc
      x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
      _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
      _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by rw [htime]; exact d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by rw [htime]; exact hdispatchClockEq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hbase : ∀ i, installed.retainedBaseScore i ≤ p.T * D p := by
    intro i
    rw [CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
      output clockData i, houtputRec]
    exact d.out.currentScore_le (output.payload.assignment.assigned i)
  have hcompat := CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
    output clockData
  rcases hcompat with ⟨_, _, huNone, hgrid, _, _, _, _, _⟩
  have hcutoffNone : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u =
      none := by rw [huNone]; rfl
  have hrenewalAnchor := CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
    output clockData d.renewal
  have hrenewalPayload :=
    (LaterAssignmentStartOperation.successful_renewal_law_spec output d.renewal).2.1
  have hweightEq : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      installed.registers.complementWeights j =
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 := by
    intro j
    change ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
        (AssignmentScoreReconstruction.sourceScore output.reconstruction j.1) =
      AssignmentScoreReconstruction.currentWeight output.reconstruction j.1
    rfl
  have henvelope : installed.registers.complementEnvelopeValid := by
    intro j
    have hanchor : installed.registers.payload.anchor j.1 =
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
      congrFun (by simpa only [installed,
        CoordinatorAssignmentRegisterInstall.later_registers_payload]
        using hrenewalPayload) j.1
    rw [hweightEq j, hanchor]
    exact ⟨le_rfl, by nlinarith [output.currentWeight_pos j.1]⟩
  have hstarted : CoordinatorLocalArmChoice.assignmentStart installed.registers.payload ≤
      CoordinatorLocalArmChoice.sourceRound d.instruction.time := by
    simp [installed, CoordinatorAssignmentRegisterInstall.installLater,
      CoordinatorLocalArmChoice.assignmentStart, CoordinatorLocalArmChoice.sourceRound,
      output.payload_start]
  have hcutoff : CoordinatorLocalArmChoice.assignmentStart installed.registers.payload ≤
      CoordinatorLocalArmChoice.cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u) := by
    simp [installed, CoordinatorAssignmentRegisterInstall.installLater,
      CoordinatorLocalArmChoice.assignmentStart, CoordinatorLocalArmChoice.cutoffRound,
      output.payload_start, hcutoffNone]
  have hweights : ∀ j : CanonicalFastSampling.FastArm installed.registers.payload.slowSet,
      0 < installed.registers.complementWeights j ∧
      installed.registers.payload.anchor j.1 ≤ installed.registers.complementWeights j ∧
      installed.registers.complementWeights j ≤ 2 * installed.registers.payload.anchor j.1 := by
    intro j
    have hanchor : installed.registers.payload.anchor j.1 =
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
      congrFun (by simpa only [installed,
        CoordinatorAssignmentRegisterInstall.later_registers_payload]
        using hrenewalPayload) j.1
    rw [hweightEq j, hanchor]
    exact ⟨output.currentWeight_pos j.1, le_rfl,
      by nlinarith [output.currentWeight_pos j.1]⟩
  have hchoice := CoordinatorLocalArmChoice.choiceInputsValid_mk
    installed.registers.payload
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
    d.instruction.time installed.registers.complementWeights hstarted hcutoff hweights
  have htime : d.instruction.time = x.time := by
    simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput] using d.instruction_time
  have hfreeze : x.clock.g = output.localConsistency.oldFreezeAt := by
    calc
      x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
      _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
      _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
  obtain ⟨selection, hdispatch⟩ := dispatchCollection_laterChosen
    x d.core d.started hdispatchClockEq d.instruction d.instruction_eq
    consistent output hlocal htime hfreeze hpending hresult hbase hchoice henvelope
  have hchosen := selection.armChoice_eq
  have hcutValid : 1 ≤ d.ledger.cutoff ∧ d.ledger.cutoff ≤ p.T := by
    rw [d.cutoff_eq]
    constructor <;> omega
  have hcutIndex :
      (⟨d.ledger.cutoff - 1, by omega⟩ : Fin p.T) = u := by
    apply Fin.ext
    change d.ledger.cutoff - 1 = u.val
    rw [d.cutoff_eq]
    omega
  have hdispatchPhysical : ReferenceActivePhysicalStep.dispatch d.record.input =
      .collection d.old d.ledger clock u
        (CoordinatorRoundDispatch.dispatchCollection x) := by
    simp only [ReferenceActivePhysicalStep.dispatch, d.coordinator_eq]
    simp only [dite_eq_left hcutValid, CoordinatorRoundDispatch.dispatch]
    rw [hcutIndex]
    rfl
  have hprep : d.record.output.preparation =
      ReferenceActivePhysicalStep.prepare d.record.input := by
    have h := congrArg
      (fun out : ReferenceActivePhysicalStep.RoundOutput d.record.input => out.preparation)
      d.record.output_eq
    simpa only [ReferenceActivePhysicalStep.step] using h
  have hprepcoord : d.record.output.preparation.coordinator =
      .collection d.old d.ledger clock u (CoordinatorRoundDispatch.dispatchCollection x) := by
    have h := congrArg
      (fun out : ReferenceActivePhysicalStep.RoundOutput d.record.input =>
        out.preparation.coordinator) d.record.output_eq
    have hprepCoordinator : d.record.output.preparation.coordinator =
        (ReferenceActivePhysicalStep.prepare d.record.input).coordinator := by
      simpa only [ReferenceActivePhysicalStep.step] using h
    calc
      d.record.output.preparation.coordinator =
          (ReferenceActivePhysicalStep.prepare d.record.input).coordinator := hprepCoordinator
      _ = .collection d.old d.ledger clock u
          (CoordinatorRoundDispatch.dispatchCollection x) := by
        change ReferenceActivePhysicalStep.dispatch d.record.input = _
        exact hdispatchPhysical
  have harm : d.record.output.preparation.coordinator.arm = selection.arm := by
    rw [hprepcoord, hdispatch]
    simp [ReferenceActivePhysicalStep.DispatchCut.arm,
      ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, d.instruction_time]
  have hobsPrepared : (ReferenceActivePhysicalStep.prepare d.record.input).observeCoordinator =
      ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare d.record.input)
        installed.registers installed.ownedRegisters installed.retainedBaseScore d.started := by
    have h := ReferenceActivePhysicalStep.observeCoordinator_collection_equation
      (ReferenceActivePhysicalStep.prepare d.record.input) d.old d.ledger clock u
      (CoordinatorRoundDispatch.dispatchCollection x) (by
        change ReferenceActivePhysicalStep.dispatch d.record.input = _
        exact hdispatchPhysical)
    rw [hdispatch] at h
    simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, d.instruction_time,
      installed, clockData, CoordinatorAssignmentRegisterInstall.installLater] using h
  have hobs : d.record.output.coordinator =
      ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare d.record.input)
        installed.registers installed.ownedRegisters installed.retainedBaseScore d.started := by
    have h := congrArg
      (fun out : ReferenceActivePhysicalStep.RoundOutput d.record.input => out.coordinator)
      d.record.output_eq
    calc
      d.record.output.coordinator =
          (ReferenceActivePhysicalStep.prepare d.record.input).observeCoordinator := by
        simpa only [ReferenceActivePhysicalStep.step] using h
      _ = _ := hobsPrepared
  have hnext : d.record.output.next.coordinator =
      (ReferenceActivePhysicalStep.livePostChoice
        (ReferenceActivePhysicalStep.prepare d.record.input)
        installed.registers installed.ownedRegisters installed.retainedBaseScore
        d.started).configuration := by
    have h := congrArg
      (fun out : ReferenceActivePhysicalStep.RoundOutput d.record.input =>
        out.next.coordinator) d.record.output_eq
    calc
      d.record.output.next.coordinator =
          (ReferenceActivePhysicalStep.prepare d.record.input).observeCoordinator.configuration := by
        simpa only [ReferenceActivePhysicalStep.step] using h
      _ = _ := congrArg CoordinatorObservation.configuration hobsPrepared
  refine ⟨consistent, output, hlocal, hresult, ?_⟩
  constructor
  · exact output.assignmentVector_eq_row_projection
  constructor
  · exact houtputRec
  constructor
  · exact hslow
  constructor
  · exact output.payload_slowSet
  constructor
  · exact CoordinatorAssignmentRegisterInstall.later_registers_payload output clockData
  constructor
  · exact output.assignmentVector_eq_row_projection
  constructor
  · exact houtputRec
  constructor
  · exact hrenewalAnchor.trans (congrArg
      AssignmentScoreReconstruction.currentWeight houtputRec)
  constructor
  · intro a
    calc
      installed.registers.payload.queues a = output.payload.queues a := by
        rw [CoordinatorAssignmentRegisterInstall.later_registers_payload]
      _ = AssignmentScoreReconstruction.initialQueue d.out a := by
        rw [output.payload_queues, houtputRec]
  constructor
  · intro i
    simpa [installed, clockData,
      CoordinatorAssignmentRegisterInstall.installLater, houtputRec] using
      CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
        output clockData i
  exact ⟨selection, hchosen, hdispatch, hprep, hprepcoord, harm, hobs, hnext⟩

/-- The actual first-collection renewal call produces its checked sampled
assignment, the literal local start, the computed installation, and the
actual original-row arm choice. The post-choice observation is kept as the
full `livePostChoice` operation, including its recorder, service, confirmation,
and finish branches.

Source ranges: `06_interruptions.tex:40-69`,
`04_slow_fast_learner.tex:176-215`, and
`appendix_a_local_protocol.tex:28-79`. -/
theorem actual_renewal_call_installation
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : RenewalCallSource rate rewards C_star C_h u t) :
    ∃ d : ActualRenewalCall rate rewards C_star C_h u t z,
      let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u d.record.input d.old d.ledger d.saved
      let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
        CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
      let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
        x.payload ell d.instruction d.out d.reconstruction_eq
      let v := LaterAssignmentStartOperation.ownAssignmentVector
        d.record.input.row d.instruction.time
      let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
      ∃ consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell,
        ∃ output : LaterAssignmentStartOperation.SuccessfulStart
          x.payload ell d.instruction x.row,
          ∃ hlocal : output.localConsistency = consistent,
            LaterAssignmentStartOperation.laterAssignmentStart
                x.payload ell d.instruction x.row consistent =
              .success output hlocal ∧
            output.assignmentVector = v ∧
            output.reconstruction = d.out ∧
            AssignmentParameterFibreKernel.successfulSlowSet p par v =
              some output.slowSet ∧
            output.payload.slowSet = output.slowSet ∧
            let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                output := {
              priorClock := x.clock
              pending := x.ledger.pending
              proposalParameterValid := d.core.clock_parameter_valid
              priorClockValid := d.core.clock_registers_valid
              startTimeValid := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  d.instruction_time] using d.core.clock_start_time_valid
              result := d.started
              startRound_eq := by
                simpa only [x,
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                  ReferenceActivePhysicalStep.collectionInput,
                  ReferenceActivePhysicalStep.collectionClock,
                  d.instruction_time] using d.clock_eq
              assignmentStart_eq := d.instruction_eq
              priorSigma_eq := d.core.clock_sigma_eq
              priorGrid_eq_freezeAt := by
                calc
                  x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
                  _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                  _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
            let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
            installed.registers.payload = output.payload ∧
            installed.assignmentVector = v ∧
            installed.reconstruction = d.out ∧
            installed.registers.payload.anchor =
              AssignmentScoreReconstruction.currentWeight d.out ∧
            (∀ a, installed.registers.payload.queues a =
              AssignmentScoreReconstruction.initialQueue d.out a) ∧
            (∀ i, installed.retainedBaseScore i =
              AssignmentScoreReconstruction.sourceScore d.out
                (output.payload.assignment.assigned i)) ∧
            ∃ selection : CoordinatorRoundDispatch.ArmSelection
                installed.registers.payload d.started d.instruction.time
                installed.registers.complementWeights d.record.input.row,
              CoordinatorLocalArmChoice.coordinatorArmChoice
                  installed.registers.payload d.started.pending
                  (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                  d.instruction.time installed.registers.complementWeights d.record.input.row =
                some selection.arm ∧
              CoordinatorRoundDispatch.dispatchCollection x =
                .laterChosen d.core consistent d.started d.clock_eq d.instruction
                  d.instruction_eq output hlocal clockData installed selection ∧
              d.record.output.preparation = ReferenceActivePhysicalStep.prepare d.record.input ∧
              d.record.output.preparation.coordinator =
                .collection d.old d.ledger clock u
                  (CoordinatorRoundDispatch.dispatchCollection x) ∧
              d.record.output.preparation.coordinator.arm = selection.arm ∧
              d.record.output.coordinator =
                ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore d.started ∧
              d.record.output.next.coordinator =
                (ReferenceActivePhysicalStep.livePostChoice
                  (ReferenceActivePhysicalStep.prepare d.record.input)
                  installed.registers installed.ownedRegisters installed.retainedBaseScore
                  d.started).configuration := by
  obtain ⟨d⟩ := ReferenceFirstCollectionRenewalAuxiliaryLaw.actual_renewal_call_parameters
    rate rewards C_star C_h u t z
  refine ⟨d, ?_⟩
  exact actual_call_witnesses d

/-- On the unchanged, unnormalized renewal-lift law, the vector inserted into
the actual original record is the same vector used by the accepted sampler,
and its actual output/payload/install slow set is the original whole-array
auxiliary sample.

Source ranges: `06_interruptions.tex:40-69,399-423`,
`04_slow_fast_learner.tex:176-215`, `07_public_setup.tex:121-164`, and
`appendix_a_local_protocol.tex:28-79`. -/
theorem ae_renewalLiftLaw_inserted_installation
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :
    ∀ᵐ wv : ReferenceFirstCollectionRenewalVectorInsertion.W
        rate rewards C_star C_h u t ∂
      ReferenceFirstCollectionRenewalVectorInsertion.Lambda rate rewards C_star C_h u t,
      let z' := ReferenceFirstCollectionRenewalVectorInsertion.put
        rate rewards C_star C_h u t wv.1.1 wv.2
      let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u t z' wv.1.2
      ∃ d : ActualRenewalCall rate rewards C_star C_h u t z',
        let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
          rate u d.record.input d.old d.ledger d.saved
        let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
          CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
        let par := LaterAssignmentStartMeasurability.selectedSamplerParameters
          x.payload ell d.instruction d.out d.reconstruction_eq
        let v := LaterAssignmentStartOperation.ownAssignmentVector
          d.record.input.row d.instruction.time
        let clock := ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u
        ∃ consistent : LaterAssignmentStartOperation.LocalConsistency x.payload ell,
          ∃ output : LaterAssignmentStartOperation.SuccessfulStart
            x.payload ell d.instruction x.row,
            ∃ hlocal : output.localConsistency = consistent,
              LaterAssignmentStartOperation.laterAssignmentStart
                  x.payload ell d.instruction x.row consistent =
                .success output hlocal ∧
              v = wv.2 ∧
              output.assignmentVector = wv.2 ∧
              output.reconstruction = d.out ∧
              AssignmentParameterFibreKernel.successfulSlowSet p par v =
                some output.slowSet ∧
              output.slowSet = U ∧
              output.payload.slowSet = U ∧
              let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                  output := {
                priorClock := x.clock
                pending := x.ledger.pending
                proposalParameterValid := d.core.clock_parameter_valid
                priorClockValid := d.core.clock_registers_valid
                startTimeValid := by
                  simpa only [x,
                    ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                    ReferenceActivePhysicalStep.collectionInput,
                    d.instruction_time] using d.core.clock_start_time_valid
                result := d.started
                startRound_eq := by
                  simpa only [x,
                    ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
                    ReferenceActivePhysicalStep.collectionInput,
                    ReferenceActivePhysicalStep.collectionClock,
                    d.instruction_time] using d.clock_eq
                assignmentStart_eq := d.instruction_eq
                priorSigma_eq := d.core.clock_sigma_eq
                priorGrid_eq_freezeAt := by
                  calc
                    x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
                    _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                    _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
              let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
              installed.registers.payload = output.payload ∧
              installed.assignmentVector = wv.2 ∧
              installed.reconstruction = d.out ∧
              installed.registers.payload.anchor =
                AssignmentScoreReconstruction.currentWeight d.out ∧
              (∀ a, installed.registers.payload.queues a =
                AssignmentScoreReconstruction.initialQueue d.out a) ∧
              (∀ i, installed.retainedBaseScore i =
                AssignmentScoreReconstruction.sourceScore d.out
                  (output.payload.assignment.assigned i)) ∧
              installed.registers.payload.slowSet = U ∧
              ∃ selection : CoordinatorRoundDispatch.ArmSelection
                  installed.registers.payload d.started d.instruction.time
                  installed.registers.complementWeights d.record.input.row,
                CoordinatorLocalArmChoice.coordinatorArmChoice
                    installed.registers.payload d.started.pending
                    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.started.clock.u)
                    d.instruction.time installed.registers.complementWeights d.record.input.row =
                  some selection.arm ∧
                CoordinatorRoundDispatch.dispatchCollection x =
                  .laterChosen d.core consistent d.started d.clock_eq d.instruction
                    d.instruction_eq output hlocal clockData installed selection ∧
                d.record.output.preparation = ReferenceActivePhysicalStep.prepare d.record.input ∧
                d.record.output.preparation.coordinator =
                  .collection d.old d.ledger clock u
                    (CoordinatorRoundDispatch.dispatchCollection x) ∧
                d.record.output.preparation.coordinator.arm = selection.arm ∧
                d.record.output.coordinator =
                  ReferenceActivePhysicalStep.livePostChoice
                    (ReferenceActivePhysicalStep.prepare d.record.input)
                    installed.registers installed.ownedRegisters installed.retainedBaseScore d.started ∧
                d.record.output.next.coordinator =
                  (ReferenceActivePhysicalStep.livePostChoice
                    (ReferenceActivePhysicalStep.prepare d.record.input)
                    installed.registers installed.ownedRegisters installed.retainedBaseScore
                    d.started).configuration := by
  filter_upwards [ReferenceFirstCollectionRenewalVectorInsertion.ae_renewalLiftLaw_inserted_sampler
      rate rewards C_star C_h u t] with wv h
  dsimp only
  rcases h with ⟨d, hv, hsample⟩
  let z' := ReferenceFirstCollectionRenewalVectorInsertion.put
    rate rewards C_star C_h u t wv.1.1 wv.2
  let U := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
    rate rewards C_star C_h u t z' wv.1.2
  let x := ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
    rate u d.record.input d.old d.ledger d.saved
  let ell : LaterAssignmentStartOperation.LocalLedger x.payload :=
    CoordinatorRoundDispatch.collectionOperationLedger x d.core.payload_n_eq
  have hwitness := actual_call_witnesses d
  dsimp only [z', U] at hwitness hsample
  obtain ⟨consistent, output, hlocal, hresult, hrest⟩ := hwitness
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := x.clock
    pending := x.ledger.pending
    proposalParameterValid := d.core.clock_parameter_valid
    priorClockValid := d.core.clock_registers_valid
    startTimeValid := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput, d.instruction_time] using
        d.core.clock_start_time_valid
    result := d.started
    startRound_eq := by
      simpa only [x, ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
        ReferenceActivePhysicalStep.collectionInput,
        ReferenceActivePhysicalStep.collectionClock, d.instruction_time] using d.clock_eq
    assignmentStart_eq := d.instruction_eq
    priorSigma_eq := d.core.clock_sigma_eq
    priorGrid_eq_freezeAt := by
      calc
        x.clock.g = x.ledger.freezeAt := d.core.ledger_freeze_eq.symm
        _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
        _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
  let installed := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hvectorOutput := hrest.1
  have hrecOutput := hrest.2.1
  have hslowActual := hrest.2.2.1
  have hpayloadSlow := hrest.2.2.2.1
  have htail := hrest.2.2.2.2
  have installedPayload := htail.1
  have hinstalledVector := htail.2.1
  have hinstalledRec := htail.2.2.1
  have hanchor := htail.2.2.2.1
  have hqueues := htail.2.2.2.2.1
  have hbase := htail.2.2.2.2.2.1
  have hchoiceTail := htail.2.2.2.2.2.2
  have hslowEq : output.slowSet = U :=
    Option.some.inj (hslowActual.symm.trans hsample)
  refine ⟨d, consistent, output, hlocal, hresult, ?_, ?_, hrecOutput,
    hslowActual, hslowEq, ?_, installedPayload, ?_, hinstalledRec,
    hanchor, hqueues, hbase, ?_, ?_⟩
  · exact hv
  · exact hvectorOutput.trans hv
  · exact hpayloadSlow.trans hslowEq
  · exact hinstalledVector.trans hv
  · calc
      _ = output.payload.slowSet := congrArg
        AssignmentStartPayload.Input.slowSet installedPayload
      _ = output.slowSet := hpayloadSlow
      _ = U := hslowEq
  · exact hchoiceTail

end Bandits.Support.ReferenceFirstCollectionRenewalSampleInstallation

end
