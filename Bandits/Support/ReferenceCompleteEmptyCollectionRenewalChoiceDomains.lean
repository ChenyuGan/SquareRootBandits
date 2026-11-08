/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteContinuingCollectionChoiceDomains

import Lean.Elab.Tactic.Omega

/-!
# Actual empty-pending collection renewal choice domains

For each actual complete-suffix collection record with empty pending set and
the retained freeze boundary reached, construct the successful later renewal,
its normalized full assignment sample, and the same physical pre-choice
selection. All score, queue, clock, and dispatch data come from the actual
source record and its checked operations.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-114,140-188,219-243`,
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299,355-426`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-84`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorAssignmentRegisterInstall
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.CheckedAssignmentSample

namespace Bandits.Support.ReferenceCompleteEmptyCollectionRenewalChoiceDomains

variable {p : ConstructorDimensions.Parameters}

private theorem allFin_eq_true_of_forall {n : ℕ} (test : Fin n → Bool)
    (hall : ∀ i, test i = true) : CoordinatorCollectionLedger.allFin n test = true := by
  unfold CoordinatorCollectionLedger.allFin
  rw [List.all_eq_true]
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
  subst b
  exact hall i

private def collectionDispatcherConsistency
    (input : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid input) :
    LaterAssignmentStartOperation.LocalConsistency input.payload
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq) := {
  oldStart_eq := by
    simpa [CoordinatorRecorderComplementBridge.sourceStart,
      CoordinatorRoundDispatch.collectionOperationLedger] using core.ledger_sigma_eq.symm
  oldAssignment_eq := by
    intro i
    simpa [CoordinatorRoundDispatch.collectionOperationLedger] using
      (core.assignment_eq i).symm
  oldFreezeAt := input.ledger.freezeAt
  oldFreezeAt_eq := rfl }

private theorem collectionDispatcherConsistency_eq
    (input : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid input)
    (consistent : LaterAssignmentStartOperation.LocalConsistency input.payload
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq)) :
    collectionDispatcherConsistency input core = consistent := by
  cases consistent with
  | mk hstart hassignment oldFreeze hfreeze =>
      have hfreeze' : oldFreeze = input.ledger.freezeAt := by
        simpa [CoordinatorRoundDispatch.collectionOperationLedger] using hfreeze
      subst oldFreeze
      rfl

private theorem dispatchCollection_laterChosen
    (input : CoordinatorRoundDispatch.CollectionInput p)
    (core : CoordinatorRoundDispatch.CollectionCoreValid input)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : CoordinatorPhaseClock.startRound p input.etaReal input.time
      input.clock input.ledger.pending = .ok started)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hassignment : started.assignmentStart = some instruction)
    (consistent : LaterAssignmentStartOperation.LocalConsistency input.payload
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq))
    (output : LaterAssignmentStartOperation.SuccessfulStart input.payload
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq)
      instruction input.row)
    (hlocal : output.localConsistency = consistent)
    (htime : instruction.time = input.time)
    (hfreeze : input.clock.g = output.localConsistency.oldFreezeAt)
    (hpending : input.ledger.pending = ∅)
    (hlater : LaterAssignmentStartOperation.laterAssignmentStart input.payload
      (CoordinatorRoundDispatch.collectionOperationLedger input core.payload_n_eq)
      instruction input.row consistent = .success output hlocal) :
    let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
      priorClock := input.clock
      pending := input.ledger.pending
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
      started instruction.time installation.registers.complementWeights input.row,
      CoordinatorRoundDispatch.dispatchCollection input =
        .laterChosen core consistent started hstart instruction hassignment output hlocal
          clockData installation selection := by
  classical
  dsimp only
  intro hbase hchoice henvelope
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := input.clock
    pending := input.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  let dispatcherClockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := input.clock
    pending := input.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htime]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htime]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let dispatcherInstallation :=
    CoordinatorAssignmentRegisterInstall.installLater output dispatcherClockData
  have hbaseDispatch : ∀ i, dispatcherInstallation.retainedBaseScore i ≤ p.T * D p := by
    simpa [dispatcherClockData, dispatcherInstallation, clockData, installation,
      CoordinatorAssignmentRegisterInstall.installLater] using hbase
  have hchoiceDispatch : CoordinatorLocalArmChoice.ChoiceInputsValid
      dispatcherInstallation.registers.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      instruction.time dispatcherInstallation.registers.complementWeights := by
    simpa [dispatcherClockData, dispatcherInstallation, clockData, installation,
      CoordinatorAssignmentRegisterInstall.installLater] using hchoice
  have henvelopeDispatch : dispatcherInstallation.registers.complementEnvelopeValid := by
    simpa [dispatcherClockData, dispatcherInstallation, clockData, installation,
      CoordinatorAssignmentRegisterInstall.installLater] using henvelope
  have hnotpending : ¬ input.ledger.pending.Nonempty := by
    rw [hpending]
    simp
  have hconsistent := collectionDispatcherConsistency_eq input core consistent
  cases hconsistent
  simp only [collectionDispatcherConsistency] at hlocal
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
        have houtput : actualOutput = output := by
          have hprojected := congrArg (fun result =>
            match result with
            | .success value _ => some value
            | _ => none) heq
          exact Option.some.inj hprojected
        subst actualOutput
        have hlocal' : actualLocal = hlocal := Subsingleton.elim _ _
        cases hlocal'
        if hbase' : ∀ i, installation.retainedBaseScore i ≤ p.T * D p then
          if hchoice' : CoordinatorLocalArmChoice.ChoiceInputsValid installation.registers.payload
              (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
              instruction.time installation.registers.complementWeights then
            if henvelope' : installation.registers.complementEnvelopeValid then
              let selected := CoordinatorLocalArmChoice.coordinatorArmChoice
                installation.registers.payload
                (by
                  simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
                    using started.pending)
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                instruction.time installation.registers.complementWeights input.row
              have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
                installation.registers.payload
                (by
                  simpa [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
                    using started.pending)
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                instruction.time installation.registers.complementWeights input.row hchoice'
              match hselected : selected with
              | none => exact False.elim (hnonempty hselected)
              | some arm =>
                  have hselected' :
                      CoordinatorLocalArmChoice.coordinatorArmChoice
                        installation.registers.payload
                        (by
                          simpa [ActiveRoundActions.Follower,
                            PublicDiscreteDraws.followerCount] using started.pending)
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                        instruction.time installation.registers.complementWeights input.row =
                        some arm := hselected
                  have hselectedDispatch :
                      CoordinatorLocalArmChoice.coordinatorArmChoice
                        output.payload started.pending
                        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
                        instruction.time
                        (CoordinatorAssignmentRegisterInstall.installLater output
                          dispatcherClockData).registers.complementWeights input.row =
                        some arm := by
                    simpa [installation, clockData, dispatcherClockData,
                      dispatcherInstallation,
                      CoordinatorAssignmentRegisterInstall.installLater,
                      ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount] using
                      hselected'
                  exact ⟨{
                    arm := arm
                    choiceInputsValid := hchoice'
                    recorderBoundaryValid := by
                      have hgrid := started.gridDomain
                      cases hσ : started.clock.sigma with
                      | none =>
                          simp only [CoordinatorPhaseClock.clockGridDomain, hσ] at hgrid
                          omega
                      | some sigma =>
                          simp only [CoordinatorPhaseClock.clockGridDomain, hσ] at hgrid
                          exact hgrid.2
                    armChoice_eq := by
                      simpa [ActiveRoundActions.Follower,
                        PublicDiscreteDraws.followerCount] using hselected' }, by
                      split
                      · split
                        · rename_i hnone
                          exact False.elim (hnonempty hnone)
                        · rename_i actualArm hactualChoice
                          have harm : actualArm = arm :=
                            Option.some.inj (hactualChoice.symm.trans hselectedDispatch)
                          subst actualArm
                          rfl
                      · rename_i hbadBase
                        exact False.elim (hbadBase hbaseDispatch)⟩
            else exact False.elim (henvelope' henvelope)
          else exact False.elim (hchoice' hchoice)
        else exact False.elim (hbase' hbase)

private theorem collection_choice_inputs_valid_of_renewal
    {eta : ReferencePrelaunchFollower.LearningRate}
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (hrenewal : instruction.kind = .renewal) :
    CoordinatorLocalArmChoice.ChoiceInputsValid output.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clockData.result.clock.u)
      instruction.time
      (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights := by
  have hcompat := CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
    output clockData
  rcases hcompat with ⟨_, hsigma, huNone, _, _, _, _, _, _⟩
  have hanchor := CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
    output clockData hrenewal
  have hstarted : CoordinatorLocalArmChoice.assignmentStart output.payload ≤
      CoordinatorLocalArmChoice.sourceRound instruction.time := by
    simp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.sourceRound, output.payload_start]
  have hcutoff : CoordinatorLocalArmChoice.assignmentStart output.payload ≤
      CoordinatorLocalArmChoice.cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clockData.result.clock.u) := by
    have hcutoffNone : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        clockData.result.clock.u = none := by
      simp [CoordinatorLiveChoiceRecorderStep.cutoffFromClock, huNone]
    rw [hcutoffNone]
    simp [CoordinatorLocalArmChoice.assignmentStart,
      CoordinatorLocalArmChoice.cutoffRound, output.payload_start]
  have hweights : ∀ j, 0 <
      (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights j ∧
      output.payload.anchor j.1 ≤
        (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights j ∧
      (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights j ≤
        2 * output.payload.anchor j.1 := by
    intro j
    have hweight :
        (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights j =
          AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 := rfl
    have hanchor' : output.payload.anchor j.1 =
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 := by
      simpa only [CoordinatorAssignmentRegisterInstall.later_registers_payload] using
        congrFun hanchor j.1
    rw [hweight, hanchor']
    exact ⟨output.currentWeight_pos j.1, le_rfl,
      by
        have hnonneg := (output.currentWeight_pos j.1).le
        calc
          AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 ≤
              AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 +
                AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
            le_add_of_nonneg_right hnonneg
          _ = 2 * AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
            (two_mul _).symm⟩
  exact CoordinatorLocalArmChoice.choiceInputsValid_mk output.payload
    (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clockData.result.clock.u)
    instruction.time (CoordinatorAssignmentRegisterInstall.installLater output clockData).registers.complementWeights
    hstarted hcutoff hweights

private theorem renewal_sample_start
    {eta : ReferencePrelaunchFollower.LearningRate}
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (reconstruction : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction reconstruction)
    (hcutoffBound : ledger.cutoff ≤ instruction.time.val + 1)
    (hcurrentPos : ∀ a, 0 < AssignmentScoreReconstruction.currentWeight reconstruction a)
    (hcutoffPos : ∀ a, 0 < AssignmentScoreReconstruction.cutoffWeight reconstruction a)
    (hkind : instruction.kind = .renewal) :
    ∃ (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
      (hlocal : output.localConsistency = consistent)
      (mass : PrefixSetSampler.NormalizedMass p.K p.m (Nat.le_of_lt p.m_lt_K))
      (sampled : OrientedAssignmentLaw.AssignmentOutcome p.K p.m),
      LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction row consistent =
        .success output hlocal ∧
      (∀ S, mass.weight S = output.law.mass S) ∧
      CheckedAssignmentSample.checkedAssignmentSample p mass.weight output.law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
          .sampled sampled := by
  classical
  have hcallPair :
      (⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction,
        rfl⟩ : LaterAssignmentStartOperation.ReconstructionCall old ledger instruction) =
        ⟨.success ledger instruction reconstruction, hcall⟩ := by
    apply LaterAssignmentStartOperation.ReconstructionCall.ext
    exact hcall
  have hselectedExists := LaterAssignmentStartOperation.selectLaw?_isSome
    old ledger instruction reconstruction hcall
    hcutoffBound hcurrentPos
  let law : LaterAssignmentStartOperation.SelectedLaw old ledger
      instruction reconstruction := Classical.choose hselectedExists
  have hlawSelected := Classical.choose_spec hselectedExists
  have hrenewalLaw := LaterAssignmentStartOperation.selectLaw?_renewal_spec
    old ledger instruction reconstruction hcutoffBound hcurrentPos
    law hlawSelected hkind
  let normalized : PrefixSetSampler.NormalizedMass p.K p.m
      (Nat.le_of_lt p.m_lt_K) := {
    weight := law.mass
    weight_nonneg := by
      intro S
      rw [hrenewalLaw.2 S]
      change 0 ≤ LaterAssignmentStartOperation.productQOnPrefixCarrier
        (AssignmentScoreReconstruction.currentWeight reconstruction) S
      unfold LaterAssignmentStartOperation.productQOnPrefixCarrier
      exact (ProductSetLaw.Q_pos
        (AssignmentScoreReconstruction.currentWeight reconstruction)
        (ConstructorDimensions.m_pos p) p.m_lt_K hcurrentPos
        ⟨S.1, by simp [ProductSetLaw.support]⟩).le
    weight_sum_eq_one := by
      simp only [PrefixMassPartition.totalMass]
      calc
        (∑ S ∈ Finset.univ, law.mass S) =
            ∑ S : PrefixSetSampler.SetCarrier p.K p.m,
              LaterAssignmentStartOperation.renewalRawMass reconstruction S := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hrenewalLaw.2 S
        _ = 1 := LaterAssignmentStartOperation.renewalRawMass_sum_eq_one
          reconstruction hcurrentPos }
  have hnormalizedSample :=
    CheckedAssignmentSample.checkedAssignmentSample_normalized_success
      p normalized law.anchor law.anchor_pos
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
  obtain ⟨sampled, hsample⟩ := hnormalizedSample
  let slowSet := CheckedAssignmentOrientation.slowSetAfter p
    sampled.1.1 sampled.1.2 sampled.2
  let newPayload := LaterAssignmentStartOperation.payloadInput old instruction
    reconstruction law slowSet
  let output : LaterAssignmentStartOperation.SuccessfulStart old ledger
      instruction row := {
    localConsistency := consistent
    reconstruction := reconstruction
    reconstruction_eq := hcall
    cutoffReached := hcutoffBound
    currentWeight_pos := hcurrentPos
    cutoffWeight_pos := hcutoffPos
    law := law
    law_selected := hlawSelected
    outcome := sampled
    slowSet := slowSet
    slowSet_eq_erasure := rfl
    assignmentVector := LaterAssignmentStartOperation.ownAssignmentVector row instruction.time
    assignmentVector_eq_row_projection := rfl
    checkedSample_eq := by simpa [normalized] using hsample
    payload := newPayload
    payload_eq_input := rfl
    payload_start := rfl
    payload_anchor := rfl
    payload_slowSet := rfl
    payload_queues := fun _ => rfl
    baseScore := LaterAssignmentStartOperation.retainedBaseScore reconstruction newPayload
    baseScore_eq_source := fun _ => rfl }
  have hlocal : output.localConsistency = consistent := rfl
  have hsampleRaw : CheckedAssignmentSample.checkedAssignmentSample p law.mass law.anchor
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
        .sampled sampled := by
    simpa [normalized] using hsample
  have hlater : LaterAssignmentStartOperation.laterAssignmentStart old
      ledger instruction row consistent = .success output hlocal := by
    change LaterAssignmentStartOperation.runReconstructionDecision old
      ledger instruction row consistent
      (LaterAssignmentStartOperation.decideFromCall old ledger instruction
        ⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩) = _
    rw [hcallPair]
    change LaterAssignmentStartOperation.runReconstructionDecision old
      ledger instruction row consistent
      (.success reconstruction hcall) = _
    change LaterAssignmentStartOperation.finishCheckedSample old
      ledger instruction row consistent reconstruction hcall
      hcutoffBound hcurrentPos hcutoffPos law hlawSelected = _
    unfold LaterAssignmentStartOperation.finishCheckedSample
    split
    · rename_i arm reason hresult
      rw [hsampleRaw] at hresult
      cases hresult
    · rename_i set hresult
      rw [hsampleRaw] at hresult
      cases hresult
    · rename_i outcome hresult
      have houtcome : outcome = sampled := by
        exact CheckedAssignmentSample.Result.sampled.inj (hresult.symm.trans hsampleRaw)
      subst outcome
      rfl
  exact ⟨output, hlocal, normalized, sampled, hlater, fun _ => rfl, hsample⟩

/-- Every actual empty-pending collection renewal on the original complete
source suffix reaches the checked later-start producer and the physical
choice. The ledger and complete incoming-mass result supply the full output
domains, including arms that were slow in the preceding assignment. Renewal
uses no preceding service subtraction; the new anchor is exactly the
reconstructed current weight. The sampler is checked on the original complete
`K + 1` assignment vector. -/
theorem complete_empty_collection_renewal_choice_domains
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (source : BootstrapPrivateRoundStreams.SourceInput p) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∀ (k : Fin records.length),
      let record := records[k.val]'k.isLt
      let x := record.input
      ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
        (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        (hstate : x.state.coordinator = .collection payload ledger saved) →
        ledger.pending = ∅ →
        ledger.freezeAt ≤ x.time.val + 1 →
        ∃ u : Fin p.T, u.val + 1 = ledger.cutoff ∧
          let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
          let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock u
          ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input),
            CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true ∧
            ∃ (started : CoordinatorPhaseClock.StartRoundResult p),
              ∃ (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time
                input.clock ledger.pending = .ok started),
              ∃ (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p),
                ∃ (hassignment : started.assignmentStart = some instruction),
                ∃ (hinstructionTime : instruction.time = x.time),
                  ∃ (_hrenewal : instruction.kind = .renewal),
              let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger
                input core.payload_n_eq
              let consistent : LaterAssignmentStartOperation.LocalConsistency
                  input.payload operationLedger := {
                oldStart_eq := by
                  simpa [CoordinatorRecorderComplementBridge.sourceStart,
                    operationLedger, CoordinatorRoundDispatch.collectionOperationLedger] using
                    core.ledger_sigma_eq.symm
                oldAssignment_eq := by
                  intro i
                  simpa [operationLedger,
                    CoordinatorRoundDispatch.collectionOperationLedger] using
                    (core.assignment_eq i).symm
                oldFreezeAt := ledger.freezeAt
                oldFreezeAt_eq := rfl }
              ∃ (output : LaterAssignmentStartOperation.SuccessfulStart
                  input.payload operationLedger instruction input.row)
                (hlocal : output.localConsistency = consistent),
                LaterAssignmentStartOperation.laterAssignmentStart input.payload
                  operationLedger instruction input.row consistent = .success output hlocal ∧
                let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence
                    output := {
                  priorClock := input.clock
                  pending := ledger.pending
                  proposalParameterValid := core.clock_parameter_valid
                  priorClockValid := core.clock_registers_valid
                  startTimeValid := by rw [hinstructionTime]; exact core.clock_start_time_valid
                  result := started
                  startRound_eq := by rw [hinstructionTime]; exact hstart
                  assignmentStart_eq := hassignment
                  priorSigma_eq := core.clock_sigma_eq
                  priorGrid_eq_freezeAt := by
                    calc
                      input.clock.g = ledger.freezeAt := core.ledger_freeze_eq.symm
                      _ = consistent.oldFreezeAt := consistent.oldFreezeAt_eq.symm
                      _ = output.localConsistency.oldFreezeAt := by rw [hlocal] }
                let installation :=
                  CoordinatorAssignmentRegisterInstall.installLater output clockData
                (∀ a, AssignmentScoreReconstruction.sourceScore output.reconstruction a =
                  (output.reconstruction.registers.cutoff a).score + operationLedger.increment a) ∧
                (∀ a, AssignmentScoreReconstruction.initialQueue output.reconstruction a =
                  (output.reconstruction.registers.current a).queue) ∧
                (∀ a, AssignmentScoreReconstruction.currentWeight output.reconstruction a =
                  (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^
                    AssignmentScoreReconstruction.sourceScore output.reconstruction a) ∧
                installation.registers.payload.anchor =
                  AssignmentScoreReconstruction.currentWeight output.reconstruction ∧
                (∀ a, installation.registers.payload.queues a =
                  AssignmentScoreReconstruction.initialQueue output.reconstruction a) ∧
                (installation.registers.scoreDomainValid ∧
                  installation.ownedRegisters.queueDomainValid ∧
                  installation.ownedRegisters.previousServiceDomainValid) ∧
                (∀ i, installation.retainedBaseScore i ≤ p.T * D p) ∧
                (instruction.kind = CoordinatorPhaseClock.classifyAssignmentStart
                    input.clock.sigma instruction.time input.clock.g ∧
                  started.clock.sigma = some x.time ∧ started.clock.u = none ∧
                  started.clock.g = FollowerCutoffScan.gridBoundary p rate.eta.val x.time ∧
                  started.pending = Finset.univ ∧ started.ledgerCommand = none) ∧
                ∃ (mass : PrefixSetSampler.NormalizedMass p.K p.m
                    (Nat.le_of_lt p.m_lt_K)) (sampled : OrientedAssignmentLaw.AssignmentOutcome
                      p.K p.m),
                  (∀ S : PrefixSetSampler.SetCarrier p.K p.m,
                    mass.weight S = output.law.mass S) ∧
                  CheckedAssignmentSample.checkedAssignmentSample p mass.weight
                    output.law.anchor
                    (LaterAssignmentStartOperation.ownAssignmentVector x.row instruction.time) =
                      .sampled sampled ∧
                  output.assignmentVector =
                    LaterAssignmentStartOperation.ownAssignmentVector x.row instruction.time ∧
                ∃ (selection : CoordinatorRoundDispatch.ArmSelection
                    installation.registers.payload started instruction.time
                    installation.registers.complementWeights input.row),
                  CoordinatorRoundDispatch.dispatchCollection input =
                    .laterChosen core consistent started
                      hstart instruction hassignment
                      output hlocal clockData installation selection ∧
                  let preparation := ReferenceActivePhysicalStep.prepare x
                  preparation.coordinator =
                    .collection payload ledger clock u
                      (CoordinatorRoundDispatch.dispatchCollection input) ∧
                  ∃ (physicalSelection : ReferenceActivePhysicalStep.Selection x),
                    ReferenceActivePhysicalStep.DispatchCut.selection
                        preparation.coordinator = some physicalSelection ∧
                    physicalSelection.view.payload = installation.registers.payload ∧
                    physicalSelection.view.cutoff =
                      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u ∧
                    CoordinatorLocalArmChoice.assignmentIsLive
                      physicalSelection.view.payload physicalSelection.view.cutoff x.time := by
  classical
  dsimp only
  intro k
  let x := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt |>.input
  intro payload ledger saved hstate hpending hfreeze
  have hstate' : x.state.coordinator = .collection payload ledger saved := by
    simpa only [x] using hstate
  have hcoreRoot :=
    ReferenceCompleteCollectionDispatchCore.complete_collection_dispatch_core
      rate rewards C_star C_h source
  dsimp only at hcoreRoot
  obtain ⟨u, hu, core, scores, started, hstart, _hpendingFrame, hempty⟩ :=
    hcoreRoot k payload ledger saved (by simpa only [x] using hstate)
  obtain ⟨instruction, hassignment, hinstructionTime⟩ := hempty hpending
  let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved u
  let input := ReferenceActivePhysicalStep.collectionInput x payload ledger clock u
  have hinputLedger : input.ledger = ledger := rfl
  have hinputTime : input.time = x.time := rfl
  have hpendingInput : input.ledger.pending = ∅ := by
    rw [hinputLedger]
    exact hpending
  have hfreezeInput : input.ledger.freezeAt ≤ input.time.val + 1 := by
    rw [hinputLedger, hinputTime]
    exact hfreeze
  let operationLedger := CoordinatorRoundDispatch.collectionOperationLedger
    input core.payload_n_eq
  have hpendingOperation : operationLedger.pending = ∅ := by
    simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger] using
      hpendingInput
  let registers := AssignmentScoreReconstruction.extractCompleteRegisters
    operationLedger core.ledger_valid hpendingOperation
  have hmassRoot :=
    ReferenceCompleteCoordinatorMass.complete_coordinator_input_output_mass
      rate rewards C_star C_h source
  dsimp only at hmassRoot
  have hmass := (hmassRoot k).1
  unfold ReferenceCompleteCoordinatorMass.coordinatorInputMass at hmass
  rw [hstate] at hmass
  have hcurrentDomains :
      AssignmentScoreReconstruction.currentOutputDomainsCheck operationLedger = true := by
    unfold AssignmentScoreReconstruction.currentOutputDomainsCheck
    apply allFin_eq_true_of_forall
    intro a
    have hcut : ledger.cutoffRegisters a = some (registers.cutoff a) := by
      simpa [registers, operationLedger,
        CoordinatorRoundDispatch.collectionOperationLedger, input,
        ReferenceActivePhysicalStep.collectionInput, hinputLedger] using registers.cutoff_eq a
    have hcurrent : ledger.currentRegisters a = some (registers.current a) := by
      simpa [registers, operationLedger,
        CoordinatorRoundDispatch.collectionOperationLedger, input,
        ReferenceActivePhysicalStep.collectionInput, hinputLedger] using registers.current_eq a
    have hcutOperation : operationLedger.cutoffRegisters a =
        some (registers.cutoff a) := by
      simpa [registers] using registers.cutoff_eq a
    have hcurrentOperation : operationLedger.currentRegisters a =
        some (registers.current a) := by
      simpa [registers] using registers.current_eq a
    have hbound := hmass a (registers.cutoff a) (registers.current a) hcut hcurrent
    have hboundAligned :
        (registers.cutoff a).score + operationLedger.increment a +
            (registers.current a).queue ≤ x.time.val * D p := by
      simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
        registers, input, ReferenceActivePhysicalStep.collectionInput,
        hinputLedger, hinputTime] using hbound.1
    have htimeBound : x.time.val * D p ≤ p.T * D p :=
      Nat.mul_le_mul_right (D p) (Nat.le_of_lt x.time.isLt)
    have hscore : (registers.cutoff a).score + operationLedger.increment a ≤
        p.T * D p := by
      omega
    have hqueue : (registers.current a).queue ≤ p.T * D p := by
      omega
    have hpair :
        decide ((registers.cutoff a).score + operationLedger.increment a ≤ p.T * D p) &&
          decide ((registers.current a).queue ≤ p.T * D p) = true := by
      simp [hscore, hqueue]
    change (match operationLedger.cutoffRegisters a, operationLedger.currentRegisters a with
      | some cutoff, some current =>
          decide (cutoff.score + operationLedger.increment a ≤ p.T * D p) &&
            decide (current.queue ≤ p.T * D p)
      | _, _ => false) = true
    rw [hcutOperation, hcurrentOperation]
    exact hpair
  have hpreviousDomains :
      AssignmentScoreReconstruction.previousOutputDomainsCheck operationLedger instruction =
        true := by
    have hafter : operationLedger.freezeAt ≤ instruction.time.val + 1 := by
      change ledger.freezeAt ≤ instruction.time.val + 1
      omega
    have hafterLedger : ledger.freezeAt ≤ instruction.time.val + 1 := by
      simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
        hinputLedger] using hafter
    simp [AssignmentScoreReconstruction.previousOutputDomainsCheck,
      operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
      input, ReferenceActivePhysicalStep.collectionInput, hafterLedger]
  have hready : operationLedger.phase = .ready := by
    change ledger.phase = .ready
    simpa [ReferenceActivePhysicalStep.collectionInput] using core.ledger_ready
  have hcursor : operationLedger.cursor = instruction.time.val + 1 := by
    change ledger.cursor = instruction.time.val + 1
    simpa [CoordinatorCollectionUpRoundStep.sourceRound,
      ReferenceActivePhysicalStep.collectionInput, hinstructionTime] using
      core.ledger_cursor_eq
  have hvalid : CoordinatorCollectionLedger.validLedgerCheck operationLedger = true := by
    have hvalidInput : CoordinatorCollectionLedger.validLedgerCheck input.ledger = true :=
      core.ledger_valid
    simpa only [CoordinatorCollectionLedger.validLedgerCheck,
      CoordinatorCollectionLedger.registerDomainsCheck,
      CoordinatorCollectionLedger.readyHistoryCheck,
      CoordinatorCollectionLedger.startedHistoryCheck,
      CoordinatorCollectionLedger.rawEntryDomainsCheck,
      CoordinatorCollectionLedger.armPendingCheck,
      operationLedger, CoordinatorRoundDispatch.collectionOperationLedger] using hvalidInput
  have hkindClock := CoordinatorPhaseClock.startRound_assignment_effect
    p input.etaReal input.time input.clock ledger.pending started instruction
    core.clock_parameter_valid core.clock_registers_valid core.clock_start_time_valid
    hstart hassignment
  rcases hkindClock with ⟨htimeClock, hkindClass, hsigma, huNone, hgrid, hproposal,
    hpendingFull, hcommand⟩
  have hfreezeInstruction : operationLedger.freezeAt ≤ instruction.time.val + 1 := by
    calc
      operationLedger.freezeAt = input.ledger.freezeAt := by
        simp [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger]
      _ ≤ input.time.val + 1 := hfreezeInput
      _ = instruction.time.val + 1 := by rw [← htimeClock]
  have hkind : instruction.kind = .renewal := by
    have hgridRenewal : input.clock.g ≤ FollowerCutoffScan.calendarRound input.time := by
      rw [← core.ledger_freeze_eq]
      change ledger.freezeAt ≤ input.time.val + 1
      simpa [input, ReferenceActivePhysicalStep.collectionInput] using hfreeze
    rw [hkindClass]
    rw [core.clock_sigma_eq]
    simp [CoordinatorPhaseClock.classifyAssignmentStart,
      hgridRenewal]
  have hkindExpected : instruction.kind =
      AssignmentScoreReconstruction.expectedLaterStartKind operationLedger.freezeAt instruction.time := by
    rw [hkind]
    simp [AssignmentScoreReconstruction.expectedLaterStartKind, hfreezeInstruction]
  have hcutoffCursor : operationLedger.cutoff ≤ operationLedger.cursor := by
    have h := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck,
      Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
  have hcutoff : operationLedger.cutoff ≤ instruction.time.val + 1 := by
    rw [← hcursor]
    exact hcutoffCursor
  let reconstruction : AssignmentScoreReconstruction.ReconstructedStart
      operationLedger instruction := {
    registers := registers
    currentScore_le := by
      intro a
      have hcut : ledger.cutoffRegisters a = some (registers.cutoff a) := by
        simpa [registers, operationLedger,
        CoordinatorRoundDispatch.collectionOperationLedger, hinputLedger] using registers.cutoff_eq a
      have hcurrent : ledger.currentRegisters a = some (registers.current a) := by
        simpa [registers, operationLedger,
        CoordinatorRoundDispatch.collectionOperationLedger, hinputLedger] using registers.current_eq a
      have h := hmass a (registers.cutoff a) (registers.current a) hcut hcurrent
      have ht := Nat.mul_le_mul_right (D p) (Nat.le_of_lt x.time.isLt)
      have hbound : (registers.cutoff a).score + operationLedger.increment a +
          (registers.current a).queue ≤ x.time.val * D p := by
        simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
          registers, input, ReferenceActivePhysicalStep.collectionInput,
          hinputLedger, hinputTime] using h.1
      omega
    initialQueue_le := by
      intro a
      have hcut : ledger.cutoffRegisters a = some (registers.cutoff a) := by
        simpa [registers, operationLedger,
          CoordinatorRoundDispatch.collectionOperationLedger, hinputLedger] using registers.cutoff_eq a
      have hcurrent : ledger.currentRegisters a = some (registers.current a) := by
        simpa [registers, operationLedger,
          CoordinatorRoundDispatch.collectionOperationLedger, hinputLedger] using registers.current_eq a
      have h := hmass a (registers.cutoff a) (registers.current a) hcut hcurrent
      have ht := Nat.mul_le_mul_right (D p) (Nat.le_of_lt x.time.isLt)
      have hbound : (registers.cutoff a).score + operationLedger.increment a +
          (registers.current a).queue ≤ x.time.val * D p := by
        simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
          registers, input, ReferenceActivePhysicalStep.collectionInput,
          hinputLedger, hinputTime] using h.1
      omega
    previousScore_nonnegative := by
      intro a hbefore
      have hafter : operationLedger.freezeAt ≤ instruction.time.val + 1 := by
        change ledger.freezeAt ≤ instruction.time.val + 1
        omega
      omega
    previousScore_le := by
      intro a hbefore
      have hafter : operationLedger.freezeAt ≤ instruction.time.val + 1 := by
        change ledger.freezeAt ≤ instruction.time.val + 1
        omega
      omega }
  have hreconstruction :
      AssignmentScoreReconstruction.reconstructLaterStart operationLedger instruction =
        .success operationLedger instruction reconstruction := by
    simp [AssignmentScoreReconstruction.reconstructLaterStart, hvalid, hready,
      hcursor, hpendingOperation, hkindExpected, hcurrentDomains, hpreviousDomains,
      reconstruction, registers]
  have hsuccessEquations :=
    AssignmentScoreReconstruction.reconstructLaterStart_success_equations
      operationLedger instruction reconstruction hreconstruction
  rcases hsuccessEquations with
    ⟨_, _, hregistersCurrent, hsourceScore, hinitialQueue, hcurrentWeight,
      _hcutoffWeight, hcurrentPos, hcutoffPos, _, _⟩
  have hconsistent : LaterAssignmentStartOperation.LocalConsistency
      input.payload operationLedger := {
    oldStart_eq := by
      simpa [CoordinatorRecorderComplementBridge.sourceStart,
        operationLedger, CoordinatorRoundDispatch.collectionOperationLedger] using
        core.ledger_sigma_eq.symm
    oldAssignment_eq := by
      intro i
      simpa [operationLedger,
        CoordinatorRoundDispatch.collectionOperationLedger] using
        (core.assignment_eq i).symm
    oldFreezeAt := ledger.freezeAt
    oldFreezeAt_eq := rfl }
  have hfreezeClock : input.clock.g = hconsistent.oldFreezeAt := by
    calc
      input.clock.g = ledger.freezeAt := core.ledger_freeze_eq.symm
      _ = hconsistent.oldFreezeAt := hconsistent.oldFreezeAt_eq.symm
  have hcutoffBound : operationLedger.cutoff ≤ instruction.time.val + 1 := hcutoff
  obtain ⟨output, hlocal, normalized, sampled, hlater, hmassLaw, hsample⟩ :=
    renewal_sample_start input.payload operationLedger instruction input.row hconsistent
      reconstruction hreconstruction hcutoffBound hcurrentPos hcutoffPos hkind
  have houtputEquations := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
    operationLedger instruction output.reconstruction output.reconstruction_eq
  rcases houtputEquations with
    ⟨_, _, _, hsourceScoreOutput, hinitialQueueOutput, hcurrentWeightOutput, _⟩
  have hfreeze : input.clock.g = output.localConsistency.oldFreezeAt := by
    calc
      input.clock.g = ledger.freezeAt := core.ledger_freeze_eq.symm
      _ = hconsistent.oldFreezeAt := hconsistent.oldFreezeAt_eq.symm
      _ = output.localConsistency.oldFreezeAt := by rw [hlocal]
  let clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output := {
    priorClock := input.clock
    pending := input.ledger.pending
    proposalParameterValid := core.clock_parameter_valid
    priorClockValid := core.clock_registers_valid
    startTimeValid := by rw [htimeClock]; exact core.clock_start_time_valid
    result := started
    startRound_eq := by rw [htimeClock]; exact hstart
    assignmentStart_eq := hassignment
    priorSigma_eq := core.clock_sigma_eq
    priorGrid_eq_freezeAt := hfreeze }
  let installation := CoordinatorAssignmentRegisterInstall.installLater output clockData
  have hdomains := CoordinatorAssignmentRegisterInstall.later_register_domains output clockData
  have hbase : ∀ i, installation.retainedBaseScore i ≤ p.T * D p := by
    intro i
    rw [CoordinatorAssignmentRegisterInstall.later_retained_base_score_eq_source
      output clockData i, hsourceScoreOutput]
    exact output.reconstruction.currentScore_le (output.payload.assignment.assigned i)
  have hchoice := collection_choice_inputs_valid_of_renewal output clockData hkind
  have henvelope : installation.registers.complementEnvelopeValid := by
    intro j
    have hanchor := CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
      output clockData hkind
    have hanchor' : installation.registers.payload.anchor j.1 =
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
      congrFun hanchor j.1
    have hweight : installation.registers.complementWeights j =
        AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 := rfl
    rw [hanchor', hweight]
    exact ⟨le_rfl, by
        have hnonneg := (output.currentWeight_pos j.1).le
        calc
          AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 ≤
              AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 +
                AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
            le_add_of_nonneg_right hnonneg
          _ = 2 * AssignmentScoreReconstruction.currentWeight output.reconstruction j.1 :=
            (two_mul _).symm⟩
  obtain ⟨selection, hdispatch⟩ := dispatchCollection_laterChosen input core
    started hstart instruction hassignment hconsistent output hlocal
    (by simpa [input, x] using htimeClock) hfreeze hpendingOperation hlater hbase
    (by simpa [installation, clockData, hinputLedger,
      CoordinatorAssignmentRegisterInstall.installLater] using hchoice)
    (by simpa [installation, clockData, hinputLedger,
      CoordinatorAssignmentRegisterInstall.installLater] using henvelope)
  have hcutoffRange : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T := by
    have h := core.ledger_valid
    simp only [CoordinatorCollectionLedger.validLedger, CoordinatorCollectionLedger.validLedgerCheck,
      Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
  have hcutoffVal : ledger.cutoff - 1 = u.val := by omega
  let physicalCutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
  have hphysicalCutoff : physicalCutoff = u := Fin.ext hcutoffVal
  have hprepare : (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload ledger clock u
        (CoordinatorRoundDispatch.dispatchCollection input) := by
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate', dite_eq_left hcutoffRange, CoordinatorRoundDispatch.dispatch]
    change DispatchCut.collection payload ledger
        (ReferenceActivePhysicalStep.collectionClock payload ledger saved physicalCutoff)
        physicalCutoff
        (CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger
            (ReferenceActivePhysicalStep.collectionClock payload ledger saved physicalCutoff)
            physicalCutoff)) = _
    have hclockCut :
        ReferenceActivePhysicalStep.collectionClock payload ledger saved physicalCutoff = clock := by
      simp [clock, hphysicalCutoff]
    rw [hclockCut, hphysicalCutoff]
  let physicalSelection : ReferenceActivePhysicalStep.Selection x := {
    view := {
      payload := installation.registers.payload
      pendingAtChoice := started.pending
      cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
      complementWeights := installation.registers.complementWeights }
    started := started
    pending_eq := rfl
    cutoff_eq := rfl
    arm := selection.arm
    choice_eq := by
      have hrow : input.row = x.row := rfl
      change CoordinatorLocalArmChoice.coordinatorArmChoice
        installation.registers.payload started.pending
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
        x.time installation.registers.complementWeights x.row = some selection.arm
      simpa only [hinstructionTime, hrow] using selection.armChoice_eq }
  have hphysicalSelection :
      ReferenceActivePhysicalStep.DispatchCut.selection
        (ReferenceActivePhysicalStep.prepare x).coordinator = some physicalSelection := by
    simp only [hprepare, hdispatch, ReferenceActivePhysicalStep.DispatchCut.selection]
    change ReferenceActivePhysicalStep.selectionAt x installation.registers.payload
      started instruction.time installation.registers.complementWeights selection =
        some physicalSelection
    unfold ReferenceActivePhysicalStep.selectionAt
    split
    · rfl
    · rename_i hwrongTime
      exact False.elim (hwrongTime hinstructionTime)
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive
      physicalSelection.view.payload physicalSelection.view.cutoff x.time := by
    have hsigma := CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
      output clockData
    rcases hsigma with ⟨_, hnewSigma, hnewCutoff, _, _, _, _, _, _⟩
    have huNoneStarted : started.clock.u = none := by
      simpa [clockData] using hnewCutoff
    constructor
    · change output.payload.sigma.val + 1 ≤ x.time.val + 1
      rw [output.payload_start, hinstructionTime]
    · change x.time.val + 1 < CoordinatorLocalArmChoice.cutoffRound
        (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
      rw [huNoneStarted]
      simp [CoordinatorLocalArmChoice.cutoffRound,
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock]
  refine ⟨u, hu, ?_⟩
  refine ⟨core, ?_⟩
  refine ⟨scores, ?_⟩
  refine ⟨started, ?_⟩
  refine ⟨?_, instruction, ?_⟩
  · simpa [input, ReferenceActivePhysicalStep.collectionInput] using hstart
  refine ⟨hassignment, ?_⟩
  refine ⟨?_, ?_⟩
  · exact hinstructionTime
  refine ⟨hkind, ?_⟩
  let consistentTarget : LaterAssignmentStartOperation.LocalConsistency
      input.payload operationLedger := {
      oldStart_eq := by
        simpa [CoordinatorRecorderComplementBridge.sourceStart,
          operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
          input, ReferenceActivePhysicalStep.collectionInput] using core.ledger_sigma_eq.symm
      oldAssignment_eq := by
        intro i
        simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
          input, ReferenceActivePhysicalStep.collectionInput] using (core.assignment_eq i).symm
      oldFreezeAt := ledger.freezeAt
      oldFreezeAt_eq := rfl }
  have hconsistentEq : hconsistent = consistentTarget := by
    cases hconsistent with
    | mk hstartOld hassignmentOld oldFreeze hfreezeOld =>
      cases consistentTarget with
      | mk hstartTarget hassignmentTarget targetFreeze hfreezeTarget =>
        have hfreezeOld' : oldFreeze = ledger.freezeAt := by
          simpa [operationLedger, CoordinatorRoundDispatch.collectionOperationLedger,
            input, ReferenceActivePhysicalStep.collectionInput, hinputLedger] using hfreezeOld
        subst oldFreeze
        subst targetFreeze
        rfl
  have hlocalOut : output.localConsistency = consistentTarget := by
    exact hlocal.trans hconsistentEq
  have hdispatchOut : CoordinatorRoundDispatch.dispatchCollection input =
      .laterChosen core consistentTarget started hstart instruction hassignment
        output hlocalOut clockData installation selection := by
    simpa only [hconsistentEq, hlocalOut] using hdispatch
  have hlaterOut : LaterAssignmentStartOperation.laterAssignmentStart input.payload
      operationLedger instruction input.row consistentTarget =
        .success output hlocalOut := by
    simpa using (hconsistentEq ▸ hlater)
  refine ⟨output, hlocalOut, ?_⟩
  refine ⟨hlaterOut, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hsourceScoreOutput
  · exact hinitialQueueOutput
  · exact hcurrentWeightOutput
  · exact CoordinatorAssignmentRegisterInstall.later_payload_anchor_renewal
      output clockData hkind
  · intro a
    exact output.payload_queues a
  · exact hdomains
  · exact hbase
  · rcases CoordinatorAssignmentRegisterInstall.later_start_round_compatibility
      output clockData with ⟨hkindInstall, hsigmaInstall, huInstall, hgridInstall,
        _, hpendingInstall, hcommandInstall, _, _⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [input] using hkindInstall
    · simpa [hinstructionTime] using hsigmaInstall
    · exact huInstall
    · simpa [hinstructionTime, clockData, input,
        ReferenceActivePhysicalStep.collectionInput] using hgridInstall
    · exact hpendingInstall
    · exact hcommandInstall
  · refine ⟨normalized, sampled, ?_, hsample, ?_⟩
    · exact hmassLaw
    · constructor
      · simpa [input, ReferenceActivePhysicalStep.collectionInput, x] using
          output.assignmentVector_eq_row_projection
      · refine ⟨selection, hdispatchOut, ?_⟩
        refine ⟨hprepare, physicalSelection, hphysicalSelection, rfl, rfl, ?_⟩
        exact hlive

end Bandits.Support.ReferenceCompleteEmptyCollectionRenewalChoiceDomains

end
