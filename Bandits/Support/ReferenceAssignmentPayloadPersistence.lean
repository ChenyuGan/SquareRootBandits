/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalHorizon
public import Bandits.Support.ActualInitializationLaunchState

/-!
# Assignment payload persistence on the computed physical horizon

The assignment record fixes the complete DOWN payload at its actual
installation. This module defines the stored-payload projection and proves
local installation and tail-frame facts on actual physical records. The
source ranges are `sources/zip4/manuscript/05_binary_transport.tex:62-68,74-78`,
`sources/zip4/manuscript/06_interruptions.tex:41-69,162,273-282,327-348`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:100-106`.

The exported facts do not yet establish run-wide payload birth, equal-start
payload identity, DOWN-word constancy, the separate joint reconstruction,
recorded-history, or regret obligations.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ActualInitializationLaunchState

namespace Bandits.Support.ReferenceAssignmentPayloadPersistence

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

/-- The literal optional payload stored by the coordinator configuration.
Only live and collection configurations contain an assignment payload. -/
def storedPayload : CoordinatorConfiguration p rate → Option (Payload rate)
  | .first => none
  | .live registers _ _ => some registers.payload
  | .collection payload _ _ => some payload
  | .dagger => none

@[simp] theorem storedPayload_first :
    storedPayload (p := p) (rate := rate) .first = none := rfl

@[simp] theorem storedPayload_live
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ) :
    storedPayload (.live registers owned base) = some registers.payload := rfl

@[simp] theorem storedPayload_collection
    (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool)) :
    storedPayload (.collection payload ledger proposal) = some payload := rfl

@[simp] theorem storedPayload_dagger :
    storedPayload (p := p) (rate := rate) .dagger = none := rfl

/-- A birth is one of the two actual installation constructors retained in a
round's dispatcher result. Its timestamp is part of the birth witness. -/
def InstallationBirth (record : RoundRecord (p := p) (rate := rate))
    (payload : Payload rate) : Prop :=
  match record.output.preparation.coordinator with
  | .first (.chosen installed _) =>
      payload = installed.registers.payload ∧
        payload.sigma.val = record.input.time.val
  | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
      payload = installed.registers.payload ∧
        payload.sigma.val = record.input.time.val
  | _ => False

/-- The selected payload retained by one actual physical record. -/
def selectedPayload (record : RoundRecord (p := p) (rate := rate)) :
    Option (Payload rate) :=
  record.output.preparation.coordinator.selection.map fun selected =>
    selected.view.payload

/-- The first chosen dispatcher branch timestamps its exact installed payload
at the physical time of that computed round. -/
theorem firstChosen_payload_time (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selection) :
    installed.registers.payload.sigma.val = x.time.val := by
  have htime := ReferenceActivePhysicalStep.dispatchFirst_chosen_time
    x installed selection hchosen
  have hpayloadTime : installed.registers.payload.sigma = installed.registers.time := by
    rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
      x installed selection hchosen]
    simp [CoordinatorAssignmentRegisterInstall.installFirst,
      CoordinatorAssignmentRegisterInstall.firstRegisters,
      AssignmentStartPayload.Input.ofFirstAssignment,
      FirstAssignmentLaunch.Input.start]
  exact congrArg Fin.val (hpayloadTime.trans htime)

/-- Given the actual `installLater` constructor equality, the later payload's
timestamp is the physical time of its chosen dispatcher branch. The equality
is an explicit input because the installation carrier itself has no frame
field. -/
theorem laterPayload_time_of_actual_installation (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val x.time clock ledger.pending =
      .ok started)
    (hinstruction : started.assignmentStart = some instruction)
    (output : LaterAssignmentStartOperation.SuccessfulStart payload
      (CoordinatorRoundDispatch.collectionOperationLedger
        (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
        core.payload_n_eq) instruction x.row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (hinstalled : installed =
      CoordinatorAssignmentRegisterInstall.installLater output clockData) :
    installed.registers.payload.sigma.val = x.time.val := by
  have htime := ReferenceActivePhysicalStep.later_instruction_time x payload ledger clock cutoff
    core started instruction hstart hinstruction
  have hpayloadTime : installed.registers.payload.sigma = instruction.time := by
    rw [hinstalled]
    change output.payload.sigma = instruction.time
    exact output.payload_start
  exact congrArg Fin.val (hpayloadTime.trans htime)

/-- Every successful live post-choice tail keeps the whole payload in its
registers; any rejected tail enters the payload-free dagger configuration. -/
theorem livePostChoice_payload_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    storedPayload (ReferenceActivePhysicalStep.livePostChoice
      prepared registers owned base started).configuration = none ∨
      storedPayload (ReferenceActivePhysicalStep.livePostChoice
        prepared registers owned base started).configuration = some registers.payload := by
  classical
  unfold ReferenceActivePhysicalStep.livePostChoice
  cases CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.liveRecordingInput prepared registers started) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
  | some recording =>
    cases hservice : CoordinatorLiveServiceFinish.servicePass registers owned recording with
    | error reason =>
      simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | ok serviced =>
      cases hconfirmation : CoordinatorLocalArmChoice.confirmationUpdate registers.payload
          started.pending (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          x.time x.row prepared.coordinatorObservation with
      | none =>
        simp [hservice, ReferenceActivePhysicalStep.coordinatorFailure,
          storedPayload]
      | some pending =>
        cases hfinish : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
            started.clock pending x.row with
        | error reason =>
          simp [hservice, hfinish,
            ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
        | ok finished =>
          simp [hservice, hfinish, storedPayload]

/-- Filtered UP reception and FinishRound retain the collection payload on a
successful result. Rejections and failed finish checks expose no payload. -/
theorem collectionFinish_payload_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : Payload rate) (started : CoordinatorPhaseClock.StartRoundResult p)
    (recording : CoordinatorRecordingOperation.Output p)
    (cut : ReferenceActivePhysicalStep.UpCut p rate) :
    storedPayload (ReferenceActivePhysicalStep.collectionFinish
      (x := x) payload started recording cut).configuration = none ∨
      storedPayload (ReferenceActivePhysicalStep.collectionFinish
        (x := x) payload started recording cut).configuration = some payload := by
  classical
  unfold ReferenceActivePhysicalStep.collectionFinish
  cases cut.result with
  | invalid => simp [ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
  | success pair =>
    rcases pair with ⟨ledger, _⟩
    cases hledger : CoordinatorCollectionLedger.finishRound ledger with
    | invalid =>
      simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | rejected _ =>
      simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | success ledgerFinished =>
      cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
          started.clock ledgerFinished.pending x.row with
      | error reason =>
        simp [hledger, hclock, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
      | ok _ =>
        simp [hledger, hclock, storedPayload]
  | rejected pair =>
    rcases pair with ⟨ledger, _⟩
    cases hledger : CoordinatorCollectionLedger.finishRound ledger with
    | invalid =>
      simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | rejected _ =>
      simp [hledger, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | success ledgerFinished =>
      cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
          started.clock ledgerFinished.pending x.row with
      | error reason =>
        simp [hledger, hclock, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
      | ok _ =>
        simp [hledger, hclock, storedPayload]

/-- Collection service, freezing, reception, decoding, and FinishRound all
carry the complete existing payload on success; each checked failure remains
the payload-free dagger branch. -/
theorem collectionPostChoice_payload_frame
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) :
    storedPayload (ReferenceActivePhysicalStep.collectionPostChoice
      (x := x) prepared payload ledger started weights).configuration = none ∨
      storedPayload (ReferenceActivePhysicalStep.collectionPostChoice
        (x := x) prepared payload ledger started weights).configuration = some payload := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice
  cases CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none => simp [ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
  | some recording =>
    cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
    | invalid =>
      simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | rejected _ =>
      simp [hstart, ReferenceActivePhysicalStep.coordinatorFailure, storedPayload]
    | success ledgerStarted =>
      simpa only [hstart] using collectionFinish_payload_frame (x := x) payload started
        recording (ReferenceActivePhysicalStep.receiveUp prepared ledgerStarted)

/-- The first installed DOWN payload carries the zero queue of the actual
first launch constructor. -/
theorem firstPayload_down_queue_zero
    (source : FirstAssignmentLaunch.Input p rate.eta)
    (i : ActiveRoundActions.Follower p.m) :
    ((CoordinatorAssignmentRegisterInstall.installFirst source).registers.payload.downRecord i).val.q =
      0 := by
  rw [(CoordinatorAssignmentRegisterInstall.installFirst source).registers.payload.downRecord_initialQueue i,
    CoordinatorAssignmentRegisterInstall.first_payload_queues_eq_start]
  exact FirstAssignmentLaunch.Input.start_queues_zero source _

/-- The actual first chosen dispatcher branch uses that first-start zero q. -/
theorem firstChosen_down_queue_zero
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selection)
    (i : ActiveRoundActions.Follower p.m) :
    (installed.registers.payload.downRecord i).val.q = 0 := by
  rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    x installed selection hchosen]
  exact firstPayload_down_queue_zero _ i

/-- Every field of a first chosen payload is the field of the exact first
assignment input that the dispatcher installed. -/
theorem firstChosen_payload_eq_input
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selection) :
    installed.registers.payload = AssignmentStartPayload.Input.ofFirstAssignment
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)) := by
  rw [ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    x installed selection hchosen]
  exact CoordinatorAssignmentRegisterInstall.first_registers_payload _

/-- Reuse the checked first dispatcher seed equations for every zero-valued
complement score, owned queue, previous service, and follower base score. -/
theorem firstChosen_zero_seed
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (installed : CoordinatorAssignmentRegisterInstall.FirstInstallation
      (CoordinatorRoundDispatch.firstLaunchInput (ReferenceActivePhysicalStep.firstInput x)))
    (selection : CoordinatorRoundDispatch.ArmSelection installed.registers.payload
      installed.startRoundResult installed.registers.time installed.registers.complementWeights x.row)
    (hchosen : CoordinatorRoundDispatch.dispatchFirst
      (ReferenceActivePhysicalStep.firstInput x) = .chosen installed selection) :
    (∀ a, installed.registers.complementScores a = 0) ∧
    (∀ a, installed.ownedRegisters.queue a = 0) ∧
    (∀ a, installed.ownedRegisters.previousService a = 0) ∧
    (∀ i, installed.followerBaseScore i = 0) :=
  ReferenceActivePhysicalStep.dispatchFirst_zero_seed x installed selection hchosen

/-- At a genuine later chosen installation, the payload's original DOWN q is
the initial queue from that installation's actual reconstruction. -/
theorem laterPayload_down_queue_reconstruction
    {old : AssignmentStartPayload.Input p rate.eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (hinstalled : installed =
      CoordinatorAssignmentRegisterInstall.installLater output clockData)
    (arm : Fin p.K) :
    installed.registers.payload.queues arm =
      AssignmentScoreReconstruction.initialQueue output.reconstruction arm := by
  rw [hinstalled]
  change output.payload.queues arm = _
  exact output.payload_queues arm

/-- Under the explicit actual-constructor equality, every field of the later
payload is the exact field produced by `SuccessfulStart`. -/
theorem laterPayload_eq_successfulStart
    {old : AssignmentStartPayload.Input p rate.eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row)
    (clockData : CoordinatorAssignmentRegisterInstall.LaterStartRoundEvidence output)
    (installed : CoordinatorAssignmentRegisterInstall.LaterInstallation output clockData)
    (hinstalled : installed =
      CoordinatorAssignmentRegisterInstall.installLater output clockData) :
    installed.registers.payload = output.payload := by
  rw [hinstalled]
  rfl

/-- The actual combined launch has no stored assignment payload before its
first physical StartRound. Its full source boundary hypotheses remain visible. -/
theorem actualBoundary_payload_mode_and_activity
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched
    storedPayload initial.coordinator = none ∧
      allActiveAtStart initial
        (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)) ∧
      (∀ time : Fin p.T,
        BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) ≤ time.val →
          ∀ i, (initial.activations i).val ≤ time.val + 1) := by
  let initial := ActualInitializationLaunchState.ofActualLaunchedBoundary
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
    hlaunched
  refine ⟨?_, ?_, ?_⟩
  · change storedPayload initial.coordinator = none
    rw [ActualInitializationLaunchState.ofActualLaunchedBoundary_coordinator
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched]
    rfl
  · change allActiveAtStart initial
      (BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h))
    intro i
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activation_le_blockStop
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched i
  · intro time htime i
    exact ActualInitializationLaunchState.ofActualLaunchedBoundary_activeAtTime
      source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed
      hlaunched time htime i

end Bandits.Support.ReferenceAssignmentPayloadPersistence

end
