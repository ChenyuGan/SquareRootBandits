/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedNextOutsideCalendarReplay

/-!
# Conditional per-operation later collection readout

For an actual complete-source physical record, the two collection constructors
produce their canonical numerical SOME readout once the actual payload is
strictly later than the physical start and its true cutoff is no later than the
current date. The proof derives prepared-follower unoccupied status from the
selected payload's actual DOWN records, START, and the complete-source cutoff
status/token facts. It retains the original recorder, whole reward row, rates,
dated input, and disabled-zero behavior. No readout is asserted for other
coordinator constructors.

Sources: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ReferenceLaterCollectionArrivalReadout

namespace Bandits.Support.ReferenceCompleteLaterCollectionCalendarReadout

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem preparedFollowersUnoccupied_of_actual_selection
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (selected : ReferenceActivePhysicalStep.Selection
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input)
    (hselection : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some selected)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (hpayload : selected.view.payload = payload)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.row) ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  obtain ⟨states, memories, hstates, hdown, _hinputFields, _houtputFields⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h source k selected hselection
  intro i
  change match (ReferenceFollowerFixedReply.actualChoice record i).configuration with
    | .ordinary state _ => state.status = .unoccupied
    | .dagger => False
  rw [hstates i]
  by_contra hbusy
  have hcurrent := hdown i hbusy
  rw [hpayload] at hcurrent
  obtain ⟨before, memory, choice, hbefore, _hdomain, hstart, hchoice,
      _hchoiceDomain, _hoperationDomain⟩ :=
    ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
      (rate := rate) rewards C_star C_h source k i
  have hchoiceEq := DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
    (hchoice.symm.trans (hstates i))
  have hchoiceDown : choice.lastDown = some (payload.downRecord i) := by
    rw [hchoiceEq.1]
    exact hcurrent
  have hbeforeDown : before.lastDown = some (payload.downRecord i) :=
    (ActiveFollowerLifecycle.startRound_frame rate.eta record.input.time before
      choice memory memory hstart).1.symm.trans hchoiceDown
  have hphase := ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_phase
    rate rewards C_star C_h source k i before memory hbefore
      (payload.downRecord i) hbeforeDown
  have htoken : before.status ≠ .unoccupied → ∃ stamp : Fin p.T,
      stamp.val + 1 = record.input.time.val ∧
        memory.lastProposalRead = some ⟨stamp,
          FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row stamp⟩ := by
    intro hoccupied
    exact ReferenceCompleteFollowerCutoffPhase.complete_ordinary_follower_token
      rate rewards C_star C_h source k i before memory hbefore hoccupied
  have hstatus := ReferenceAssignmentFollowerMassSteps.start_round_cutoff_status
    (rate := rate) record.input.time record.input.row before choice memory memory
      (payload.downRecord i) hbeforeDown hphase htoken hstart
  have hstartPayload : ActiveFollowerDownAcceptance.downStart p rate
      (payload.downRecord i) = payload.sigma := by
    apply Fin.ext
    have hval := ActiveFollowerDownAcceptance.downStart_val_add_one p rate
      (payload.downRecord i)
    rw [payload.downRecord_fields i] at hval
    exact Nat.add_right_cancel hval
  have hchoiceUnoccupied : choice.status = .unoccupied :=
    hstatus.mpr (by rw [hstartPayload]; exact hcut)
  exact hbusy (hchoiceEq.1 ▸ hchoiceUnoccupied)

private theorem actual_collection_selection_payload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff) = true)
    (hcoord : record.output.preparation.coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores)) :
    ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      record.output.preparation.coordinator.selection = some selected ∧
        selected.view.payload = payload := by
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hpreparedCoord : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) := by
    have hc := congrArg (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input =>
      prepared.coordinator) hprep.symm
    exact hc.trans hcoord
  have hselection : ∃ selected : ReferenceActivePhysicalStep.Selection record.input,
      (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection = some selected := by
    rw [hpreparedCoord]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection]
  rcases hselection with ⟨selected, hselected⟩
  have hselected' : record.output.preparation.coordinator.selection = some selected := by
    have hc := congrArg (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input =>
      prepared.coordinator.selection) hprep
    exact hc.trans hselected
  have hselectedPayload : selected.view.payload = payload := by
    have h := hselected
    rw [hpreparedCoord] at h
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection] at h
    have heq := Option.some.inj h
    exact congrArg (fun value : ReferenceActivePhysicalStep.Selection record.input =>
      value.view.payload) heq.symm
  exact ⟨selected, hselected', hselectedPayload⟩

private theorem cutoff_collection_input_disabled_gate
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base)
    (selected : CoordinatorRoundDispatch.ArmSelection registers.payload dispatched.startResult
      record.input.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
      record.input.row)
    (henabled : (ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
      record registers owned base dispatched selected).enabled = false) :
    (ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
      record registers owned base dispatched selected).recordedArm = none := by
  classical
  have hmap := ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput_map_eq_projection
    record registers owned base dispatched selected
  dsimp only at hmap
  have hdisabled : decide (¬ CoordinatorRecordingOperation.isFrozen
      (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
          registers.payload dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights))) =
      false := by
    simpa only [ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput] using henabled
  rw [hdisabled] at hmap
  simpa [CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart,
    SnapshotRecordingKernel.recordingMap_disabled] using hmap

private theorem continuing_collection_input_disabled_gate
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (henabled : (ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
      record payload ledger clock cutoff snapshot).enabled = false) :
    (ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
      record payload ledger clock cutoff snapshot).recordedArm = none := by
  classical
  have hmap := ReferenceLaterCollectionArrivalReadout.continuingCollectionInput_map_eq_projection
    record payload ledger clock cutoff snapshot boundary
  dsimp only at hmap
  have hdisabled : decide (¬ CoordinatorRecordingOperation.isFrozen
      (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
          payload snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights
            (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)))) = false := by
    change _ = false at henabled
    exact henabled
  rw [hdisabled] at hmap
  simpa [CoordinatorRecordingOperation.collectionCoordinatorSourceMapPart,
    SnapshotRecordingKernel.recordingMap_disabled] using hmap

private theorem actual_collection_readout_call
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (c : RecordedQueueRun.RoundInput p.K)
    (hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h).get k) = some c)
    (hcallExpected : ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (started : CoordinatorPhaseClock.StartRoundResult p)
        (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ),
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h).get k) =
        some ⟨payload, ledger, started, weights⟩) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).get k
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    ∃ (callPayload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm callPayload.slowSet → ℝ)
      (out : CoordinatorRecordingOperation.Output p),
      callPayload = payload ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall s record =
        some ⟨callPayload, ledger, started, weights⟩ ∧
      record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
        record.output.preparation callPayload ledger started weights ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
          callPayload started weights) = some out ∧
      c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time ∧
      c.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
      c.rate = callPayload.rate ∧
      c.reward = (fun a => ((rewards record.input.time a).val : ℝ) / (D p : ℝ)) ∧
      record.coordinatorDiagnostics.recording = some out ∧
      out.gateArm = c.recordedArm ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a =
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
      (∀ a, CoordinatorCollectionLedger.localArrival
        (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a =
          RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) := by
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h).get k
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  change ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some c at hreadout
  change (∃ (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ),
    ReferenceLaterCollectionArrivalReadout.laterCollectionCall s record =
      some ⟨payload, ledger, started, weights⟩) at hcallExpected
  obtain ⟨callPayload, callLedger, callStarted, callWeights, callOut, hcall,
      hpost, hrun, henabled, henabledClock, hrate, hreward, hrecording,
      hgate, harrival⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call s record c hreadout
  obtain ⟨expectedLedger, expectedStarted, expectedWeights, hcallExpected⟩ := hcallExpected
  have hcallTuple := Option.some.inj (hcall.symm.trans hcallExpected)
  have hcallPayload : callPayload = payload := congrArg Sigma.fst hcallTuple
  obtain ⟨physicalPayload, physicalLedger, physicalStarted, physicalWeights,
      physicalOut, hphysicalCall, hphysicalRun, hphysicalRecording, hphysicalGate,
      hphysicalArrival, hphysicalRate, hphysicalReward, _hphysicalFormula⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_physical
      rate rewards C_star C_h source k c hreadout
  have hphysicalTuple := Option.some.inj (hphysicalCall.symm.trans hcallExpected)
  have hphysicalPayload : physicalPayload = payload := congrArg Sigma.fst hphysicalTuple
  have hout : callOut = physicalOut :=
    Option.some.inj (hrecording.symm.trans hphysicalRecording)
  refine ⟨callPayload, callLedger, callStarted, callWeights, callOut, hcallPayload,
    hcall, hpost, hrun, henabled, henabledClock, ?_, ?_, hrecording, hgate,
    harrival, ?_⟩
  · simpa only [hcallPayload] using hrate
  · exact hphysicalReward
  · intro a
    have hraw : ReferenceCollectionRawBufferHistory.rawDiagnostic record =
        CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder callOut := by
      change record.output.coordinator.recording = some callOut at hrecording
      simp [ReferenceCollectionRawBufferHistory.rawDiagnostic,
        CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, hrecording]
    rw [hraw, hout]
    exact hphysicalArrival a

/-- On an actual complete-source `.live` / `.cutoffChosen` preparation, strict
later start and the true-cutoff/date inequality imply the canonical numerical
SOME readout. The only logical inputs beyond the selected actual constructor
are those two displayed scalar conditions. -/
theorem complete_later_live_cutoff_collection_calendar_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (dispatched : CoordinatorStartRoundCutoffDispatch.Output
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time) base)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time).time
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time).priorClock
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time).clockPending =
        .ok dispatched.startResult)
    (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time))
    (hinit : dispatched.collectionInitialization = .success (some ledger))
    (hcand : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time) base
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
    (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt registers owned
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time) base
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
    (hclock : dispatched.startResult.clock =
      { (ReferenceActivePhysicalStep.liveRegistersAt registers
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val]'k.isLt).input.time).priorClock with
          u := some (ReferenceActivePhysicalStep.liveRegistersAt registers
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).input.time).time })
    (hpending : dispatched.startResult.pending = Finset.univ)
    (hnone : dispatched.startResult.assignmentStart = none)
    (selected : CoordinatorRoundDispatch.ArmSelection registers.payload dispatched.startResult
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time
      (ReferenceActivePhysicalStep.liveRegistersAt registers
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.time).complementWeights
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.row)
    (hbranch : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator =
      .live registers owned base
        (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected))
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
      registers.payload.sigma.val)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val registers.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.row) ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        record = some c ∧
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record ∧
      ∃ (callPayload : ReferenceActivePhysicalStep.Payload rate)
        (callLedger : ReferenceActivePhysicalStep.Ledger rate)
        (started : CoordinatorPhaseClock.StartRoundResult p)
        (weights : CanonicalFastSampling.FastArm callPayload.slowSet → ℝ)
        (out : CoordinatorRecordingOperation.Output p),
        callPayload = registers.payload ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          record = some ⟨callPayload, callLedger, started, weights⟩ ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
            callPayload started weights) = some out ∧
        record.coordinatorDiagnostics.recording = some out ∧
        c.rate = callPayload.rate ∧
        c.reward = (fun a => ((rewards record.input.time a).val : ℝ) / (D p : ℝ)) ∧
        (∀ a, CoordinatorCollectionLedger.localArrival
          (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
        (c.enabled = false → c.recordedArm = none ∧
          ∀ a, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let weights := (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
  change record.output.preparation.coordinator =
    .live registers owned base
      (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected) at hbranch
  let selectedPhysical : ReferenceActivePhysicalStep.Selection record.input := {
    view := ⟨registers.payload, dispatched.startResult.pending,
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u,
      weights⟩
    started := dispatched.startResult
    pending_eq := rfl
    cutoff_eq := rfl
    arm := selected.arm
    choice_eq := selected.armChoice_eq }
  have hprepared : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  have hpreparedCoord : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .live registers owned base
        (.cutoffChosen dispatched hstart ledger hinit hcand hdomain hclock hpending hnone selected) := by
    have hc := congrArg (fun prepared : ReferenceActivePhysicalStep.PreparedRound record.input =>
      prepared.coordinator) hprepared.symm
    exact hc.trans hbranch
  have hselection : record.output.preparation.coordinator.selection = some selectedPhysical := by
    rw [hprepared, hpreparedCoord]
    simp [ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt, selectedPhysical, weights]
  have hpayload : selectedPhysical.view.payload = registers.payload := rfl
  have hfollowers := preparedFollowersUnoccupied_of_actual_selection
    rate rewards C_star C_h source k selectedPhysical hselection registers.payload hpayload hcut
  have hfollowersRecord : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record := by
    simpa only [record, R] using hfollowers
  let c := ReferenceLaterCollectionArrivalReadout.laterCutoffCollectionInput
    record registers owned base dispatched selected
  have hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some c := by
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hfollowersRecord,
      hbranch, hlater, c, s]
  have hcallExpected : ∃ (callLedger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (callWeights : CanonicalFastSampling.FastArm registers.payload.slowSet → ℝ),
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall s record =
        some ⟨registers.payload, callLedger, started, callWeights⟩ := by
    refine ⟨ReferenceActivePhysicalStep.sharedLedger ledger, dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights,
      ?_⟩
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, hfollowersRecord,
      hbranch, hlater, s]
    rfl
  obtain ⟨callPayload, callLedger, started, weights', out, hpayloadCall,
      hcall, _hpost, hrun, _henabled, _henabledClock, hrate, hreward,
      hrecording, _hgate, _hrawInput, hraw⟩ :=
    actual_collection_readout_call rate rewards C_star C_h source k registers.payload
      c hreadout hcallExpected
  have hgateNone : c.enabled = false → c.recordedArm = none := by
    intro henabled
    apply cutoff_collection_input_disabled_gate record registers owned base dispatched selected
    exact henabled
  have hzero : c.enabled = false → ∀ a,
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
    intro henabled a
    simp [RecordedQueueRun.quantizedArrival, hgateNone henabled]
  refine ⟨c, ?_, hfollowersRecord, callPayload, callLedger, started, weights', out,
    hpayloadCall, hcall, hrun, hrecording, ?_, hreward, hraw, ?_⟩
  · simpa only [s, record] using hreadout
  · simpa only [hpayloadCall] using hrate
  · intro henabled
    exact ⟨hgateNone henabled, hzero henabled⟩

/-- On an actual continuing collection PREPARE constructor, strict later start
and the true-cutoff/date inequality imply the canonical numerical SOME
readout. The only logical inputs beyond the selected actual constructor are
those two displayed scalar conditions. -/
theorem complete_continuing_collection_calendar_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input payload ledger clock cutoff))
    (boundary : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scores : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input payload ledger clock cutoff) = true)
    (hbranch : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator =
      .collection payload ledger clock cutoff (.continuing core snapshot boundary scores))
    (_hlater : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h <
      payload.sigma.val)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input.row) ≤
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
        record = some c ∧
      ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record ∧
      ∃ (callPayload : ReferenceActivePhysicalStep.Payload rate)
        (callLedger : ReferenceActivePhysicalStep.Ledger rate)
        (started : CoordinatorPhaseClock.StartRoundResult p)
        (weights : CanonicalFastSampling.FastArm callPayload.slowSet → ℝ)
        (out : CoordinatorRecordingOperation.Output p),
        callPayload = payload ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall
          (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
          record = some ⟨callPayload, callLedger, started, weights⟩ ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
            callPayload started weights) = some out ∧
        record.coordinatorDiagnostics.recording = some out ∧
        c.rate = callPayload.rate ∧
        c.reward = (fun a => ((rewards record.input.time a).val : ℝ) / (D p : ℝ)) ∧
        (∀ a, CoordinatorCollectionLedger.localArrival
          (ReferenceCollectionRawBufferHistory.rawDiagnostic record) a =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a) ∧
        (c.enabled = false → c.recordedArm = none ∧
          ∀ a, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  let record := R[k.val]'k.isLt
  let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  change record.output.preparation.coordinator =
    .collection payload ledger clock cutoff (.continuing core snapshot boundary scores) at hbranch
  obtain ⟨selected, hselection, hselectedPayload⟩ :=
    actual_collection_selection_payload record payload ledger clock cutoff core snapshot
      boundary scores hbranch
  have hfollowers := preparedFollowersUnoccupied_of_actual_selection
    rate rewards C_star C_h source k selected hselection payload hselectedPayload hcut
  have hfollowersRecord : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied record := by
    simpa only [record, R] using hfollowers
  let c := ReferenceLaterCollectionArrivalReadout.continuingCollectionInput
    record payload ledger clock cutoff snapshot
  have hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s record = some c := by
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout, hfollowersRecord,
      hbranch, c]
  have hcallExpected : ∃ (callLedger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (callWeights : CanonicalFastSampling.FastArm payload.slowSet → ℝ),
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall s record =
        some ⟨payload, callLedger, started, callWeights⟩ := by
    refine ⟨ledger, snapshot.clockStarted,
      CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
        snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq,
      ?_⟩
    simp [ReferenceLaterCollectionArrivalReadout.laterCollectionCall, hfollowersRecord, hbranch]
  obtain ⟨callPayload, callLedger, started, weights, out, hpayloadCall,
      hcall, _hpost, hrun, _henabled, _henabledClock, hrate, hreward,
      hrecording, _hgate, _hrawInput, hraw⟩ :=
    actual_collection_readout_call rate rewards C_star C_h source k payload
      c hreadout hcallExpected
  have hgateNone : c.enabled = false → c.recordedArm = none := by
    intro henabled
    exact continuing_collection_input_disabled_gate record payload ledger clock cutoff snapshot
      boundary henabled
  have hzero : c.enabled = false → ∀ a,
      RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a = 0 := by
    intro henabled a
    simp [RecordedQueueRun.quantizedArrival, hgateNone henabled]
  refine ⟨c, ?_, hfollowersRecord, callPayload, callLedger, started, weights, out,
    hpayloadCall, hcall, hrun, hrecording, ?_, hreward, hraw, ?_⟩
  · simpa only [s, record] using hreadout
  · simpa only [hpayloadCall] using hrate
  · intro henabled
    exact ⟨hgateNone henabled, hzero henabled⟩

end Bandits.Support.ReferenceCompleteLaterCollectionCalendarReadout

end
