/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay

import Mathlib.Tactic

/-!
# Literal first corrected collection queue source

Source: ZIP4 `appendix_a_local_protocol.tex:28-64`,
`06_interruptions.tex:40-100,192-233,246-299`, and
`04_slow_fast_learner.tex:157-174`.

The root `firstCell_collection_known_queue_source` consumes the accepted
prefix replay producer. It keeps one original source calendar for retained
INPUT/CHOICE/decode/OUTPUT sites and for the first excluded collection choice.
The excluded cell is produced from actual source execution before extending
the numerical word. Guarded candidates survive as observations even when
START output validation, decode, finish, or the clock subsequently fails.
These deterministic identities do not assert a probability cover or manuscript
closure.
-/

@[expose] public section
noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix
open ReferenceFirstCorrectedNativeUpReplayCalendarJoin

namespace Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueSource

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The current-register queue actually stored at a coordinator site. -/
def currentRegisterQueue? (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K) : Option ℕ :=
  (ledger.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue

/-- The cutoff-register queue actually stored at a coordinator site. -/
def cutoffRegisterQueue? (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K) : Option ℕ :=
  (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue

/-- Which actual known-queue register is being observed at a source site. -/
inductive QueueRegisterField where
  | current
  | cutoff
  deriving DecidableEq, Repr

/-- Read a queue only from the selected actual register; missing registers
remain `none`. -/
def knownSiteQueue? (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K) (field : QueueRegisterField) : Option ℕ :=
  match field with
  | .current => currentRegisterQueue? ledger a
  | .cutoff => cutoffRegisterQueue? ledger a

theorem knownSiteQueue?_current (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K) :
    knownSiteQueue? ledger a .current =
      (ledger.currentRegisters a).map CoordinatorCollectionLedger.CurrentRegister.queue := rfl

theorem knownSiteQueue?_cutoff (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K) :
    knownSiteQueue? ledger a .cutoff =
      (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue := rfl

/-- The stage-(1) candidate is present precisely after the literal input and
raw-slot guards used by `CoordinatorCollectionLedger.startRound`. -/
def reachedStageOneCandidate? (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (out : CoordinatorRecordingOperation.Output p) :
    Option (ReferenceActivePhysicalStep.Ledger rate) := by
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out
  let t := time.val + 1
  exact if hinput : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .ready ∧ t = ledger.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true then
    if CoordinatorCollectionLedger.rawSlotFreshCheck ledger time raw = true then
      some (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw)
    else none
  else none

/-! The next export keeps the actual horizon, phase, failed-round, and
excluded-record branches of the accepted extraction visible. In particular,
it does not turn a missing segment or record into a default segment. -/

/-- At every actual source suffix record, a present collection readout exposes
the recorder and stage-(1) result. A candidate is returned only under the
literal input and raw-slot guards; candidate output validity and a later tail
success are not prerequisites. -/
theorem firstCell_all_actual_stageOne_readouts
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (_hz : z ∈ correctedCell rate rewards C_star C_h u t)
    : ∀ (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).length)
      (c : RecordedQueueRun.RoundInput p.K),
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some c) →
      let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h).get k
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some c ∧
      ∃ (payload : Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
        (started : CoordinatorPhaseClock.StartRoundResult p)
        (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
        (out : CoordinatorRecordingOperation.Output p),
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) record =
            some ⟨payload, ledger, started, weights⟩ ∧
        record.coordinatorDiagnostics = ReferenceActivePhysicalStep.collectionPostChoice
          record.output.preparation payload ledger started weights ∧
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
            payload started weights) = some out ∧
        record.coordinatorDiagnostics.recording = some out ∧ out.gateArm = c.recordedArm ∧
        c.enabled = ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time ∧
        c.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
        (let delta := RecordedQueueRun.quantizedArrival
          (K := p.K) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
         let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out
         let candidate := CoordinatorCollectionLedger.startRoundCandidate
           ledger record.input.time c.enabled raw
         (∀ (_guards : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
              ledger.phase = .ready ∧ record.input.time.val + 1 = ledger.cursor ∧
              1 ≤ record.input.time.val + 1 ∧ record.input.time.val + 1 ≤ p.T ∧
              CoordinatorCollectionLedger.rawInputDomainCheck raw = true ∧
              CoordinatorCollectionLedger.rawSlotFreshCheck ledger record.input.time raw = true),
            ∃ reached, reachedStageOneCandidate? ledger record.input.time c.enabled out = some reached ∧
              (∀ a current, ledger.currentRegisters a = some current →
                reached.currentRegisters a = some ⟨(QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (c.enabled, delta c a)).2,
                  (QueueReplay.transition (4 * rate.n) (0, current.queue)
                    (c.enabled, delta c a)).1⟩ ∧
                reached.gammaLoc a = (QueueReplay.transition (4 * rate.n) (0, current.queue)
                  (c.enabled, delta c a)).1 ∧
                currentRegisterQueue? reached a = some
                  (QueueReplay.transition (4 * rate.n) (0, current.queue)
                    (c.enabled, delta c a)).2) ∧
              (∀ a, cutoffRegisterQueue? reached a = cutoffRegisterQueue? ledger a) ∧
              (∀ a, ledger.currentRegisters a = none → reached.gammaLoc a = 0) ∧
              (∀ a slot, reached.rawBuffer a slot =
                if c.recordedArm = some a ∧ ledger.currentRegisters a = none ∧ 0 < delta c a ∧
                    CoordinatorCollectionLedger.sourceRound record.input.time < ledger.freezeAt ∧
                    slot = record.input.time
                then some (delta c a) else ledger.rawBuffer a slot)) ∧
         (ReferenceLaterCollectionArrivalReadout.stageOneAttempt ledger record.input.time c.enabled out = .invalid ∨
           (∃ rejected, ReferenceLaterCollectionArrivalReadout.stageOneAttempt
             ledger record.input.time c.enabled out = .rejected rejected) ∨
           ∃ result, ReferenceLaterCollectionArrivalReadout.stageOneAttempt
             ledger record.input.time c.enabled out = .success result ∧ result = candidate)) := by
  intro k c hreadout
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).get k
  let delta := RecordedQueueRun.quantizedArrival
    (K := p.K) (ReferenceFirstLaunchNumericalCell.queueParameters rate)
  have hreadoutRecord : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) record = some c := by
    simpa only [record, List.get_eq_getElem] using hreadout
  have hreadoutZero : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some c := by
    have hsome : (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) record).isSome = true := by
      rw [hreadoutRecord]
      rfl
    obtain ⟨hunoccupied, hbranch⟩ :=
      (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) record).mp hsome
    cases hcoord : record.output.preparation.coordinator with
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hunoccupied, hcoord] using hreadoutRecord
        | _ => simp only [hcoord] at hbranch
    | live registers owned base outcome =>
        cases outcome with
        | cutoffChosen dispatched hstart ledger initializer candidate domain clock pending none selected =>
            have htime : ReferenceCompletePhysicalHistory.physicalStart
                rate z rewards C_star C_h < registers.payload.sigma.val := by
              simpa only [hcoord] using hbranch
            have hpositive : 0 < registers.payload.sigma.val := by omega
            simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionReadout,
              dite_eq_left hunoccupied, hcoord, htime, hpositive, ite_true] using hreadoutRecord
        | _ => simp only [hcoord] at hbranch
    | first outcome => simp only [hcoord] at hbranch
    | invalidCollectionCutoff => simp only [hcoord] at hbranch
    | dagger => simp only [hcoord] at hbranch
  have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
    cases hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
    | none => rfl
    | some liveCell =>
        exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint
          rate 0 record ⟨by rw [hlive]; rfl, by rw [hreadoutZero]; rfl⟩)
  have hcell0 : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some c := by
    simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveNone,
      Option.none_or, hreadoutZero]
  obtain ⟨payload, ledger, started, weights, out, hcall, htail, hrun, hdiag,
    hgate, henabled, hclock, hknown, hunknown, hbuffer, hresult⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_stageOne
      rate rewards C_star C_h z k c hreadout
  refine ⟨hcell0, payload, ledger, started, weights, out, hcall, htail, hrun, hdiag,
    hgate, henabled, hclock, ?_, ?_⟩
  · intro guards
    rcases guards with ⟨hvalid, hphase, hcursor, hpos, hbound, hdomain, hslot⟩
    let reached := CoordinatorCollectionLedger.startRoundCandidate ledger
      record.input.time c.enabled
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)
    have hreach : reachedStageOneCandidate? ledger record.input.time c.enabled out = some reached := by
      have hinputExact : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
          ledger.phase = .ready ∧ record.input.time.val + 1 = ledger.cursor ∧
          1 ≤ record.input.time.val + 1 ∧ record.input.time.val + 1 ≤ p.T ∧
          CoordinatorCollectionLedger.rawInputDomainCheck
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) = true :=
        ⟨hvalid, hphase, hcursor, hpos, hbound, hdomain⟩
      unfold reachedStageOneCandidate?
      dsimp only
      rw [dite_eq_left hinputExact]
      rw [ite_eq_left hslot]
    refine ⟨reached, hreach, ?_, ?_, ?_, ?_⟩
    · intro a current hcurrent
      have htransition := hknown a current hcurrent
      refine ⟨htransition.1, htransition.2, ?_⟩
      change (reached.currentRegisters a).map
        CoordinatorCollectionLedger.CurrentRegister.queue = some
          (QueueReplay.transition (4 * rate.n) (0, current.queue)
            (c.enabled, delta c a)).2
      rw [htransition.1]
      rfl
    · intro a
      change (reached.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue =
        (ledger.cutoffRegisters a).map CoordinatorCollectionLedger.CutoffRegister.queue
      rfl
    · exact hunknown
    · exact hbuffer
  · exact hresult

/-- A present reached-candidate observer returns exactly the source stage-(1)
guard truth and candidate term. -/
theorem reachedStageOneCandidate_guard_values
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (out : CoordinatorRecordingOperation.Output p)
    (candidate : ReferenceActivePhysicalStep.Ledger rate)
    (h : reachedStageOneCandidate? ledger time enabled out = some candidate) :
    CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .ready ∧ time.val + 1 = ledger.cursor ∧
      1 ≤ time.val + 1 ∧ time.val + 1 ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) = true ∧
      CoordinatorCollectionLedger.rawSlotFreshCheck ledger time
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) = true ∧
      candidate = CoordinatorCollectionLedger.startRoundCandidate ledger time enabled
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) := by
  dsimp only [reachedStageOneCandidate?] at h
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out
  let t := time.val + 1
  change (if hinput : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .ready ∧ t = ledger.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true then
    if hslot : CoordinatorCollectionLedger.rawSlotFreshCheck ledger time raw then
      some (CoordinatorCollectionLedger.startRoundCandidate ledger time enabled raw)
    else none else none) = some candidate at h
  by_cases hinput : CoordinatorCollectionLedger.validLedgerCheck ledger = true ∧
      ledger.phase = .ready ∧ t = ledger.cursor ∧ 1 ≤ t ∧ t ≤ p.T ∧
      CoordinatorCollectionLedger.rawInputDomainCheck raw = true
  · rw [dite_eq_left hinput] at h
    by_cases hslot : CoordinatorCollectionLedger.rawSlotFreshCheck ledger time raw
    · rw [dite_eq_left hslot] at h
      simp only [Option.some.injEq] at h
      subst candidate
      rcases hinput with ⟨hvalid, hphase, htime, hpositive, hbound, hdomain⟩
      exact ⟨hvalid, hphase, htime, hpositive, hbound, hdomain, hslot, rfl⟩
    · rw [dite_eq_right hslot] at h
      contradiction
  · rw [dite_eq_right hinput] at h
    contradiction

/-- A reached candidate uses the actual current register and source local
arrival at the real stage-(1) transition. -/
theorem reachedStageOneCandidate_known_transition
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (out : CoordinatorRecordingOperation.Output p)
    (candidate : ReferenceActivePhysicalStep.Ledger rate)
    (hcandidate : reachedStageOneCandidate? ledger time enabled out = some candidate)
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (hknown : ledger.currentRegisters a = some current) :
    candidate.currentRegisters a = some ⟨
      (QueueReplay.transition (4 * rate.n) (0, current.queue)
        (CoordinatorCollectionLedger.localQueueRecord ledger time enabled
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a)).2,
      (QueueReplay.transition (4 * rate.n) (0, current.queue)
        (CoordinatorCollectionLedger.localQueueRecord ledger time enabled
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a)).1⟩ := by
  dsimp only [reachedStageOneCandidate?] at hcandidate
  split at hcandidate
  · split at hcandidate
    · simp only [Option.some.injEq] at hcandidate
      subst candidate
      exact CoordinatorCollectionLedger.startRoundCandidate_known_transition
        ledger time enabled (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out)
        a current hknown
    · contradiction
  · contradiction

/-- The current queue observer at the reached candidate is the queue field of
the literal stage-(1) transition. -/
theorem reachedStageOneCandidate_current_queue
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (out : CoordinatorRecordingOperation.Output p)
    (candidate : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K) (current : CoordinatorCollectionLedger.CurrentRegister)
    (hreached : reachedStageOneCandidate? ledger time enabled out = some candidate)
    (hknown : ledger.currentRegisters a = some current) :
    currentRegisterQueue? candidate a = some
      (QueueReplay.transition (4 * rate.n) (0, current.queue)
        (CoordinatorCollectionLedger.localQueueRecord ledger time enabled
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a)).2 := by
  obtain ⟨_, _, _, _, _, _, _, hcandidate⟩ :=
    reachedStageOneCandidate_guard_values ledger time enabled out candidate hreached
  rw [hcandidate]
  simp [currentRegisterQueue?, CoordinatorCollectionLedger.startRoundCandidate, hknown]

/-- Stage (1) preserves the actual cutoff-register queue observer. -/
theorem reachedStageOneCandidate_cutoff_queue
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (time : Fin p.T) (enabled : Bool) (out : CoordinatorRecordingOperation.Output p)
    (candidate : ReferenceActivePhysicalStep.Ledger rate)
    (a : Fin p.K)
    (hreached : reachedStageOneCandidate? ledger time enabled out = some candidate) :
    cutoffRegisterQueue? candidate a = cutoffRegisterQueue? ledger a := by
  obtain ⟨_, _, _, _, _, _, _, hcandidate⟩ :=
    reachedStageOneCandidate_guard_values ledger time enabled out candidate hreached
  rw [hcandidate]
  simp [cutoffRegisterQueue?, CoordinatorCollectionLedger.startRoundCandidate]

private theorem actual_segment_run
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (e : ℕ) (seg : Segment rate)
    (hseg : segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h) e = some seg) :
    let s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
    ∃ (initial : ReferenceActivePhysicalStep.State p rate)
      (span : s + (p.T - s) ≤ p.T) (active : allActiveAtStart initial s),
      initial.coordinator = .first ∧
      ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h =
        (run initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
          rewards s (p.T - s) span active).records := by
  intro s
  have hlaunchNe : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h ≠ none := by
    intro hnone
    have hnil : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h = [] := by
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone,
        dite_true]
    rw [hnil] at hseg
    simp only [segmentAt, List.drop_nil, ReferenceCollectionSegmentExtraction.segment] at hseg
    contradiction
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h).isSome = true := by
    cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h with
    | none => exact False.elim (hlaunchNe hl)
    | some initial => rfl
  have hc := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
    rate z rewards C_star C_h).mp hsome
  obtain ⟨initial, hlaunch, hfirst, _⟩ :=
    ReferenceCorrectedInitializationLaunch.correctedLaunch_coordinator_provenance
      rate z rewards C_star C_h hc
  have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h
  exact ⟨initial, by dsimp only [s]; omega,
    ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h initial hlaunch, hfirst,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h initial hlaunch⟩

/-- A retained record's final ledger is the endpoint after that record. -/
theorem retained_final_endpoint
    (initial : ReferenceActivePhysicalStep.Ledger rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (v : ℕ) (hv : v < records.length) (done : CompletedRound rate)
    (hdone : extractRound records[v] = some done) :
    endpointLedger initial (records.take (v + 1)) = done.final := by
  rw [List.take_add_one, List.getElem?_eq_getElem hv]
  rw [Option.toList_some, endpointLedger_append]
  simp only [endpointLedger, completed, List.filterMap_cons, hdone,
    List.filterMap_nil, List.foldl_cons, List.foldl_nil]

/-- A collection INPUT really has the CHOICE pre-ledger; a LIVE cutoff input
is deliberately outside this query. -/
theorem collection_input_ledger
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (call : Choice rate)
    (hcall : choice record.input = some call)
    (payload : Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool))
    (hinput : record.input.state.coordinator = .collection payload ledger proposal) :
    ledger = call.preLedger :=
  (choice_collection_pre record.input payload ledger proposal call hinput hcall).1.symm

/-- The actual filtered reception's decoded ledger has the same queues as
its completed OUTPUT. Finishing changes accumulators, phase and cursor only. -/
theorem completed_decode_registers
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (done : CompletedRound rate)
    (hdone : extractRound record = some done) :
    ∃ (out : CoordinatorRecordingOperation.Output p)
      (started decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p),
      record.output.coordinator.recording = some out ∧
      CoordinatorRecorderComplementBridge.run
        (collectionRecordingInput (prepare record.input) done.context.payload
          done.context.started done.context.weights) = some out ∧
      CoordinatorCollectionLedger.startRound done.context.preLedger
        (record.input.time.val + 1) (collectionEnabled done.context.preLedger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) = .success started ∧
      (receiveUp (prepare record.input) started).result =
        (if done.accepted then .success (decoded, bank) else .rejected (decoded, bank)) ∧
      CoordinatorCollectionLedger.finishRound decoded = .success done.final ∧
      decoded.currentRegisters = done.final.currentRegisters ∧
      decoded.cutoffRegisters = done.final.cutoffRegisters := by
  obtain ⟨out, started, decoded, bank, ho, hr, hs, hi, hd, _⟩ :=
    actual_collection_round_inputs record done hdone
  have hsingle := (actual_collection_round_checked record done hdone).2.2.1
  have hdecode := receiveUp_decode_result record.input started
  cases ha : done.accepted <;> simp only [ha, Bool.false_eq_true,
    ite_false, ite_true] at hd
  all_goals
    rw [hd] at hdecode
    rw [hi] at hsingle
    cases hf : CoordinatorCollectionLedger.finishRound decoded with
    | invalid =>
        simp only [CollectionCheckedExecution.checkedRounds, inputOf,
          CoordinatorCollectionLedger.sourceRound, hs, hdecode, hf] at hsingle
        contradiction
    | rejected bad =>
        simp only [CollectionCheckedExecution.checkedRounds, inputOf,
          CoordinatorCollectionLedger.sourceRound, hs, hdecode, hf] at hsingle
        contradiction
    | success finished =>
        have he : finished = done.final := by
          have hpair := hsingle
          simp only [CollectionCheckedExecution.checkedRounds, inputOf,
            CoordinatorCollectionLedger.sourceRound, hs, hdecode, hf] at hpair
          exact congrArg Prod.snd (Option.some.inj hpair)
        subst finished
        have hc := CollectionCheckedExecution.finishRound_success_candidate decoded done.final hf
        refine ⟨out, started, decoded, bank, ho, hr, hs, ?_, hf, ?_, ?_⟩
        · simpa only [ha, Bool.false_eq_true, ite_false, ite_true] using hd
        · rw [hc]; rfl
        · rw [hc]; rfl

private theorem completed_payload
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) (done : CompletedRound rate)
    (h : extractRound record = some done) :
    ∃ saved, record.output.next.coordinator = .collection done.context.payload done.final saved := by
  obtain ⟨hc, _, _, P, saved, hn⟩ := actual_collection_round_checked record done h
  have ht : record.output.coordinator = collectionPostChoice (prepare record.input)
      done.context.payload done.context.preLedger done.context.started done.context.weights := by
    rw [record.output_eq]
    exact choice_tail record.input done.context hc
  have hf := ReferenceAssignmentPayloadPersistence.collectionPostChoice_payload_frame
    (prepare record.input) done.context.payload done.context.preLedger
      done.context.started done.context.weights
  have hs : record.output.coordinator.configuration = .collection P done.final saved := by
    rw [record.output_eq] at hn ⊢
    exact hn
  rw [← ht, hs] at hf
  simp only [ReferenceAssignmentPayloadPersistence.storedPayload_collection,
    reduceCtorEq, false_or] at hf
  have hp := Option.some.inj hf
  exact ⟨saved, hp ▸ hn⟩

/-- All actual retained INPUT/CHOICE, decoded and OUTPUT queue queries use
one original numerical calendar. Queries are inside the conclusion: the only
root condition is the original corrected cell, followed by actual segment
selection. Successful decode is not used to infer stage-(1) reachability. -/
theorem firstCell_collection_known_queue_source_sites
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    let R := sourceRecords rate rewards C_star C_h z
    let s := sourceStart rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∀ (seg : Segment rate), segmentAt R e = some seg →
      ∃ (A D : List (RecordedQueueRun.RoundInput p.K)),
        A.length = e ∧ D.length = seg.records.length ∧
        prefixInputs rate rewards C_star C_h (s + e) z = some A ∧
        (∀ j : Fin seg.records.length, ∃ hD : j.val < D.length,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[j.val] = some (D[j.val]'hD)) ∧
        (∀ a v, (seg.records.take v).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
          (D.take v).map (fun d => (d.enabled, RecordedQueueRun.quantizedArrival Q d a))) ∧
        (∀ v, v ≤ D.length →
          let Gv := A ++ D.take v
          let lv := endpointLedger seg.context.preLedger (seg.records.take v)
          prefixInputs rate rewards C_star C_h (s + e + v) z = some Gv ∧
          (∀ a current, lv.currentRegisters a = some current →
            current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gv Gv.length a).2) ∧
          (∀ a cutoff, lv.cutoffRegisters a = some cutoff →
            cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) ∧
        (∀ (v : ℕ) (hv : v < seg.records.length),
          let record := seg.records[v]
          let Gv := A ++ D.take v
          let Gnext := A ++ D.take (v + 1)
          ∃ (done : CompletedRound rate), extractRound record = some done ∧
            choice record.input = some done.context ∧
            done.context.preLedger = endpointLedger seg.context.preLedger (seg.records.take v) ∧
            done.final = endpointLedger seg.context.preLedger (seg.records.take (v + 1)) ∧
            (∀ a current, done.context.preLedger.currentRegisters a = some current →
              current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gv Gv.length a).2) ∧
            (∀ a cutoff, done.context.preLedger.cutoffRegisters a = some cutoff →
              cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) ∧
            (∀ payload ledger proposal,
              record.input.state.coordinator = .collection payload ledger proposal →
              ledger = done.context.preLedger) ∧
            (∀ a current, done.final.currentRegisters a = some current →
              current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gnext Gnext.length a).2) ∧
            (∀ a cutoff, done.final.cutoffRegisters a = some cutoff →
              cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) ∧
            (∃ proposal, record.output.next.coordinator = .collection done.context.payload done.final proposal) ∧
            ∃ (out : CoordinatorRecordingOperation.Output p)
              (started decoded : ReferenceActivePhysicalStep.Ledger rate)
              (bank : CoordinatorUpReception.UpDecoderBank p),
              record.output.coordinator.recording = some out ∧
              CoordinatorRecorderComplementBridge.run
                (collectionRecordingInput (prepare record.input) done.context.payload
                  done.context.started done.context.weights) = some out ∧
              CoordinatorCollectionLedger.startRound done.context.preLedger (record.input.time.val + 1)
                (collectionEnabled done.context.preLedger record.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) = .success started ∧
              (receiveUp (prepare record.input) started).result =
                (if done.accepted then .success (decoded, bank) else .rejected (decoded, bank)) ∧
              CoordinatorCollectionLedger.finishRound decoded = .success done.final ∧
              (∀ a current, decoded.currentRegisters a = some current →
                current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gnext Gnext.length a).2) ∧
              (∀ a cutoff, decoded.cutoffRegisters a = some cutoff →
                cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) := by
  intro R s e Q seg hseg
  obtain ⟨A, D, hA, hD, hprefix, hcells, hwords, hvalues⟩ :=
    ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay.firstCell_collection_known_queue_every_prefix_replay
      rate rewards C_star C_h u t z hz seg hseg
  refine ⟨A, D, hA, hD, hprefix, hcells, hwords, hvalues, ?_⟩
  intro v hv
  dsimp only
  have hgood := segment_all_completed _ seg (segmentAt_branch R e seg hseg).1
  obtain ⟨done, hdone⟩ : ∃ done, extractRound seg.records[v] = some done := by
    cases hh : extractRound seg.records[v] with
    | none => have hg := hgood _ (List.getElem_mem hv); simp only [hh] at hg; contradiction
    | some done => exact ⟨done, rfl⟩
  obtain ⟨initial, span, active, _hfirst, hrun⟩ :=
    actual_segment_run rate rewards C_star C_h z e seg hseg
  have hsegRun := hseg
  change segmentAt (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) e = _ at hsegRun
  rw [hrun] at hsegRun
  have hbefore := ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    rewards _ _ span active e seg hsegRun v hv done hdone
  have hafter := (retained_final_endpoint seg.context.preLedger seg.records v hv done hdone).symm
  have hpre := hvalues v (by omega)
  have hpost := hvalues (v + 1) (by omega)
  have hactual := actual_collection_round_checked seg.records[v] done hdone
  refine ⟨done, hdone, hactual.1, hbefore, hafter, ?_, ?_, ?_, ?_, ?_, completed_payload seg.records[v] done hdone, ?_⟩
  · simpa only [hbefore] using hpre.2.1
  · simpa only [hbefore] using hpre.2.2
  · intro payload ledger proposal hi
    exact collection_input_ledger _ _ hactual.1 payload ledger proposal hi
  · simpa only [hafter] using hpost.2.1
  · simpa only [hafter] using hpost.2.2
  · obtain ⟨out, started, decoded, bank, ho, hr, hs, hd, hf, hc, hk⟩ :=
      completed_decode_registers seg.records[v] done hdone
    refine ⟨out, started, decoded, bank, ho, hr, hs, hd, hf, ?_, ?_⟩
    · rw [hc, hafter]; exact hpost.2.1
    · rw [hk, hafter]; exact hpost.2.2

open ReferenceLaterCollectionArrivalReadout

private theorem choice_selection (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (ctx : Choice rate) (hchoice : choice r.input = some ctx) :
    ∃ v : Selection r.input,
      r.output.preparation.coordinator.selection = some v ∧ v.view.payload = ctx.payload := by
  classical
  unfold choice at hchoice
  split at hchoice
  next => contradiction
  next hn =>
    have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
      rw [r.output_eq]; rfl
    rw [hprep] at hchoice hn
    cases hc : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hchoice
    | invalidCollectionCutoff => simp [hc, choiceOfCut] at hchoice
    | dagger => simp [hc, choiceOfCut] at hchoice
    | collection payload ledger clock cutoff outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next core snapshot hboundary hchecked =>
        rw [← Option.some.inj hchoice]
        exact ⟨_, rfl, rfl⟩
    | live registers owned base outcome =>
      cases outcome <;> simp only [hc, choiceOfCut] at hchoice
      all_goals try contradiction
      next dispatched hs ledger hi he hd hclock hp hn selected =>
        rw [← Option.some.inj hchoice]
        simp only [DispatchCut.selection, selectionAt, dite_true]
        exact ⟨_, rfl, rfl⟩

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

/-- Actual collection CHOICE after its true cutoff supplies the canonical
cell before START, decoding, finishing, or clock success is tested. -/
private theorem actual_choice_readout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (call : Choice rate)
    (hchoice : choice (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input = some call)
    (hlater : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < call.payload.sigma.val)
    (hcut : FollowerCutoffScan.firstCutoff p rate.eta.val call.payload.sigma
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.row) ≤
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val].input.time.val + 1) :
    ∃ d, laterCollectionReadout
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some d ∧
      laterCollectionReadout 0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some d ∧
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] = some d ∧
      laterCollectionCall 0
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val] =
        some ⟨call.payload, call.preLedger, call.started, call.weights⟩ := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]
  obtain ⟨selected, hselected, hpay⟩ := choice_selection record call hchoice
  have ho := preparedFollowersUnoccupied_of_actual_selection rate rewards C_star C_h z k
    selected hselected call.payload hpay hcut
  change preparedFollowersUnoccupied record at ho
  have hp : (prepare record.input).coordinator = record.output.preparation.coordinator := by
    rw [record.output_eq]; rfl
  have hch := hchoice
  unfold choice at hch
  split at hch
  · contradiction
  next hn =>
    rw [hp] at hch
    have hdom : (match record.output.preparation.coordinator with
      | .collection _ _ _ _ (.continuing ..) => True
      | .live r _ _ (.cutoffChosen ..) =>
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < r.payload.sigma.val
      | _ => False) := by
      cases hc : record.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hch
      | invalidCollectionCutoff => simp [hc, choiceOfCut] at hch
      | dagger => simp [hc, choiceOfCut] at hch
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals first | contradiction | trivial
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals first | contradiction | (have heq := congrArg Choice.payload (Option.some.inj hch); change registers.payload = call.payload at heq; simpa only [← heq] using hlater)
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp
      ((laterCollectionReadout_domain _ record).mpr ⟨ho, hdom⟩)
    have hzero : laterCollectionReadout 0 record = some d := by
      cases hc : record.output.preparation.coordinator with
      | first outcome => simp only [hc] at hdom
      | invalidCollectionCutoff => simp only [hc] at hdom
      | dagger => simp only [hc] at hdom
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc] at hdom
          simpa only [laterCollectionReadout, dite_eq_left ho, hc] using hd
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc] at hdom
          have hpos : 0 < registers.payload.sigma.val := by omega
          simpa only [laterCollectionReadout, dite_eq_left ho, hc, dite_eq_left hdom,
            dite_eq_left hpos] using hd
    have hlive : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none := by
      cases hh : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record with
      | none => rfl
      | some c => exact False.elim (ReferenceCompleteNumericalBranchObservation.readouts_disjoint rate 0 record
          ⟨by rw [hh]; rfl, by rw [hzero]; rfl⟩)
    refine ⟨d, hd, hzero, ?_, ?_⟩
    · change ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some d
      simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hlive, Option.none_or, hzero]
    · unfold laterCollectionCall
      rw [ite_eq_left ho]
      cases hc : record.output.preparation.coordinator with
      | first outcome => cases outcome <;> simp [hc, choiceOfCut] at hch
      | invalidCollectionCutoff => simp [hc, choiceOfCut] at hch
      | dagger => simp [hc, choiceOfCut] at hch
      | collection payload ledger clock cutoff outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals first | contradiction | (rw [← Option.some.inj hch])
      | live registers owned base outcome =>
          cases outcome <;> simp only [hc, choiceOfCut] at hch
          all_goals try contradiction
          simp only [hc] at hdom
          have hpos : 0 < registers.payload.sigma.val := by omega
          rw [← Option.some.inj hch]
          simp only [ite_eq_left hpos]

private theorem liveTail_eq_continuingPrefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail
        rate rewards C_star C_h z =
      ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix
        rate rewards C_star C_h z
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.birthIndex
            rate rewards C_star C_h z + 1) := by
  simp only [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.liveTail,
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords,
    ReferenceFirstReplacementLiveFollowerPrefix.continuingTail,
    ReferenceCompleteLaterLiveComplementPrefixReplay.continuingPrefix]
  congr 1
  funext r
  unfold ReferenceCompleteLaterLiveComplementPrefixReplay.continuingTest
    ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
  cases r.output.preparation.coordinator with
  | live registers owned base outcome => cases outcome <;> rfl
  | first outcome => rfl
  | collection payload ledger clock cutoff outcome => rfl
  | invalidCollectionCutoff => rfl
  | dagger => rfl

/-- Source geometry of the original first collection, including its actual
nonempty first checked round. -/
private theorem firstCell_segment_geometry
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t)
    (seg : Segment rate)
    (hseg : segmentAt (sourceRecords rate rewards C_star C_h z)
      (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) = some seg) :
    seg.records ≠ [] ∧ ReferenceCollectionPhaseHistory.cutoffChosen seg.entry.input = true ∧
      seg.context.payload.sigma = t ∧
      sourceStart rate rewards C_star C_h z < seg.context.payload.sigma.val ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val seg.context.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z))) =
        sourceStart rate rewards C_star C_h z +
          (birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length) + 1 := by
  let R := sourceRecords rate rewards C_star C_h z
  let s := sourceStart rate rewards C_star C_h z
  let b := birthIndex rate rewards C_star C_h z
  let e := b + 1 + (liveTail rate rewards C_star C_h z).length
  have he : e < R.length := by
    by_contra hn
    have hn' : R.drop e = [] := List.drop_eq_nil_iff.mpr (by omega)
    have hb := (segmentAt_branch R e seg hseg).1
    rw [hn'] at hb
    contradiction
  obtain ⟨L, B, c, birth, payload, segW, D, _hL, _hprefix, hLb, hdate, _hb,
    _hborn, hsigma, hlater, hsegW, _hentry, hpay, hcut, htrue, _rest⟩ :=
    ReferenceFirstCorrectedCollectionKnownQueuePrefixReplay.firstCell_actual_segment_prefix_words
      rate rewards C_star C_h u t z hz he
  have heq : segW = seg := Option.some.inj (hsegW.symm.trans hseg)
  subst segW
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  change R.length = p.T - s at hlen
  have htT : t.val + 1 < p.T := by
    change s + b = t.val at hdate
    dsimp only [e] at he
    omega
  obtain ⟨_birth, rout, qout, beta, _hb, _hdate, _ht, _hrows, _hJ, _hrewards,
    _hborn, _hsigma, _hlater, _hlive, hcont⟩ :=
    ReferenceFirstCorrectedReplacementCollectionReadout.firstCell_collection_readout_cover
      rate rewards C_star C_h u t z hz
  obtain ⟨_heR, _heT, _rE, _qE, _hpayE, _hstateE, hboundary⟩ := hcont htT
  have hW := liveTail_eq_continuingPrefix rate rewards C_star C_h z
  simp only [← hW] at hboundary
  rcases hboundary with hterminal | ⟨_he, segC, _I, _l0, hsegC, _hentryC,
    _hpayC, _hpre, _hIC, _hIdef, _hstart, _harm, _hIsigma, _hIcut,
    _hIscan, _hfreeze, _hbase, _hcutC, hnonempty, _restC⟩
  · change e = R.length at hterminal
    omega
  have hsegEq : segC = seg := Option.some.inj (hsegC.symm.trans hseg)
  subst segC
  refine ⟨?_, hcut, ?_, ?_, ?_⟩
  · obtain ⟨during, hd⟩ := hnonempty
    rw [hd]
    exact List.cons_ne_nil _ _
  · rw [hpay]; exact hsigma
  · rw [hpay]; exact hlater
  · rw [hpay]; exact htrue

/-- The head excluded by the actual partition has its original index. -/
theorem first_excluded_original_index
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : Segment rate) (hseg : segmentAt R e = some seg)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : seg.remaining.head? = some record) :
    R[e + seg.records.length]? = some record := by
  have hp := segmentAt_partition R e seg hseg
  have hd := congrArg (List.drop seg.records.length) hp
  have hdrop : R.drop (e + seg.records.length) = seg.remaining := by
    simpa only [List.drop_left', List.drop_drop, Nat.add_comm] using hd.symm
  have hh := congrArg List.head? hdrop
  simpa only [List.head?_drop, hr] using hh

/-- Appending one actual cell performs one unstopped queue update; enabled
zero arrivals serve, and disabled dates preserve. -/
private theorem unstopped_append_one_queue
    (Q : RecordedQueueRun.Parameters) (G : List (RecordedQueueRun.RoundInput p.K))
    (d : RecordedQueueRun.RoundInput p.K) (a : Fin p.K) :
    (UnstoppedRecordedQueueComparison.unstoppedReplay Q (G ++ [d]) (G ++ [d]).length a).2 =
      (QueueReplay.transition (4 * Q.n)
        (0, (UnstoppedRecordedQueueComparison.unstoppedReplay Q G G.length a).2)
        (d.enabled, RecordedQueueRun.quantizedArrival Q d a)).2 := by
  simp only [UnstoppedRecordedQueueComparison.unstoppedReplay, List.take_length,
    List.map_append, List.map_cons, List.map_nil, QueueReplay.replay_append]
  simp only [QueueReplay.replay, List.foldl_cons, List.foldl_nil]
  cases he : d.enabled <;>
    simp only [UnstoppedRecordedQueueComparison.unstoppedRecord, he, Bool.false_eq_true,
      ite_false, ite_true, QueueReplay.transition]

/-- A literal reached candidate on a source readout uses the one appended
calendar cell, even if a later operation discards that candidate. -/
private theorem actual_candidate_calendar
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : Choice rate) (d : RecordedQueueRun.RoundInput p.K)
    (hread : laterCollectionReadout 0 record = some d)
    (hcall : laterCollectionCall 0 record = some ⟨call.payload, call.preLedger, call.started, call.weights⟩)
    (G : List (RecordedQueueRun.RoundInput p.K))
    (hqueues : ∀ a current, call.preLedger.currentRegisters a = some current →
      current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) G G.length a).2)
    (out : CoordinatorRecordingOperation.Output p)
    (hout : record.coordinatorDiagnostics.recording = some out)
    (candidate : ReferenceActivePhysicalStep.Ledger rate)
    (hreached : reachedStageOneCandidate? call.preLedger record.input.time
      (collectionEnabled call.preLedger record.input.time) out = some candidate) :
    (∀ a current, candidate.currentRegisters a = some current →
      current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) (G ++ [d]) (G ++ [d]).length a).2) ∧
    candidate.cutoffRegisters = call.preLedger.cutoffRegisters := by
  obtain ⟨payload, ledger, clock, weights, out', hcall', _htail, _hrun,
    henabled, _hclock, _hrate, _hreward, hout', _hgate, harr⟩ :=
    laterCollectionReadout_call 0 record d hread
  have hargs := Option.some.inj (hcall'.symm.trans hcall)
  cases hargs
  have heq : out' = out := Option.some.inj (hout'.symm.trans hout)
  subst out'
  obtain ⟨_hv, _hp, _hc, _hpos, _hbound, _hdomain, _hslot, hcandidate⟩ :=
    reachedStageOneCandidate_guard_values _ _ _ _ _ hreached
  rw [hcandidate]
  refine ⟨?_, rfl⟩
  intro a current hcurrent
  cases hknown : call.preLedger.currentRegisters a with
  | none => simp only [CoordinatorCollectionLedger.startRoundCandidate, hknown,
      reduceCtorEq] at hcurrent
  | some before =>
    have ht := CoordinatorCollectionLedger.startRoundCandidate_known_transition
      call.preLedger record.input.time (collectionEnabled call.preLedger record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a before hknown
    have hcurrentEq := Option.some.inj (hcurrent.symm.trans ht)
    have hqueue := congrArg CoordinatorCollectionLedger.CurrentRegister.queue hcurrentEq
    dsimp only at hqueue
    rw [unstopped_append_one_queue, hqueue, hqueues a before hknown]
    change (QueueReplay.transition (4 * rate.n) _ _).2 = (QueueReplay.transition (4 * rate.n) _ _).2
    cases he : d.enabled with
    | false => simp only [← henabled, he, CoordinatorCollectionLedger.localQueueRecord,
        Bool.false_and, QueueReplay.transition, Bool.false_eq_true, ite_false]
    | true =>
        have hbefore := (of_decide_eq_true (henabled.symm.trans he)).2.2
        simp only [CoordinatorCollectionLedger.localQueueRecord,
          CoordinatorCollectionLedger.sourceRound, hbefore, decide_true, Bool.and_true,
          ← henabled, he, ite_true, harr a]

private theorem source_record_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (k : ℕ)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : (sourceRecords rate rewards C_star C_h z)[k]? = some record) :
    record.input.time.val = sourceStart rate rewards C_star C_h z + k := by
  obtain ⟨hk, hkr⟩ := List.getElem?_eq_some_iff.mp hr
  have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values rate z rewards C_star C_h
  change (sourceRecords rate rewards C_star C_h z).map (fun r => r.input.time.val) =
    List.range' (sourceStart rate rewards C_star C_h z)
      (p.T - sourceStart rate rewards C_star C_h z) at ht
  have hlen := ReferenceCompletePhysicalHistory.completeSuffixRecords_length rate z rewards C_star C_h
  have hk' : k < p.T - sourceStart rate rewards C_star C_h z := by
    change (sourceRecords rate rewards C_star C_h z).length = p.T - sourceStart rate rewards C_star C_h z at hlen
    omega
  have hh := congrArg (fun xs => xs[k]?) ht
  rw [List.getElem?_map, hr, Option.map_some,
    List.getElem?_eq_getElem (by simpa only [List.length_range'] using hk')] at hh
  exact (Option.some.inj hh).trans (List.getElem_range'_1 k _)

private theorem retained_original_index
    (R : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (e : ℕ) (seg : Segment rate) (hseg : segmentAt R e = some seg)
    (v : ℕ) (hv : v < seg.records.length) :
    R[e + v]? = some seg.records[v] := by
  have hp := congrArg (fun xs => xs[v]?) (segmentAt_partition R e seg hseg)
  rw [List.getElem?_append_left hv, List.getElem?_eq_getElem hv,
    List.getElem?_drop] at hp
  exact hp.symm

private theorem collection_choice_payload
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : Payload rate) (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (proposal : Option (Fin p.T × Bool)) (call : Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hchoice : choice x = some call) : call.payload = payload := by
  unfold choice at hchoice
  split at hchoice
  · contradiction
  next =>
    change choiceOfCut (dispatch x) = some call at hchoice
    simp only [dispatch, hstate] at hchoice
    split at hchoice
    next hcut =>
      let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := collectionClock payload ledger proposal cutoff
      change choiceOfCut (.collection payload ledger clock cutoff
        (CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff))) = some call at hchoice
      cases ho : CoordinatorRoundDispatch.dispatchCollection (collectionInput x payload ledger clock cutoff) <;>
        simp only [choiceOfCut, ho] at hchoice
      all_goals first | contradiction | (exact (congrArg Choice.payload (Option.some.inj hchoice)).symm)
    · simp only [choiceOfCut, reduceCtorEq] at hchoice

/-- One original calendar supplies all actual known collection register sites
and every reached stage-(1) candidate, including the first excluded record.
The excluded record supplies its own cell before the prefix is extended;
no decode, finish, clock success or future installation is assumed. -/
theorem firstCell_collection_known_queue_source
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (hz : z ∈ correctedCell rate rewards C_star C_h u t) :
    let R := sourceRecords rate rewards C_star C_h z
    let s := sourceStart rate rewards C_star C_h z
    let e := birthIndex rate rewards C_star C_h z + 1 + (liveTail rate rewards C_star C_h z).length
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∀ (seg : Segment rate), segmentAt R e = some seg →
      ∃ (A D : List (RecordedQueueRun.RoundInput p.K)),
        A.length = e ∧ D.length = seg.records.length ∧
        prefixInputs rate rewards C_star C_h (s + e) z = some A ∧
        (∀ j : Fin seg.records.length, ∃ hD : j.val < D.length,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate seg.records[j.val] = some (D[j.val]'hD)) ∧
        (∀ a v, (seg.records.take v).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger a) =
          (D.take v).map (fun d => (d.enabled, RecordedQueueRun.quantizedArrival Q d a))) ∧
        (∀ v, v ≤ D.length →
          let Gv := A ++ D.take v
          let lv := endpointLedger seg.context.preLedger (seg.records.take v)
          prefixInputs rate rewards C_star C_h (s + e + v) z = some Gv ∧
          (∀ a current, lv.currentRegisters a = some current →
            current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gv Gv.length a).2) ∧
          (∀ a cutoff, lv.cutoffRegisters a = some cutoff →
            cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) ∧
        (∀ (v : ℕ) (hv : v < seg.records.length),
          let record := seg.records[v]
          let Gv := A ++ D.take v
          let Gnext := A ++ D.take (v + 1)
          ∃ (done : CompletedRound rate), extractRound record = some done ∧
            choice record.input = some done.context ∧
            done.context.preLedger = endpointLedger seg.context.preLedger (seg.records.take v) ∧
            done.final = endpointLedger seg.context.preLedger (seg.records.take (v + 1)) ∧
            (∀ a current, done.context.preLedger.currentRegisters a = some current →
              current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gv Gv.length a).2) ∧
            (∀ a cutoff, done.context.preLedger.cutoffRegisters a = some cutoff →
              cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) ∧
            (∀ payload ledger proposal,
              record.input.state.coordinator = .collection payload ledger proposal →
              ledger = done.context.preLedger) ∧
            (∀ a current, done.final.currentRegisters a = some current →
              current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gnext Gnext.length a).2) ∧
            (∀ a cutoff, done.final.cutoffRegisters a = some cutoff →
              cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) ∧
            (∃ proposal, record.output.next.coordinator = .collection done.context.payload done.final proposal) ∧
            ∃ (out : CoordinatorRecordingOperation.Output p)
              (started decoded : ReferenceActivePhysicalStep.Ledger rate)
              (bank : CoordinatorUpReception.UpDecoderBank p),
              record.output.coordinator.recording = some out ∧
              CoordinatorRecorderComplementBridge.run
                (collectionRecordingInput (prepare record.input) done.context.payload
                  done.context.started done.context.weights) = some out ∧
              CoordinatorCollectionLedger.startRound done.context.preLedger (record.input.time.val + 1)
                (collectionEnabled done.context.preLedger record.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) = .success started ∧
              (receiveUp (prepare record.input) started).result =
                (if done.accepted then .success (decoded, bank) else .rejected (decoded, bank)) ∧
              CoordinatorCollectionLedger.finishRound decoded = .success done.final ∧
              (∀ a current, decoded.currentRegisters a = some current →
                current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q Gnext Gnext.length a).2) ∧
              (∀ a cutoff, decoded.cutoffRegisters a = some cutoff →
                cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) ∧
        (∀ (v : ℕ) (hv : v < seg.records.length),
          let record := seg.records[v]
          ∃ (d : RecordedQueueRun.RoundInput p.K) (call : Choice rate),
            D[v]? = some d ∧ choice record.input = some call ∧
            call.payload = seg.context.payload ∧
            call.preLedger = endpointLedger seg.context.preLedger (seg.records.take v) ∧
            laterCollectionReadout s record = some d ∧
            laterCollectionReadout 0 record = some d ∧
            laterCollectionCall 0 record = some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
            ∀ (out : CoordinatorRecordingOperation.Output p)
              (candidate : ReferenceActivePhysicalStep.Ledger rate),
              record.coordinatorDiagnostics.recording = some out →
              reachedStageOneCandidate? call.preLedger record.input.time
                (collectionEnabled call.preLedger record.input.time) out = some candidate →
              (∀ a current, candidate.currentRegisters a = some current →
                current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                  (A ++ D.take (v + 1)) (A ++ D.take (v + 1)).length a).2) ∧
              (∀ a cutoff, candidate.cutoffRegisters a = some cutoff →
                cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) ∧
        (∀ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
          seg.remaining.head? = some record →
          R[e + D.length]? = some record ∧
          ∃ saved, record.input.state.coordinator = .collection seg.context.payload seg.final saved ∧
            (∀ a current, seg.final.currentRegisters a = some current →
              current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                (A ++ D) (A ++ D).length a).2) ∧
            (∀ a cutoff, seg.final.cutoffRegisters a = some cutoff →
              cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) ∧
            ∀ call, choice record.input = some call →
              call.payload = seg.context.payload ∧ call.preLedger = seg.final ∧ call.initializer = none ∧
              ∃ d : RecordedQueueRun.RoundInput p.K,
                laterCollectionReadout s record = some d ∧
                laterCollectionReadout 0 record = some d ∧
                ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record = some d ∧
                laterCollectionCall 0 record = some ⟨call.payload, call.preLedger, call.started, call.weights⟩ ∧
                prefixInputs rate rewards C_star C_h (s + e + D.length + 1) z = some (A ++ D ++ [d]) ∧
                ∀ (out : CoordinatorRecordingOperation.Output p)
                  (candidate : ReferenceActivePhysicalStep.Ledger rate),
                  record.coordinatorDiagnostics.recording = some out →
                  reachedStageOneCandidate? call.preLedger record.input.time
                    (collectionEnabled call.preLedger record.input.time) out = some candidate →
                  (∀ a current, candidate.currentRegisters a = some current →
                    current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q
                      (A ++ D ++ [d]) (A ++ D ++ [d]).length a).2) ∧
                  (∀ a cutoff, candidate.cutoffRegisters a = some cutoff →
                    cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2)) := by
  intro R s e Q seg hseg
  obtain ⟨A, D, hA, hD, hprefix, hcells, hwords, hvalues, hsites⟩ :=
    firstCell_collection_known_queue_source_sites rate rewards C_star C_h u t z hz seg hseg
  obtain ⟨hne, hcut, _hsigma, hlater, htrue⟩ :=
    firstCell_segment_geometry rate rewards C_star C_h u t z hz seg hseg
  obtain ⟨_hle, hfields, hpayload, saved, _hend, _hcursor, _during, _hshape,
    _hprefixR, _hnotlater, _hduring, _hpending, _hnodup, _haccepted, hboundary⟩ :=
    ReferenceFirstCorrectedReplacementCollectionBoundaryHistory.firstCell_collection_boundary_history
      rate rewards C_star C_h u t z hz e seg hseg hne hcut
  refine ⟨A, D, hA, hD, hprefix, hcells, hwords, hvalues, hsites, ?_, ?_⟩
  · intro v hv
    dsimp only
    let record := seg.records[v]
    have hindex := retained_original_index R e seg hseg v hv
    obtain ⟨hk, hkr⟩ := List.getElem?_eq_some_iff.mp hindex
    change R[e + v] = record at hkr
    have hkrActual : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + v] = record := hkr
    have htime := source_record_time rate rewards C_star C_h z (e + v) record hindex
    have hrR : record ∈ R := by rw [← hkr]; exact List.getElem_mem hk
    have hrow : record.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
      change record.input.rows record.input.selected = _
      rw [(hfields record hrR).1, (hfields record hrR).2.1]
    obtain ⟨done, hdone, hchoice, hbefore, _hafter, hcurrent, hcutoff, _hinput,
      _hfinal, _hcutfinal, _houtput, _hcalls⟩ := hsites v hv
    have hpay := hpayload record (List.getElem_mem hv) done.context hchoice
    have hcutNow : FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤ record.input.time.val + 1 := by
      rw [hpay, hrow, htrue]
      omega
    obtain ⟨d, hread, hzero, hcell, hcall⟩ := actual_choice_readout rate rewards C_star C_h z
      ⟨e + v, hk⟩ done.context (by exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => choice r.input) hkrActual).trans hchoice)
      (by rw [hpay]; exact hlater) (by
        have hp := congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          FollowerCutoffScan.firstCutoff p rate.eta.val done.context.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤ r.input.time.val + 1) hkrActual
        exact hp.mpr hcutNow)
    have hread := (congrArg (laterCollectionReadout s) hkrActual).symm.trans hread
    have hzero := (congrArg (laterCollectionReadout 0) hkrActual).symm.trans hzero
    have hcell := (congrArg (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) hkrActual).symm.trans hcell
    have hcall := (congrArg (laterCollectionCall 0) hkrActual).symm.trans hcall
    obtain ⟨hvD, hcellD⟩ := hcells ⟨v, hv⟩
    have hd : d = D[v] := Option.some.inj (hcell.symm.trans hcellD)
    have hDv : D[v]? = some d := by rw [List.getElem?_eq_getElem hvD, hd]
    refine ⟨d, done.context, hDv, hchoice, hpay, hbefore, hread, hzero, hcall, ?_⟩
    intro out candidate ho hc
    have hcandidate := actual_candidate_calendar rate record done.context d hzero hcall
      (A ++ D.take v) hcurrent out ho candidate hc
    have hword : A ++ D.take (v + 1) = (A ++ D.take v) ++ [d] := by
      rw [List.take_add_one, hDv, Option.toList_some, List.append_assoc]
    refine ⟨?_, ?_⟩
    · rw [hword]; exact hcandidate.1
    · rw [hcandidate.2]; exact hcutoff
  · intro record hr
    have hindex : R[e + D.length]? = some record := by
      rw [hD]
      exact first_excluded_original_index R e seg hseg record hr
    obtain ⟨hk, hkr⟩ := List.getElem?_eq_some_iff.mp hindex
    have hkrActual : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + D.length] = record := hkr
    have hboundaryCoord : record.input.state.coordinator = .collection seg.context.payload seg.final saved := by
      rcases hboundary with hhorizon | ⟨hv, _hstate, hcoord, _htime, _hdrop, _hlater⟩
      · have hh : ¬ e + D.length < R.length := by rw [hD, hhorizon]; exact Nat.lt_irrefl _
        exact False.elim (hh hk)
      · have hindexB : R[e + seg.records.length]? = some record := by simpa only [hD] using hindex
        have hrecB : (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[e + seg.records.length] = record :=
          (List.getElem?_eq_some_iff.mp hindexB).2
        exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          r.input.state.coordinator) hrecB).symm.trans hcoord
    have hfinal := hvalues D.length (Nat.le_refl _)
    have htakeR : seg.records.take D.length = seg.records := by rw [hD, List.take_length]
    simp only [List.take_length, htakeR] at hfinal
    change prefixInputs rate rewards C_star C_h (s + e + D.length) z = some (A ++ D) ∧
      (∀ a current, seg.final.currentRegisters a = some current →
        current.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q (A ++ D) (A ++ D).length a).2) ∧
      (∀ a cutoff, seg.final.cutoffRegisters a = some cutoff →
        cutoff.queue = (UnstoppedRecordedQueueComparison.unstoppedReplay Q A A.length a).2) at hfinal
    refine ⟨hindex, saved, hboundaryCoord, hfinal.2.1, hfinal.2.2, ?_⟩
    intro call hchoice
    have hpay := collection_choice_payload record.input _ _ _ call hboundaryCoord hchoice
    have hpre := choice_collection_pre record.input _ _ _ call hboundaryCoord hchoice
    have hspan := ReferenceCompleteCollectionIncrementSpan.complete_collection_input_increment_span
      rate rewards C_star C_h z ⟨e + D.length, hk⟩ seg.context.payload seg.final saved
      (by exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
        r.input.state.coordinator) hkrActual).trans hboundaryCoord)
    obtain ⟨_b, _hbk, _hbirth, _hbase, _hassign, _hstart, htruecut, _hfreeze,
      _hpos, _horder, _hT, hcutCursor, hcursor, _hspan⟩ := hspan
    have hrR : record ∈ R := by rw [← hkr]; exact List.getElem_mem hk
    have hrow : record.input.row = z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
      change record.input.rows record.input.selected = _
      rw [(hfields record hrR).1, (hfields record hrR).2.1]
    have hcutNow : FollowerCutoffScan.firstCutoff p rate.eta.val call.payload.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val record.input.row) ≤ record.input.time.val + 1 := by
      rw [hpay, hrow, ← htruecut]
      have hcursorR := hcursor.trans (congrArg
        (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => r.input.time.val + 1) hkrActual)
      omega
    obtain ⟨d, hread, hzero, hcell, hcall⟩ := actual_choice_readout rate rewards C_star C_h z
      ⟨e + D.length, hk⟩ call (by exact (congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => choice r.input) hkrActual).trans hchoice)
      (by rw [hpay]; exact hlater) (by
        have hp := congrArg (fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          FollowerCutoffScan.firstCutoff p rate.eta.val call.payload.sigma
            (FollowerCutoffScan.completeRowProposalBit p rate.eta.val r.input.row) ≤ r.input.time.val + 1) hkrActual
        exact hp.mpr hcutNow)
    have hread := (congrArg (laterCollectionReadout s) hkrActual).symm.trans hread
    have hzero := (congrArg (laterCollectionReadout 0) hkrActual).symm.trans hzero
    have hcell := (congrArg (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) hkrActual).symm.trans hcell
    have hcall := (congrArg (laterCollectionCall 0) hkrActual).symm.trans hcall
    have hfull : prefixInputs rate rewards C_star C_h (s + e + D.length) z = some (A ++ D) := by
      exact hfinal.1
    have happend := prefixInputs_append_one rate rewards C_star C_h
      (s + e + D.length) z (A ++ D) hfull record d
      (by simpa only [show s + e + D.length - sourceStart rate rewards C_star C_h z = e + D.length by omega] using hindex)
      hcell
    refine ⟨hpay, hpre.1, hpre.2, d, hread, hzero, hcell, hcall, happend, ?_⟩
    intro out candidate ho hc
    have hcandidate := actual_candidate_calendar rate record call d hzero hcall
      (A ++ D) (by rw [hpre.1]; exact hfinal.2.1) out ho candidate hc
    refine ⟨hcandidate.1, ?_⟩
    rw [hcandidate.2, hpre.1]
    exact hfinal.2.2

end Bandits.Support.ReferenceFirstCorrectedCollectionKnownQueueSource
