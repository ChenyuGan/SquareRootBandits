/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalCalendarCellPresence
public import Bandits.Support.ReferenceOriginalCalendarContinuingLiveRecorderLaw

import Mathlib.Tactic

/-!
# Actual physical calendar observations and queue replay

The source calendar is the complete physical suffix.  This file builds its
arrival observations from the retained physical dispatcher and recorder data,
then characterizes the zero-origin queue replay on every original boundary.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceActiveHorizonMeasurability
open ReferenceCoordinatorRecorderCallTrace
open ReferenceLaterLiveNumericalReadout
open ReferenceLaterCollectionArrivalReadout
open ReferenceContinuingRecordingPhysicalReward
open ReferenceContinuingRecordingFastPair
open ReferenceCollectionRawBufferHistory
open CoordinatorCollectionLedger
open ActiveRoundActions
open ContinuousControlSlice
open CanonicalRecordingSlice
open PublicDiscreteDraws
open scoped Classical

namespace Bandits.Support.ReferenceCompletePhysicalCalendarQueueTruth

variable {p : ConstructorDimensions.Parameters}

abbrev Record (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)

/-- A physical calendar cell retains the actual dispatcher selection, phase,
freeze bit, recorder result, whole reward row, marker, and every arm's natural
arrival.  The type is indexed by the same actual round record. -/
structure PhysicalCell (rate : ReferenceActivePhysicalStep.RateInput p) where
  record : Record rate
  selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate
  live : Bool
  enabled : Bool
  time : Fin p.T
  recorder : Option (CoordinatorRecordingOperation.Output p)
  marker : Option (Fin p.K)
  reward : Fin p.K → ℝ
  rateVector : Fin p.K → ℝ
  arrival : Fin p.K → ℕ

/-- Literal assignment ownership in LIVE and coordinator ownership in collection. -/
def PhysicalCell.owns {rate : ReferenceActivePhysicalStep.RateInput p}
    (cell : PhysicalCell rate) (owner : Fin p.m) (a : Fin p.K) : Prop :=
  if cell.live then
    if h : owner = coordinator p.two_le_m then
      a ∉ Finset.univ.image cell.selected.1.payload.assignment.assigned
    else a = cell.selected.1.payload.assignment.assigned (followerIndex p.two_le_m owner h)
  else owner = coordinator p.two_le_m

/-- The literal all-arm raw arrival in LIVE.  Off the slow set it is the
coordinator's retained raw output.  On the slow set it is the unique assigned
owner's current saved contribution or occupied online arrival.  A missing
occupied `lastDown` stays absent. -/
def livePhysicalArrival? (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : Record rate)
    (payload : ReferenceActivePhysicalStep.Payload rate) (arm : Fin p.K) : Option ℕ := by
  classical
  by_cases _hoffSlow : arm ∉ payload.slowSet.1
  · exact coordinatorRaw (roundRecordCode record) arm
  · by_cases hassigned : ∃ i : Fin (p.m - 1), payload.assignment.assigned i = arm
    · let i := Classical.choose hassigned
      match (record.output.preparation.followers.followers i).configuration with
      | .dagger => exact none
      | .ordinary state _ =>
          if hunoccupied : state.status = .unoccupied then
            exact some (actualCurrentSavedContribution record payload i)
          else
            match state.lastDown with
            | none => exact none
            | some down =>
                exact some (ActiveFollowerQueueOperation.rawArrival rate.eta i
                  record.input.row record.input.time down
                  (record.output.ownEntries (followerPlayer p.two_le_m i)).2)
    · exact none

/-- LIVE uses the coordinator's actual raw output off the assigned set and the
true owner's current saved or occupied raw amount on the assigned set.
COLLECTION uses the actual recorder input for every arm. -/
def physicalArrival? (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : Record rate)
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (live : Bool) (recorder : Option (CoordinatorRecordingOperation.Output p))
    (arm : Fin p.K) : Option ℕ :=
  if live then
    livePhysicalArrival? rate record selected.1.payload arm
  else
    match recorder with
    | none => none
    | some output => some (localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output) arm)

/-- Assemble all arm amounts only when each physical source amount is present.
There is no default value for a malformed occupied record. -/
noncomputable def physicalArrivalVector? (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : Record rate)
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (live : Bool) (recorder : Option (CoordinatorRecordingOperation.Output p)) :
    Option (Fin p.K → ℕ) := by
  classical
  by_cases htotal : ∀ arm, (physicalArrival? rate record selected live recorder arm).isSome = true
  · exact some (fun arm => (physicalArrival? rate record selected live recorder arm).get
      (htotal arm))
  · exact none

/-- The literal optional observer of an actual record.  It reads the retained
dispatcher/recorder branch.  The observer is an analytical projection and is
not an additional player register. -/
noncomputable def actualPhysicalObserver (rate : ReferenceActivePhysicalStep.RateInput p)
    (record : Record rate) : Option (PhysicalCell rate) := by
  classical
  let code := roundRecordCode record
  match cell code with
  | none => exact none
  | some (selected, live, enabled, recorder) =>
      if live then
        let marker := physicalMarkerOnRecord record selected.1.payload enabled
        match physicalArrivalVector? rate record selected live recorder with
        | none => exact none
        | some arrival =>
            exact some {
              record := record
              selected := selected
              live := live
              enabled := enabled
              time := record.input.time
              recorder := recorder
              marker := marker
              reward := fun arm => ((record.input.rewards record.input.time arm).val : ℝ) /
                (D p : ℝ)
              rateVector := selected.1.payload.rate
              arrival := arrival }
      else
        match recorder with
        | none => exact none
        | some output =>
            let marker := output.gateArm
            match physicalArrivalVector? rate record selected live recorder with
            | none => exact none
            | some arrival =>
                exact some {
                  record := record
                  selected := selected
                  live := live
                  enabled := enabled
                  time := record.input.time
                  recorder := recorder
                  marker := marker
                  reward := fun arm => ((record.input.rewards record.input.time arm).val : ℝ) /
                    (D p : ℝ)
                  rateVector := selected.1.payload.rate
                  arrival := arrival }

private theorem selection_on_record {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected) :
    selection (roundRecordCode r) =
      some (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) := by
  have hp : r.output.preparation = ReferenceActivePhysicalStep.prepare r.input := by
    rw [r.output_eq]
    rfl
  have hd : (ReferenceActivePhysicalStep.dispatch r.input).selection = some selected := by
    rw [hp] at hs
    exact hs
  exact (roundRecordCode_front r).1.trans (by rw [hd]; rfl)

private theorem live_arrival_of_physical_cell {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (c : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (hf : ∀ i, (c.states i).status ≠ .unoccupied →
      (c.states i).lastDown = some (c.selected.view.payload.downRecord i))
    (hcoord : ∀ a, a ∉ c.selected.view.payload.slowSet.1 →
      coordinatorRaw (roundRecordCode r) a = some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.input a))
    (hu : ∀ i, (c.states i).status = .unoccupied →
      actualCurrentSavedContribution r c.selected.view.payload i =
        RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          c.input (c.selected.view.payload.assignment.assigned i))
    (ho : ∀ i, (c.states i).status ≠ .unoccupied →
      ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
        (c.selected.view.payload.downRecord i)
        (r.output.ownEntries (followerPlayer p.two_le_m i)).2 =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        c.input (c.selected.view.payload.assignment.assigned i))
    (a : Fin p.K) :
    livePhysicalArrival? rate r c.selected.view.payload a =
      some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c.input a) := by
  classical
  by_cases ha : a ∉ c.selected.view.payload.slowSet.1
  · simpa only [livePhysicalArrival?, dite_eq_left ha] using hcoord a ha
  · have ha' : a ∈ c.selected.view.payload.slowSet.1 := by simpa only [not_not] using ha
    rw [← c.selected.view.payload.assignment_image] at ha'
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ha'
    have hex : ∃ j : Fin (p.m - 1), c.selected.view.payload.assignment.assigned j = a := ⟨i, hi⟩
    let j := Classical.choose hex
    have hj : c.selected.view.payload.assignment.assigned j = a := Classical.choose_spec hex
    have hji : j = i := c.selected.view.payload.assignment.injective (hj.trans hi.symm)
    simp only [livePhysicalArrival?, dite_eq_right ha, dite_eq_left hex]
    rw [show Classical.choose hex = i from hji]
    rw [c.ordinary i]
    by_cases hstatus : (c.states i).status = .unoccupied
    · simp only [dite_eq_left hstatus, hu i hstatus, hi]
    · simp only [dite_eq_right hstatus, hf i hstatus, ho i hstatus, hi]

private theorem vector_of_arrivals {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate)
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (live : Bool) (out : Option (CoordinatorRecordingOperation.Output p))
    (arrivals : Fin p.K → ℕ)
    (ha : ∀ a, physicalArrival? rate r selected live out a = some (arrivals a)) :
    physicalArrivalVector? rate r selected live out = some arrivals := by
  have ht : ∀ a, (physicalArrival? rate r selected live out a).isSome = true := by
    intro a
    rw [ha a]
    rfl
  simp only [physicalArrivalVector?, dite_eq_left ht]
  congr 1
  funext a
  simp only [ha a, Option.get_some]

private theorem arrivals_of_vector {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (live : Bool) (out : Option (CoordinatorRecordingOperation.Output p)) (arrivals : Fin p.K → ℕ)
    (hv : physicalArrivalVector? rate r selected live out = some arrivals) :
    ∀ a, physicalArrival? rate r selected live out a = some (arrivals a) := by
  unfold physicalArrivalVector? at hv
  split_ifs at hv with ht
  have he := Option.some.inj hv
  intro a
  rw [← he]
  exact (Option.some_get _).symm

/-- Every present observer preserves its literal selection, started clock,
phase, enabled bit, original whole reward table and actual raw source amounts.
This statement also applies to manufactured records whenever they are present. -/
theorem actualPhysicalObserver_fields {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (physical : PhysicalCell rate)
    (hobs : actualPhysicalObserver rate r = some physical) :
    physical.record = r ∧ selection (roundRecordCode r) = some physical.selected ∧
      physical.live = live (roundRecordCode r) physical.selected ∧
      physical.enabled = enabled (roundRecordCode r) physical.selected ∧
      physical.time = r.input.time ∧ physical.recorder = recording (roundRecordCode r) ∧
      physical.reward = (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      physical.rateVector = physical.selected.1.payload.rate ∧
      (if physical.live then
        physical.marker = physicalMarkerOnRecord r physical.selected.1.payload physical.enabled
      else ∃ out, physical.recorder = some out ∧ physical.marker = out.gateArm) ∧
      ∀ a, physicalArrival? rate r physical.selected physical.live physical.recorder a =
        some (physical.arrival a) := by
  unfold actualPhysicalObserver cell at hobs
  cases hs : selection (roundRecordCode r) with
  | none => simp only [hs, Option.map_none] at hobs; cases hobs
  | some selected =>
      simp only [hs, Option.map_some] at hobs
      split_ifs at hobs with hl
      · cases hv : physicalArrivalVector? rate r selected
            (live (roundRecordCode r) selected) (recording (roundRecordCode r)) with
        | none => simp only [hv] at hobs; cases hobs
        | some arrival =>
            simp only [hv, Option.some.injEq] at hobs
            cases hobs
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
              by simp only [hl, ite_true], arrivals_of_vector r selected _ _ arrival hv⟩
      · cases ho : recording (roundRecordCode r) with
        | none => simp only [ho] at hobs; cases hobs
        | some out =>
            simp only [ho] at hobs
            cases hv : physicalArrivalVector? rate r selected
                (live (roundRecordCode r) selected) (some out) with
            | none => simp only [hv] at hobs; cases hobs
            | some arrival =>
                simp only [hv, Option.some.injEq] at hobs
                cases hobs
                exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
                  by simp only [hl]; exact ⟨out, rfl, rfl⟩,
                  arrivals_of_vector r selected _ _ arrival hv⟩

private theorem observer_live {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hl : live (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true)
    (he : enabled (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true)
    (arrivals : Fin p.K → ℕ)
    (ha : ∀ a, livePhysicalArrival? rate r selected.view.payload a = some (arrivals a)) :
    ∃ physical, actualPhysicalObserver rate r = some physical ∧
      physical.record = r ∧ physical.selected =
        ReferenceLiveDispatchOutputMeasurability.encodeSelection selected ∧
      physical.live = true ∧ physical.enabled = true ∧
      physical.time = r.input.time ∧
      physical.marker = physicalMarkerOnRecord r selected.view.payload true ∧
      physical.reward = (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      physical.rateVector = selected.view.payload.rate ∧ physical.arrival = arrivals := by
  have hv : physicalArrivalVector? rate r
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) true
      (recording (roundRecordCode r)) = some arrivals :=
    vector_of_arrivals r _ true _ arrivals (by
      intro a
      exact ha a)
  unfold actualPhysicalObserver
  simp only [cell, selection_on_record r selected hs, Option.map_some, hl, he,
    hv]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem observer_collection {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (selected : ReferenceActivePhysicalStep.Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hl : live (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false)
    (out : CoordinatorRecordingOperation.Output p)
    (hout : r.coordinatorDiagnostics.recording = some out) :
    ∃ physical, actualPhysicalObserver rate r = some physical ∧
      physical.record = r ∧ physical.selected =
        ReferenceLiveDispatchOutputMeasurability.encodeSelection selected ∧
      physical.live = false ∧ physical.enabled = enabled (roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) ∧
      physical.time = r.input.time ∧ physical.recorder = some out ∧
      physical.marker = out.gateArm ∧
      physical.reward = (fun a => ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) ∧
      physical.rateVector = selected.view.payload.rate ∧
      physical.arrival = (fun a => localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a) := by
  have hr : recording (roundRecordCode r) = some out :=
    (recording_eq_actualDiagnostics r).trans hout
  have hv := vector_of_arrivals r
    (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) false (some out)
    (fun a => localArrival (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder out) a)
    (fun _ => rfl)
  unfold actualPhysicalObserver
  simp only [cell, selection_on_record r selected hs, Option.map_some, hl, hr, hv]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem collection_call_selection {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (s : ℕ) (payload : Payload rate) (ledger : Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hcall : laterCollectionCall s r = some ⟨payload, ledger, started, weights⟩) :
    ∃ selected : ReferenceActivePhysicalStep.Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      selected.view.payload = payload ∧ selected.started = started ∧
      live (roundRecordCode r)
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = false := by
  classical
  have hframes := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r
  unfold laterCollectionCall at hcall
  split_ifs at hcall with hf
  · cases hcoord : r.output.preparation.coordinator with
    | first outcome => simp only [hcoord] at hcall; cases outcome <;> cases hcall
    | dagger => simp only [hcoord] at hcall; cases hcall
    | invalidCollectionCutoff => simp only [hcoord] at hcall; cases hcall
    | collection P L clock cutoff outcome =>
        cases outcome
        case continuing core snapshot boundary scores =>
          simp only [hcoord, Option.some.injEq] at hcall
          cases hcall
          rw [hcoord] at hframes
          let selected : ReferenceActivePhysicalStep.Selection r.input :=
            (r.output.preparation.coordinator.selection).get (by
              simp only [hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
                Option.isSome_some])
          have hs : r.output.preparation.coordinator.selection = some selected :=
            (Option.some_get _).symm
          refine ⟨selected, ?_, ?_, ?_, ?_⟩
          · simpa only [hcoord] using hs
          · simp only [selected, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
              Option.get_some]
          · simp only [selected, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
              Option.get_some]
          · rw [live_eq_assignmentIsLive _ _ r.input.time rfl]
            simpa only [selected, hcoord, ReferenceActivePhysicalStep.DispatchCut.selection,
              Option.get_some, ReferenceLiveDispatchOutputMeasurability.encodeSelection]
              using decide_eq_false hframes.1
        all_goals simp only [hcoord] at hcall; cases hcall
    | live regs owned base outcome =>
        cases outcome
        case cutoffChosen dispatched hstart newLedger hinit hcand hd hc hp hn arm =>
          simp only [hcoord] at hcall
          split_ifs at hcall with hlater
          · simp only [Option.some.injEq] at hcall
            cases hcall
            rw [hcoord] at hframes
            let selected := ReferenceCoordinatorRecorderCallCorrespondence.selectionOfArm
              r.input regs.payload dispatched.startResult r.input.time
              (liveRegistersAt regs r.input.time).complementWeights arm rfl
            have hs : r.output.preparation.coordinator.selection = some selected := by
              rw [hcoord]
              exact ReferenceCoordinatorRecorderCallCorrespondence.selectionAt_eq ..
            refine ⟨selected, ?_, rfl, rfl, ?_⟩
            · simpa only [hcoord] using hs
            · rw [live_eq_assignmentIsLive _ _ r.input.time rfl]
              exact decide_eq_false hframes.1
        all_goals simp only [hcoord] at hcall; cases hcall

/-- Every present collection readout comes from the actual recorder for all
arms. Its marker is the coordinator gate, including failed and zero gates. -/
theorem collection_record_physical_observer {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (s : ℕ) (c : RecordedQueueRun.RoundInput p.K)
    (hc : laterCollectionReadout s r = some c) :
    ∃ physical, actualPhysicalObserver rate r = some physical ∧
      physical.record = r ∧ physical.live = false ∧ physical.enabled = c.enabled ∧
      physical.time = r.input.time ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (r).output.preparation.arms.actions owner = a ∧
        (r).gridFeedback owner = (r).input.rewards (r).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  obtain ⟨payload, ledger, started, weights, out, hcall, _hdiag, _hrun,
    _hen, he, hrate, hreward, hout, hgate, harr⟩ := laterCollectionReadout_call s r c hc
  obtain ⟨selected, hs, hp, ht, hl⟩ :=
    collection_call_selection r s payload ledger started weights hcall
  obtain ⟨physical, hobs, hr, _hselected, hlive, henabled, htime, _hrec,
    hmarker, hy, hxi, ha⟩ := observer_collection r selected hs hl out hout
  refine ⟨physical, hobs, hr, hlive, ?_, htime, hmarker.trans hgate,
    hy.trans hreward.symm, hxi.trans ((congrArg AssignmentStartPayload.Input.rate hp).trans hrate.symm), ?_, ?_⟩
  · rw [henabled, enabled_eq_time_before_startGrid]
    change decide (r.input.time.val + 1 < selected.started.clock.g) = c.enabled
    rw [ht]
    exact he.symm
  · intro a hmarker'
    have hg : out.gateArm = some a := hmarker.symm.trans hmarker'
    obtain ⟨_valid, _hd, _hs, _hf, _ho, hact, _hmask, _ht, hfeed, _hraw⟩ :=
      collectionRecorder_gated_feedback r
        ((laterCollectionReadout_domain s r).mp (by rw [hc]; rfl)).1
        payload started weights out a _hrun hg
    exact ⟨coordinator p.two_le_m,
      by simp only [PhysicalCell.owns, hlive, Bool.false_eq_true, ite_false], hact, hfeed⟩
  · intro a
    exact (congrFun ha a).trans (harr a)

private theorem actual_live_enabled {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (selected : Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hl : live (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true) :
    enabled (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
  have hd : (dispatch r.input).selection = some selected := by
    rw [r.output_eq] at hs
    exact hs
  have hb := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits r selected hd
  split at hb <;> simp_all only [Bool.false_eq_true]

/-- On the actual incoming-LIVE domain, retained DOWN fields and current
saved contributions give the same all-arm physical observer, without waiting
for any future decoder acceptance. -/
theorem continuing_record_physical_observer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) (q : Fin p.T)
    (hz : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
      rate rewards C_star C_h q) :
    ∃ (r : Record rate) (c : RecordedQueueRun.RoundInput p.K) (physical : PhysicalCell rate),
      ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
        rate rewards C_star C_h q z = some r ∧ laterLiveReadout 0 r = some c ∧
      actualPhysicalObserver rate r = some physical ∧
      physical.record = r ∧ physical.live = true ∧ physical.enabled = c.enabled ∧
      physical.time = r.input.time ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (r).output.preparation.arms.actions owner = a ∧
        (r).gridFeedback owner = (r).input.rewards (r).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  obtain ⟨r, c, cell, hr, hc, hinput, hmarker, _hfeedback, hf, hu, hraw⟩ :=
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualCell_physical
      rate rewards C_star C_h q z hz
  have hcoord : ∀ a, a ∉ cell.selected.view.payload.slowSet.1 →
      coordinatorRaw (roundRecordCode r) a = some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell.input a) := by
    intro a ha
    rcases (hraw a).2 with ⟨_, out, _, h⟩ | ⟨i, hi, _, _⟩
    · simpa only [hinput] using h
    · exact False.elim (ha (by
        rw [← cell.selected.view.payload.assignment_image]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩))
  have ho : ∀ i, (cell.states i).status ≠ .unoccupied →
      ActiveFollowerQueueOperation.rawArrival rate.eta i r.input.row r.input.time
        (cell.selected.view.payload.downRecord i)
        (r.output.ownEntries (followerPlayer p.two_le_m i)).2 =
      RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        cell.input (cell.selected.view.payload.assignment.assigned i) := by
    intro i hi
    rcases (hraw (cell.selected.view.payload.assignment.assigned i)).2 with
      ⟨hoff, _⟩ | ⟨j, hj, _, ha⟩
    · exact False.elim (hoff (by
        rw [← cell.selected.view.payload.assignment_image]
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))
    · have hji : j = i := cell.selected.view.payload.assignment.injective hj
      subst j
      simpa only [ite_eq_right hi, hinput] using ha
  have hl : live (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection cell.selected) = true := by
    rw [live_eq_assignmentIsLive _ _ r.input.time rfl]
    exact decide_eq_true cell.assignment_live
  have he := actual_live_enabled r cell.selected cell.selection_actual hl
  obtain ⟨physical, hobs, hrecord, _hselected, hplive, hpen, htime, hm, hy, hxi, ha⟩ :=
    observer_live r cell.selected cell.selection_actual hl he _
      (live_arrival_of_physical_cell r cell hf hcoord (by simpa only [hinput] using hu) ho)
  refine ⟨r, c, physical, hr, hc, hobs, hrecord, hplive,
    hpen.trans ((hinput ▸ cell.enabled).symm), htime, hm.trans hmarker.symm, ?_, ?_, ?_, ?_⟩
  · have hyc : cell.input.reward = (fun a =>
        ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) := by rw [cell.input_eq]; rfl
    exact hy.trans ((hinput ▸ hyc).symm)
  · have hxic : cell.input.rate = cell.selected.view.payload.rate := by rw [cell.input_eq]; rfl
    exact hxi.trans ((hinput ▸ hxic).symm)
  · intro a hma
    obtain ⟨owner, _howns, hact, hfeed, _hown⟩ :=
      _hfeedback a ((hm.trans hmarker.symm).symm.trans hma)
    have hwhole := (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
      rate rewards C_star C_h q z r hr).2.2.2
    exact ⟨owner, by simpa only [PhysicalCell.owns, hplive, _hselected,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection, SnapshotRecordingKernel.owns, ite_true]
      using _howns, hact, by simpa only [hwhole] using hfeed⟩
  · intro a
    simpa only [hinput] using congrFun ha a

private theorem sourcePart_normalize {rate : ReferenceActivePhysicalStep.RateInput p}
    (record : Record rate)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (started : CoordinatorPhaseClock.StartRoundResult p) (time : Fin p.T)
    (arm : CoordinatorRoundDispatch.ArmSelection registers.payload started time
      registers.complementWeights record.input.row)
    (htime : time = record.input.time)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (hgrid : record.input.time.val + 1 < started.clock.g) :
    let I := ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation registers started
    let v := CoordinatorRecorderComplementBridge.recorderInput_inputsValid I
      (ReferenceCoordinatorLiveRecording.liveRecordingInput_valid record.output.preparation
        registers started time arm)
    CoordinatorRecordingOperation.liveCoordinatorSourceMapPart
        (CoordinatorRecorderComplementBridge.recorderInput I) v registers.payload.assignment
        { missing := started.pending, status := fun i => (states i).status }
        (decide (¬ CoordinatorRecorderComplementBridge.isFrozen I)) =
      if recorderSourceFromScalar p.two_le_m (coordinate Label.rec (record.input.row.2 record.input.time).1) =
          coordinator p.two_le_m then
        ReferenceFirstWindowNumericalStream.sourceArm record registers.payload started.pending states
          registers.complementWeights (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)
          (by simpa [htime] using arm.choiceInputsValid)
      else none := by
  classical
  dsimp only
  have henabled : decide (¬ CoordinatorRecorderComplementBridge.isFrozen
      (ReferenceActivePhysicalStep.liveRecordingInput record.output.preparation registers started)) = true := by
    apply decide_eq_true
    intro hf
    have hge : record.input.time.val + 1 ≥ started.clock.g := hf.2
    omega
  rw [henabled]
  rfl

private theorem sourceCell_unit_payload {rate : ReferenceActivePhysicalStep.RateInput p}
    (r : Record rate) (P P' : Payload rate) (h : P = P')
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (v : CoordinatorLocalArmChoice.ChoiceInputsValid P none r.input.time (fun _ => 1))
    (v' : CoordinatorLocalArmChoice.ChoiceInputsValid P' none r.input.time (fun _ => 1)) :
    ReferenceFirstWindowNumericalStream.sourceCell r P Finset.univ states (fun _ => 1) none v =
      ReferenceFirstWindowNumericalStream.sourceCell r P' Finset.univ states (fun _ => 1) none v' := by
  subst P'
  rfl

section FirstRecording

open ReferenceFirstLaunchRecordingPhysicalMarker

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (q : Fin (M p)) (t : Fin p.T) (control0 : ContinuousLearningRows.TimeControl p)
    (x : RetainedStart rate rewards C_star C_h q t control0)
    (v : AssignmentVector p) (d : NonAssignmentControl p)

local notation "r₀" => ReferenceFirstLaunchRecordingPhysicalMarker.record
  rate rewards C_star C_h q t control0 x v d
local notation "P₀" => ReferenceFirstLaunchRecordingPhysicalMarker.payload
  rate rewards C_star C_h q t control0 x v d
local notation "c₀" => numericalCell rate rewards C_star C_h q t control0 x v d
local notation "s₀" => ReferenceFirstLaunchRecordingPhysicalMarker.states
  rate rewards C_star C_h q t control0 x v d
local notation "I₀" => physicalMarker rate rewards C_star C_h q t control0 x v d

/-- FIRST's actual recorder supplies every arm's literal arrival, including
undecoded assigned arms and recorded zero floors. This is on the existing
retained source coordinates, with no arrival or correctness premise. -/
theorem first_record_physical_observer :
    ∃ physical, actualPhysicalObserver rate r₀ = some physical ∧
      physical.record = r₀ ∧ physical.live = true ∧ physical.enabled = true ∧
      physical.time = (r₀).input.time ∧ physical.marker = (c₀).recordedArm ∧
      physical.reward = (c₀).reward ∧ physical.rateVector = (c₀).rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (r₀).output.preparation.arms.actions owner = a ∧
        (r₀).gridFeedback owner = (r₀).input.rewards (r₀).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c₀ a := by
  classical
  have hseed := record_seed rate rewards C_star C_h q t control0 x v d
  have hu : ∀ i, (s₀ i).status = .unoccupied := fun i =>
    (hseed.2.2.2 i).2.2.2.2.2.1
  obtain ⟨installed, arm, _hchosen, hbranch, hP, _, _, _, _, hcomp, _⟩ :=
    installation_exists rate rewards C_star C_h q t control0 x v d
  have hi := ReferenceActivePhysicalStep.dispatchFirst_chosen_installation
    (r₀).input installed arm _hchosen
  subst installed
  let installed := CoordinatorAssignmentRegisterInstall.installFirst
    (launchInput rate rewards C_star C_h q t control0 x v d)
  obtain ⟨htime, selected, hs, hselEq, _hin, _hf, out, hout, _hrun, hg, hraw, hcoord⟩ :=
    ReferenceFirstWindowRecordingTruth.first_branch_recording_truth r₀ installed arm hbranch
      s₀ (fun _ => ActiveFollowerLifecycle.initialMemory p)
      (record_prepared rate rewards C_star C_h q t control0 x v d)
      (fun i hi => False.elim (hi (hu i)))
  obtain ⟨selected', hs', hpayload, hpending, hcut, hweights, hlive, _hvalid⟩ :=
    selection_exists rate rewards C_star C_h q t control0 x v d
  have hsame : selected' = selected := Option.some.inj (hs'.symm.trans hs)
  subst selected'
  have hInstalledPayload : installed.registers.payload = P₀ := by
    have hh := congrArg (fun s : ReferenceActivePhysicalStep.Selection (r₀).input =>
      s.view.payload) hselEq
    exact hh.symm.trans hpayload
  have hprep : (r₀).output.preparation = ReferenceActivePhysicalStep.prepare (r₀).input := by
    rw [(r₀).output_eq]
    rfl
  have hframe := ReferenceCoordinatorRecorderCallCorrespondence.actual_call_frames r₀
  rw [hbranch] at hframe
  have hn := sourcePart_normalize r₀ installed.registers installed.startRoundResult
    installed.registers.time arm htime s₀ hframe.2.2
  rw [hprep] at hn
  have hmap : out.gateArm =
      if recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec ((r₀).input.row.2 (r₀).input.time).1) = coordinator p.two_le_m
      then I₀ else none := by
    rw [hg]
    calc
      _ = _ := hn
      _ = _ := by
        have hstartPending : installed.startRoundResult.pending = Finset.univ := by
          have hh := congrArg (fun s : ReferenceActivePhysicalStep.Selection (r₀).input =>
            s.view.pendingAtChoice) hselEq
          exact hh.symm.trans hpending
        have hstartCut : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
            installed.startRoundResult.clock.u = none := by
          have hh := congrArg (fun s : ReferenceActivePhysicalStep.Selection (r₀).input =>
            s.view.cutoff) hselEq
          exact hh.symm.trans hcut
        simp only [hstartPending, hstartCut]
        change (if _ then ReferenceFirstWindowNumericalStream.sourceArm r₀ P₀ Finset.univ s₀
          (fun _ => 1) none _ else none) = _
        rw [← numerical_arm_eq_physical rate rewards C_star C_h q t control0 x v d]
        rfl
  have hraw' : out.rawArrival = SnapshotRecordingKernel.recordedIncrement p rate.eta.val
      (P₀).anchor (fun j => RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
        ((r₀).input.rewards (r₀).input.time j)) out.gateArm := by
    simpa only [← hg, hInstalledPayload] using hraw
  have hcraw : ∀ a, a ∉ (P₀).slowSet.1 → coordinatorRaw (roundRecordCode r₀) a =
      some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c₀ a) := by
    intro a ha
    rw [hcoord a, (numerical_cell_readout rate rewards C_star C_h q t control0 x v d).2.2 a]
    by_cases hm : I₀ = some a
    · have howner := owner_feedback rate rewards C_star C_h q t control0 x v d a hm
      have hsource : sourceOwner v d = coordinator p.two_le_m := by
        by_contra hn
        have hh := howner.1
        simp only [SnapshotRecordingKernel.owns, dite_eq_right hn] at hh
        apply ha
        rw [← (P₀).assignment_image, payload_assignment rate rewards C_star C_h q t control0 x v d]
        exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, hh.symm⟩
      have hsrecord : recorderSourceFromScalar p.two_le_m
          (coordinate Label.rec ((r₀).input.row.2 (r₀).input.time).1) = coordinator p.two_le_m := by
        rw [record_slice rate rewards C_star C_h q t control0 x v d]
        exact hsource
      have hgate : out.gateArm = some a := by rw [hmap, ite_eq_left hsrecord, hm]
      rw [ite_eq_left hgate, ite_eq_left hm, hraw', hgate]
      obtain ⟨_, _, _, ht, hr⟩ := record_source_inputs rate rewards C_star C_h q t control0 x v d
      simp only [SnapshotRecordingKernel.recordedIncrement, payload_anchor, ht, hr,
        RealRewardGridCount.realRewardGridValue, rate.n_scale]
      congr 2
      ring
    · have hgate : out.gateArm ≠ some a := by
        rw [hmap]
        split_ifs
        · exact hm
        · intro h
          cases h
      rw [ite_eq_right hgate, ite_eq_right hm]
  have ha : ∀ a, livePhysicalArrival? rate r₀ selected.view.payload a =
      some (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c₀ a) := by
    intro a
    rw [hpayload]
    by_cases hoff : a ∉ (P₀).slowSet.1
    · simpa only [livePhysicalArrival?, dite_eq_left hoff] using hcraw a hoff
    · have hin : a ∈ (P₀).slowSet.1 := by simpa only [not_not] using hoff
      rw [← (P₀).assignment_image] at hin
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hin
      have hex : ∃ j : Fin (p.m - 1), (P₀).assignment.assigned j = a := ⟨i, hi⟩
      have hchoose : Classical.choose hex = i :=
        (P₀).assignment.injective ((Classical.choose_spec hex).trans hi.symm)
      simp only [livePhysicalArrival?, dite_eq_right hoff, dite_eq_left hex]
      rw [hchoose, record_prepared rate rewards C_star C_h q t control0 x v d i]
      simp only [hu i, dite_true]
      rw [show actualCurrentSavedContribution r₀ P₀ i =
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            c₀ ((P₀).assignment.assigned i) from
        current_saved_eq_numerical_arrival rate rewards C_star C_h q t control0 x v d i]
      rw [hi]
  have hl : live (roundRecordCode r₀)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
    rw [live_eq_assignmentIsLive _ _ (r₀).input.time rfl]
    exact decide_eq_true hlive
  have he : enabled (roundRecordCode r₀)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
    rw [enabled_eq_time_before_startGrid]
    change decide ((r₀).input.time.val + 1 < selected.started.clock.g) = true
    rw [hselEq]
    exact decide_eq_true hframe.2.2
  obtain ⟨physical, hobs, hr, _hsel, hlp, hep, ht, hm, hreward, hrate, harrival⟩ :=
    observer_live r₀ selected hs hl he _ ha
  refine ⟨physical, hobs, hr, hlp, hep, ht, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm, hpayload]
    exact (numerical_cell_readout rate rewards C_star C_h q t control0 x v d).2.1.symm
  · exact hreward
  · change physical.rateVector = (P₀).rate
    exact hrate.trans (congrArg AssignmentStartPayload.Input.rate hpayload)
  · intro a hma
    have hmark : physical.marker = I₀ := by rw [hm, hpayload]; rfl
    obtain ⟨_howns, hact, hfeed, _hown, _hy⟩ := owner_feedback
      rate rewards C_star C_h q t control0 x v d a (hmark.symm.trans hma)
    obtain ⟨_, _, _, htime, hwhole⟩ := record_source_inputs
      rate rewards C_star C_h q t control0 x v d
    exact ⟨sourceOwner v d, by simpa only [PhysicalCell.owns, hlp, _hsel,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection, hpayload, payload_assignment,
      SnapshotRecordingKernel.owns, ite_true] using _howns,
      hact, by simpa only [hwhole, htime] using hfeed⟩
  · intro a
    exact congrFun harrival a

private theorem first_record_readout (c : RecordedQueueRun.RoundInput p.K)
    (hc : laterLiveReadout 0 r₀ = some c) : c = c₀ := by
  obtain ⟨selected, ho, hs, _hpos, _hlive, hcell⟩ := laterLiveReadout_some 0 r₀ c hc
  obtain ⟨selected', hs', hp, hpend, hcut, hw, _, _⟩ :=
    selection_exists rate rewards C_star C_h q t control0 x v d
  have he : selected' = selected := Option.some.inj (hs'.symm.trans hs)
  subst selected'
  have hstates : preparedStates r₀ ho = s₀ := by
    funext i
    exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj
      ((prepared_configuration r₀ ho i).symm.trans
        (record_prepared rate rewards C_star C_h q t control0 x v d i))).1
  have hweights : selected.view.complementWeights = fun _ => 1 := funext hw
  have v0 : CoordinatorLocalArmChoice.ChoiceInputsValid selected.view.payload none
      (r₀).input.time (fun _ => 1) := by
    simpa only [hcut, hweights] using selection_choiceValid selected
  have hc' : c = ReferenceFirstWindowNumericalStream.sourceCell r₀ selected.view.payload
      Finset.univ s₀ (fun _ => 1) none v0 := by
    simpa only [hweights, hstates, hpend, hcut] using hcell
  exact hc'.trans (sourceCell_unit_payload r₀ selected.view.payload P₀ hp s₀ v0
    (first_choice_valid rate rewards C_star C_h q t control0 x v d))

end FirstRecording

/-- A later assignment's physical observer uses the new actual payload but
keeps the same original suffix and reward table. This is an arrival statement,
independent of any future UP completion. -/
theorem later_record_physical_observer
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).length)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : laterLiveReadout (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get k) = some c) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get k
    ∃ physical, actualPhysicalObserver rate r = some physical ∧
      physical.record = r ∧ physical.live = true ∧ physical.enabled = c.enabled ∧
      physical.time = r.input.time ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (r).output.preparation.arms.actions owner = a ∧
        (r).gridFeedback owner = (r).input.rewards (r).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  dsimp only
  let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).get k
  obtain ⟨cell, hinput, hen, hl, he, _hrows, _hJ, _hwhole, hmarker, hf,
    _hfeedback, ho, hu, _hlogging, ⟨out, _hout, hcoord⟩, _hbirth⟩ :=
    laterLiveReadout_physical rate rewards C_star C_h z k c hc
  obtain ⟨physical, hobs, hr, _hselected, hpl, hpe, ht, hm, hy, hxi, ha⟩ :=
    observer_live r cell.selected cell.selection_actual hl he _
      (live_arrival_of_physical_cell r cell hf (by simpa only [hinput] using hcoord)
        (by simpa only [hinput] using hu)
        (by intro i hi; simpa only [hinput] using (ho i hi).2))
  refine ⟨physical, hobs, hr, hpl, hpe.trans hen.symm, ht, hm.trans hmarker.symm, ?_, ?_, ?_, ?_⟩
  · have h : cell.input.reward = (fun a =>
        ((r.input.rewards r.input.time a).val : ℝ) / (D p : ℝ)) := by rw [cell.input_eq]; rfl
    exact hy.trans ((hinput ▸ h).symm)
  · have h : cell.input.rate = cell.selected.view.payload.rate := by rw [cell.input_eq]; rfl
    exact hxi.trans ((hinput ▸ h).symm)
  · intro a hma
    obtain ⟨owner, _howns, _hunique, hact, hfeed, _hown⟩ :=
      _hfeedback a ((hm.trans hmarker.symm).symm.trans hma)
    exact ⟨owner, by simpa only [PhysicalCell.owns, hpl, _hselected,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection, SnapshotRecordingKernel.owns, ite_true]
      using _howns, hact, by simpa only [_hwhole] using hfeed⟩
  · intro a
    simpa only [hinput] using congrFun ha a

section ActualSuffix

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "s" => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h

private theorem dispatch_origin (r : Record rate) :
    match r.output.preparation.coordinator with
    | .first _ => r.input.state.coordinator = .first
    | .live regs owned base _ => r.input.state.coordinator = .live regs owned base
    | .collection P L _ _ _ => ∃ saved, r.input.state.coordinator = .collection P L saved
    | .dagger => r.input.state.coordinator = .dagger
    | .invalidCollectionCutoff => True := by
  have hp : r.output.preparation.coordinator = dispatch r.input := by
    rw [r.output_eq]
    rfl
  rw [hp]
  unfold dispatch
  cases hc : r.input.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; trivial
  | live regs owned base => simp only [CoordinatorRoundDispatch.dispatch]; rfl
  | collection P L saved =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split_ifs <;> first | exact ⟨saved, rfl⟩ | trivial
  | dagger => rfl

private theorem selector_readout (r : Record rate) (c : RecordedQueueRun.RoundInput p.K)
    (hc : laterLiveReadout 0 r = some c) (selected : Selection r.input)
    (hs : r.output.preparation.coordinator.selection = some selected)
    (hstrict : s < selected.view.payload.sigma.val) :
    laterLiveReadout s r = some c := by
  obtain ⟨selected', ho, hs', _, hl, heq⟩ := laterLiveReadout_some 0 r c hc
  have he : selected' = selected := Option.some.inj (hs'.symm.trans hs)
  subst selected'
  have hcond : s < selected.view.payload.sigma.val ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff r.input.time :=
    ⟨hstrict, hl⟩
  simp only [laterLiveReadout, hs, hcond, dite_eq_left ho]
  exact congrArg some heq.symm

private theorem actual_incoming_not_first (k : Fin (R).length) (hk : k.val ≠ 0) :
    ((R).get k).input.state.coordinator ≠ .first := by
  have hpred : k.val - 1 < (R).length := by omega
  have hadj := ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
    (rate := rate) rewards C_star C_h z (k.val - 1) (by omega)
  have hprev := (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
    rate rewards C_star C_h z).1 ⟨k.val - 1, hpred⟩
  have he : k.val - 1 + 1 = k.val := by omega
  have hadj' : ((R).get k).input.state = (R[k.val - 1]).output.next := by
    simpa only [he, List.get_eq_getElem] using hadj
  exact fun h => hprev.2.2.2.1 ((congrArg State.coordinator hadj').symm.trans h)

private theorem actual_record_lookup (k : Fin (R).length) :
    ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
      rate rewards C_star C_h ((R).get k).input.time z = some ((R).get k) := by
  have htime : ((R).get k).input.time.val = s + k.val :=
    ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
      rate z rewards C_star C_h k.val ((R).get k) (List.getElem?_eq_getElem k.isLt)
  unfold ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualRecordAt
    ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left (by omega), htime, Nat.add_sub_cancel_left]
  exact List.getElem?_eq_getElem k.isLt

private theorem first_actual_record_observer (k : Fin (R).length) (hk : k.val = 0)
    (c : RecordedQueueRun.RoundInput p.K) (hc : laterLiveReadout 0 ((R).get k) = some c) :
    ∃ physical, actualPhysicalObserver rate ((R).get k) = some physical ∧
      physical.record = (R).get k ∧ physical.live = true ∧ physical.enabled = c.enabled ∧
      physical.time = ((R).get k).input.time ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (((R).get k)).output.preparation.arms.actions owner = a ∧
        (((R).get k)).gridFeedback owner = (((R).get k)).input.rewards (((R).get k)).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  obtain ⟨hcross, hspan, hrecord⟩ := source_record_prefix rate rewards C_star C_h z k
  have hs : s < p.T := by omega
  let t : Fin p.T := ⟨s, hs⟩
  let q := BootstrapPrivateRoundStreams.sourceCoordinatorIndex p z
  let control0 : ContinuousLearningRows.TimeControl p := (z.1.2 q).2 t
  let zs : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := ⟨z, rfl, hcross, rfl⟩
  let coords := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h q t control0 zs
  have htransport := ReferenceFirstLaunchRecordingSourceLaw.source_record_eq
    rate rewards C_star C_h q t control0 zs
  have hfirst : (R).get k = ReferenceFirstLaunchNumericalCell.firstPhysicalRecord
      rate z rewards C_star C_h hcross hs := by
    rw [hrecord]
    simp only [hk]
    rfl
  have hr : ReferenceFirstLaunchRecordingPhysicalMarker.record
      rate rewards C_star C_h q t control0 coords.1 coords.2.1 coords.2.2 = (R).get k :=
    htransport.trans hfirst.symm
  have hread := first_record_readout rate rewards C_star C_h q t control0
    coords.1 coords.2.1 coords.2.2 c (by rw [hr]; exact hc)
  rw [hread]
  have hen := (ReferenceFirstLaunchRecordingPhysicalMarker.numerical_cell_readout
    rate rewards C_star C_h q t control0 coords.1 coords.2.1 coords.2.2).1
  have hacts := congrArg (fun r : Record rate => r.output.preparation.arms.actions) hr
  simpa only [hacts, hr, hen] using first_record_physical_observer rate rewards C_star C_h q t control0
    coords.1 coords.2.1 coords.2.2

private theorem actual_live_record_observer (k : Fin (R).length)
    (c : RecordedQueueRun.RoundInput p.K) (hc : laterLiveReadout 0 ((R).get k) = some c) :
    ∃ physical, actualPhysicalObserver rate ((R).get k) = some physical ∧
      physical.record = (R).get k ∧ physical.live = true ∧ physical.enabled = c.enabled ∧
      physical.time = ((R).get k).input.time ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (((R).get k)).output.preparation.arms.actions owner = a ∧
        (((R).get k)).gridFeedback owner = (((R).get k)).input.rewards (((R).get k)).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  by_cases hk : k.val = 0
  · exact first_actual_record_observer rate rewards C_star C_h z k hk c hc
  let r := (R).get k
  obtain ⟨selected, _ho, hs, _hpos, hlive, _heq⟩ := laterLiveReadout_some 0 r c hc
  have hl : live (roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true := by
    rw [live_eq_assignmentIsLive _ _ r.input.time rfl]
    exact decide_eq_true hlive
  have hd : (dispatch r.input).selection = some selected := by
    rw [r.output_eq] at hs
    exact hs
  have hb := ReferenceCoordinatorRecorderCallCorrespondence.actual_phase_bits r selected hd
  have horigin := dispatch_origin rate r
  have hn := actual_incoming_not_first rate rewards C_star C_h z k hk
  have hlookup := actual_record_lookup rate rewards C_star C_h z k
  generalize hcut : r.output.preparation.coordinator = cut at hb horigin
  cases cut with
  | first outcome => exact False.elim (hn horigin)
  | live regs owned base outcome =>
      have hz : z ∈ ReferenceOriginalCalendarContinuingLiveRecorderLaw.actualDomain
          rate rewards C_star C_h r.input.time := ⟨r, hlookup, ⟨regs, owned, base, horigin⟩, by rw [hc]; rfl⟩
      obtain ⟨r', c', physical, hr', hc', hp, hrec, hpl, he, ht, hm, hy, hxi, hfeedback, ha⟩ :=
        continuing_record_physical_observer rate rewards C_star C_h z r.input.time hz
      have hr : r' = r := Option.some.inj (hr'.symm.trans hlookup)
      rw [hr] at hc' hp hrec ht
      have hacts := congrArg (fun r : Record rate => r.output.preparation.arms.actions) hr
      simp only [hacts, hr] at hfeedback
      have heq : c' = c := Option.some.inj (hc'.symm.trans hc)
      subst c'
      exact ⟨physical, hp, hrec, hpl, he, ht, hm, hy, hxi, hfeedback, ha⟩
  | collection P L clock cutoff outcome =>
      cases outcome
      case laterChosen core consistent started hstart instruction hi output hcons clockData installed arm =>
        have hchosen : ReferenceCollectionPhaseHistory.laterChosen r.input = true := by
          unfold ReferenceCollectionPhaseHistory.laterChosen
          have hp : r.output.preparation = prepare r.input := by rw [r.output_eq]; rfl
          rw [← hp, hcut]
        obtain ⟨P0, rb, qb, beta, birthCell, native, _, _, _, _, _, _, hstrict,
          _, _, _, hpay, _⟩ :=
          ReferenceCompleteInstallationCollectionPrefixNumericalTruth.actual_later_installation_collection_prefix_numerical_truth
            rate rewards C_star C_h z k hchosen
        have hsel : native.selected = selected :=
          Option.some.inj (native.selection_actual.symm.trans hs)
        have hstrict' : s < selected.view.payload.sigma.val := by
          rw [← hsel, hpay]
          exact hstrict
        exact later_record_physical_observer rate rewards C_star C_h z k c
          (selector_readout rate rewards C_star C_h z r c hc selected hs hstrict')
      all_goals simp only [hl, Bool.true_eq_false, false_and] at hb
  | dagger => cases hb
  | invalidCollectionCutoff => cases hb

/-- Every actual original physical suffix record has a total literal observer
and the same enabled bit, marker, whole reward/rate vectors and all-arm raw
arrivals as its present numerical cell. No overflow stop filters this suffix. -/
theorem actual_record_physical_observer (k : Fin (R).length) :
    ∃ (c : RecordedQueueRun.RoundInput p.K) (physical : PhysicalCell rate),
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate ((R).get k) = some c ∧
      actualPhysicalObserver rate ((R).get k) = some physical ∧
      physical.record = (R).get k ∧ physical.enabled = c.enabled ∧
      physical.time = ((R).get k).input.time ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ (((R).get k)).output.preparation.arms.actions owner = a ∧
        (((R).get k)).gridFeedback owner = (((R).get k)).input.rewards (((R).get k)).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  have hphase := (ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
    rate rewards C_star C_h z k).2
  cases hc : laterLiveReadout 0 ((R).get k) with
  | some c =>
      obtain ⟨physical, hp, hr, _hl, he, ht, hm, hy, hxi, hfeedback, ha⟩ :=
        actual_live_record_observer rate rewards C_star C_h z k c hc
      exact ⟨c, physical, by simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0,
        hc, Option.some_or], hp, hr, he, ht, hm, hy, hxi, hfeedback, ha⟩
  | none =>
      rcases hphase with hl | ⟨c, hcol⟩
      · have h := (laterLiveReadout_domain 0 ((R).get k)).mpr hl
        rw [hc] at h
        cases h
      · obtain ⟨physical, hp, hr, _hl, he, ht, hm, hy, hxi, hfeedback, ha⟩ :=
          collection_record_physical_observer ((R).get k) 0 c hcol
        exact ⟨c, physical, by simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0,
          hc, Option.none_or]; exact hcol, hp, hr, he, ht, hm, hy, hxi, hfeedback, ha⟩

/-- Totality is derived on the complete actual source suffix before any total
word is extracted. Manufactured missing selections and DOWN records remain absent. -/
theorem actualPhysicalObserver_total (k : Fin (R).length) :
    (actualPhysicalObserver rate ((R).get k)).isSome = true := by
  obtain ⟨_, physical, _, hp, _⟩ := actual_record_physical_observer rate rewards C_star C_h z k
  rw [hp]
  rfl

end ActualSuffix

/-- Project a physical cell to the queue input at this original date. -/
def PhysicalCell.queueInput {rate : ReferenceActivePhysicalStep.RateInput p}
    (cell : PhysicalCell rate) (arm : Fin p.K) : Bool × ℕ :=
  (cell.enabled, cell.arrival arm)

/-- The literal Option-valued sequence of observations on the original
physical suffix.  Missing actual selections or raw arrivals remain `none`. -/
def actualPhysicalOptionWord (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : List (Option (PhysicalCell rate)) :=
  (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h).map
    (actualPhysicalObserver rate)

/-- The total physical word exists only when every actual record has its
literal physical observer.  This partial word preserves all failure branches. -/
def actualPhysicalWord? (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Option (List (PhysicalCell rate)) :=
  (actualPhysicalOptionWord rate z rewards C_star C_h).mapM id

private theorem listOptionMapM_isSome {β : Type*} (observations : List (Option β)) :
    (observations.mapM id).isSome = true ↔
      ∀ observation, observation ∈ observations → observation.isSome = true := by
  induction observations with
  | nil => simp
  | cons observation rest ih =>
      cases observation with
      | none => simp
      | some value =>
          simp only [List.mapM_cons]
          cases htail : (rest.mapM id) with
          | none =>
              have hnot : ¬ ∀ observation, observation ∈ rest → observation.isSome = true := by
                intro hall
                have hmap := ih.mpr hall
                simp [htail] at hmap
              simp [hnot]
          | some tail =>
              have hall : ∀ observation, observation ∈ rest → observation.isSome = true :=
                ih.mp (by simp [htail])
              simp
              exact hall

/-- A total physical word can be extracted exactly when every original
suffix record has an actual observer. -/
theorem actualPhysicalWord?_isSome_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (actualPhysicalWord? rate z rewards C_star C_h).isSome = true ↔
      ∀ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h,
        (actualPhysicalObserver rate record).isSome = true := by
  change (((ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h).map (actualPhysicalObserver rate)).mapM id).isSome = true ↔
      ∀ record ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h,
        (actualPhysicalObserver rate record).isSome = true
  rw [listOptionMapM_isSome]
  constructor
  · intro h record hrecord
    exact h (actualPhysicalObserver rate record)
      (List.mem_map.mpr ⟨record, hrecord, rfl⟩)
  · intro h observation hobservation
    rcases List.mem_map.mp hobservation with ⟨record, hrecord, rfl⟩
    exact h record hrecord

/-- A zero-origin physical calendar replay is the literal fold of the actual
physical observer's enabled/arrival projection. -/
def physicalReplay (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (Bool × (Fin p.K → ℕ))) (arm : Fin p.K) (h : ℕ) : ℕ × ℕ :=
  QueueReplay.replay (4 * rate.n) (0, 0)
    ((word.take h).map fun cell => (cell.1, cell.2 arm))

/-- The replay is a literal one-record queue transition at every nonterminal
boundary.  In particular, an enabled zero arrival still serves old backlog. -/
theorem physicalReplay_succ (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (Bool × (Fin p.K → ℕ))) (arm : Fin p.K) (h : ℕ)
    (hh : h < word.length) :
    physicalReplay rate word arm (h + 1) =
      QueueReplay.transition (4 * rate.n) (physicalReplay rate word arm h)
        ((word[h].1, word[h].2 arm)) := by
  simp only [physicalReplay, List.take_succ_eq_append_getElem hh, List.map_append,
    List.map_singleton, QueueReplay.replay_append]
  rfl

/-- The full enabled/disabled source recurrence, including service on enabled
zero-arrival records and preservation on disabled records. -/
theorem physicalReplay_recurrence (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (Bool × (Fin p.K → ℕ))) (arm : Fin p.K) (h : ℕ)
    (hh : h < word.length) :
    physicalReplay rate word arm (h + 1) =
      if word[h].1 then
        let backlog := (physicalReplay rate word arm h).2
        let arrival := word[h].2 arm
        let service := min (4 * rate.n) (backlog + arrival)
        ((physicalReplay rate word arm h).1 + service, backlog + arrival - service)
      else physicalReplay rate word arm h := by
  rw [physicalReplay_succ rate word arm h hh]
  simp only [QueueReplay.transition]

/-- Any sequence satisfying the same zero-origin recurrence is the unique
QueueReplay fold on the complete input word. -/
theorem physicalReplay_unique (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (Bool × (Fin p.K → ℕ)))
    (registers : ℕ → Fin p.K → ℕ × ℕ)
    (horigin : ∀ arm, registers 0 arm = (0, 0))
    (hstep : ∀ h (hh : h < word.length) arm,
      registers (h + 1) arm = QueueReplay.transition (4 * rate.n)
        (registers h arm) ((word.get ⟨h, hh⟩).1, (word.get ⟨h, hh⟩).2 arm)) :
    ∀ h arm, h ≤ word.length → registers h arm = physicalReplay rate word arm h := by
  intro h
  induction h with
  | zero =>
      intro arm _
      rw [horigin arm]
      rfl
  | succ h ih =>
      intro arm hh
      have hlt : h < word.length := by omega
      calc
        registers (h + 1) arm = QueueReplay.transition (4 * rate.n)
            (registers h arm) ((word.get ⟨h, hlt⟩).1, (word.get ⟨h, hlt⟩).2 arm) :=
          hstep h hlt arm
        _ = QueueReplay.transition (4 * rate.n)
            (physicalReplay rate word arm h) ((word.get ⟨h, hlt⟩).1, (word.get ⟨h, hlt⟩).2 arm) := by
              rw [ih arm (by omega)]
        _ = physicalReplay rate word arm (h + 1) :=
              (physicalReplay_succ rate word arm h hlt).symm

/-- Conservation of score plus queue against every enabled natural arrival in
the complete replayed prefix. -/
theorem physicalReplay_conservation (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (Bool × (Fin p.K → ℕ))) (arm : Fin p.K) (h : ℕ) :
    (physicalReplay rate word arm h).1 + (physicalReplay rate word arm h).2 =
      RecordedQueueRun.acceptedTotal
        ((word.take h).map fun cell => (cell.1, cell.2 arm)) := by
  simpa [physicalReplay] using
    RecordedQueueRun.replay_total (4 * rate.n) (0, 0)
      ((word.take h).map fun cell => (cell.1, cell.2 arm))

/-- Project an extracted physical word to its actual queue inputs. -/
def physicalRawWord (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (PhysicalCell rate)) :
    List (Bool × (Fin p.K → ℕ)) :=
  word.map fun cell => (cell.enabled, cell.arrival)

/-- The physical score/backlog state is replayed from the one source origin,
without resetting at a later assignment installation. -/
def actualCalendarReplay (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (PhysicalCell rate)) (arm : Fin p.K) (h : ℕ) : ℕ × ℕ :=
  physicalReplay rate (physicalRawWord rate word) arm h

/-- The complete extracted physical suffix starts at zero score and zero
backlog for every arm. -/
theorem actualCalendarReplay_origin (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (PhysicalCell rate)) (arm : Fin p.K) :
    actualCalendarReplay rate word arm 0 = (0, 0) := rfl

/-- Conservation for every extracted physical prefix and every arm. -/
theorem actualCalendarReplay_conservation (rate : ReferenceActivePhysicalStep.RateInput p)
    (word : List (PhysicalCell rate)) (arm : Fin p.K) (h : ℕ) :
    (actualCalendarReplay rate word arm h).1 + (actualCalendarReplay rate word arm h).2 =
      RecordedQueueRun.acceptedTotal
        (((physicalRawWord rate word).take h).map fun cell => (cell.1, cell.2 arm)) := by
  exact physicalReplay_conservation rate (physicalRawWord rate word) arm h

section CompleteWord

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (z : BootstrapPrivateRoundStreams.SourceInput p)

local notation "R" => ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
local notation "s" => ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h

/-- The unique total word extracted from the now-proved-total literal observer
on every original physical date, including all post-overflow records. -/
def actualPhysicalWord : List (PhysicalCell rate) :=
  List.ofFn fun k : Fin (R).length => (actualPhysicalObserver rate ((R).get k)).get
    (actualPhysicalObserver_total rate rewards C_star C_h z k)

local notation "W" => actualPhysicalWord rate rewards C_star C_h z

@[simp] theorem actualPhysicalWord_length : (W).length = (R).length := List.length_ofFn

/-- Every extracted cell is exactly the literal observer at that original index. -/
theorem actualPhysicalWord_observed (k : Fin (R).length) :
    actualPhysicalObserver rate ((R).get k) =
      some ((W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩) := by
  simp only [actualPhysicalWord, List.get_ofFn]
  exact (Option.some_get _).symm

/-- Lossless whole-word observation, with no dropped absent-marker date. -/
theorem actualPhysicalWord_observation :
    (R).map (actualPhysicalObserver rate) = (W).map some := by
  apply List.ext_getElem
  · simp only [List.length_map, actualPhysicalWord_length]
  · intro i hi hj
    simp only [List.getElem_map]
    exact actualPhysicalWord_observed rate rewards C_star C_h z ⟨i, by simpa using hi⟩

/-- At each original date, the one extracted physical cell has the actual
owner's action and original reward feedback, and agrees with the same cell0
in every field and every natural raw arrival. -/
theorem actualPhysicalWord_characterization (k : Fin (R).length) :
    let physical := (W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate ((R).get k) = some c ∧
      physical.record = (R).get k ∧ physical.time = ((R).get k).input.time ∧
      physical.enabled = c.enabled ∧ physical.marker = c.recordedArm ∧
      physical.reward = c.reward ∧ physical.rateVector = c.rate ∧
      (∀ a, physical.marker = some a → ∃ owner : Fin p.m,
        physical.owns owner a ∧ ((R).get k).output.preparation.arms.actions owner = a ∧
        ((R).get k).gridFeedback owner = ((R).get k).input.rewards ((R).get k).input.time a) ∧
      ∀ a, physical.arrival a = RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a := by
  dsimp only
  obtain ⟨c, physical, hc, hp, hr, he, ht, hm, hy, hxi, hf, ha⟩ :=
    actual_record_physical_observer rate rewards C_star C_h z k
  have hw := actualPhysicalWord_observed rate rewards C_star C_h z k
  have heq := Option.some.inj (hp.symm.trans hw)
  rw [heq] at hr he ht hm hy hxi hf ha
  exact ⟨c, hc, hr, ht, he, hm, hy, hxi, hf, ha⟩

/-- Every actual selected payload carries a unique all-arm assignment
partition from the physical CHOICE states. Occupied followers retain that
payload's actual DOWN record. No future acceptance is required. -/
theorem actual_selected_assignment_owner_partition (k : Fin (R).length)
    (selected : Selection ((R).get k).input)
    (hs : ((R).get k).output.preparation.coordinator.selection = some selected) :
    ∃ (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
      (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p),
      (∀ i, (((R).get k).output.preparation.followers.followers i).configuration =
        .ordinary (states i) (memories i)) ∧
      (∀ i, (states i).status ≠ .unoccupied →
        (states i).lastDown = some (selected.view.payload.downRecord i)) ∧
      ∀ a, ∃! owner : Fin p.m, SnapshotRecordingKernel.owns p
        (.live selected.view.payload.assignment
          (ReferenceActiveDataOwnership.choiceSnapshot selected states)) owner a := by
  obtain ⟨states, memories, ho, hf, _, _⟩ :=
    ReferenceCompletePayloadChoiceChronology.complete_selected_payload_choice_fields
      (rate := rate) rewards C_star C_h z k selected hs
  refine ⟨states, memories, ho, hf, ?_⟩
  intro a
  let regime := SnapshotRecordingKernel.Regime.live selected.view.payload.assignment
    (ReferenceActiveDataOwnership.choiceSnapshot selected states)
  obtain ⟨owner, howner⟩ := SnapshotRecordingKernel.exists_ownerSource p regime a
  exact ⟨owner, howner, fun other hother =>
    SnapshotRecordingKernel.owns_unique p regime a other owner hother howner⟩

/-- The observed physical word is unique as a whole word, not merely up to a
raw-arrival projection. -/
theorem actualPhysicalWord_unique (word : List (PhysicalCell rate))
    (hword : (R).map (actualPhysicalObserver rate) = word.map some) : word = W := by
  apply List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h)
  exact hword.symm.trans (actualPhysicalWord_observation rate rewards C_star C_h z)

/-- Enabled/marker/whole reward/rate/all-arm arrival view of a physical cell. -/
def physicalView (cell : PhysicalCell rate) :=
  (cell.enabled, cell.marker, cell.reward, cell.rateVector, cell.arrival)

/-- Same-typed numerical view; this is a projection, not a new numerical word. -/
def numericalView (cell : RecordedQueueRun.RoundInput p.K) :=
  (cell.enabled, cell.recordedArm, cell.reward, cell.rate,
    RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell)

private theorem observer_view (r : Record rate) (hr : r ∈ R) :
    (actualPhysicalObserver rate r).map (physicalView rate) =
      (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate r).map (numericalView rate) := by
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hr
  subst r
  obtain ⟨c, physical, hc, hp, _, he, _, hm, hy, hxi, _hfeedback, ha⟩ :=
    actual_record_physical_observer rate rewards C_star C_h z k
  rw [hp, hc]
  simp only [Option.map_some, physicalView, numericalView, he, hm, hy, hxi, funext ha]

/-- A source-bound physical score/queue, defined by literal zero-seeded replay
of the complete original physical word. Later installations never reset it. -/
def sourceCalendarReplay (arm : Fin p.K) (h : ℕ) : ℕ × ℕ :=
  actualCalendarReplay rate W arm h

/-- One physical word and P's one numerical word agree in every metadata and
all-arm raw field, at every original date and boundary. No-launch retains
absent numerical prefixes; a terminal launch has a present empty word. -/
theorem complete_physical_calendar_word :
    match ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
    | none => W = [] ∧ s = p.T ∧
        (∀ n, ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
          rate rewards C_star C_h n z = none)
    | some _ => ∃ L : List (RecordedQueueRun.RoundInput p.K),
        L.length = (R).length ∧
        (R).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate) = L.map some ∧
        (∀ h, h ≤ (R).length →
          ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
            rate rewards C_star C_h (s + h) z = some (L.take h)) ∧
        (W).map (physicalView rate) = L.map (numericalView rate) ∧
        physicalRawWord rate W = L.map (fun c => (c.enabled,
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c)) ∧
        ∀ h a, sourceCalendarReplay rate rewards C_star C_h z a h =
          ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay rate L a h := by
  have hp := ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
    rate rewards C_star C_h z
  cases hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
  | none =>
      rw [hl] at hp
      obtain ⟨hr, hs, hn⟩ := hp
      refine ⟨?_, hs, hn⟩
      apply List.eq_nil_of_length_eq_zero
      rw [actualPhysicalWord_length, hr]
      rfl
  | some active =>
      rw [hl] at hp
      obtain ⟨L, hlen, hmap, hpref, _hphase⟩ := hp
      have hview : (W).map (physicalView rate) = L.map (numericalView rate) := by
        apply List.map_injective_iff.mpr (fun _ _ h => Option.some.inj h)
        have hh : ((R).map (actualPhysicalObserver rate)).map (Option.map (physicalView rate)) =
            ((R).map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).map
              (Option.map (numericalView rate)) := by
          simp only [List.map_map]
          apply List.map_congr_left
          exact observer_view rate rewards C_star C_h z
        rw [actualPhysicalWord_observation, hmap] at hh
        simpa only [List.map_map, Function.comp_def, Option.map_some] using hh
      have hraw : physicalRawWord rate W = L.map (fun c => (c.enabled,
          RecordedQueueRun.quantizedArrival (ReferenceFirstLaunchNumericalCell.queueParameters rate) c)) := by
        have hh := congrArg (List.map fun v => (v.1, v.2.2.2.2)) hview
        simpa only [List.map_map, Function.comp_def, physicalView, numericalView, physicalRawWord] using hh
      refine ⟨L, hlen, hmap, hpref, hview, hraw, ?_⟩
      intro h a
      simp only [sourceCalendarReplay, actualCalendarReplay, physicalReplay, hraw,
        ← List.map_take, List.map_map, Function.comp_def,
        ReferenceFirstCorrectedNextCalendarWordJoin.calendarReplay,
        ReferenceFirstCorrectedNextCalendarWordJoin.rawCalendar]

/-- Disabled physical dates have an absent marker and zero raw arrivals;
they are distinct from enabled dates with a zero recorded floor. -/
theorem actualPhysicalWord_disabled (k : Fin (R).length)
    (hdisabled : ((W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩).enabled = false) :
    let physical := (W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩
    physical.marker = none ∧ ∀ a, physical.arrival a = 0 := by
  dsimp only
  obtain ⟨c, hc, _hr, _ht, he, hm, _hy, _hxi, _hf, ha⟩ :=
    actualPhysicalWord_characterization rate rewards C_star C_h z k
  have hen : c.enabled = false := he.symm.trans hdisabled
  cases hread : laterLiveReadout 0 ((R).get k) with
  | some liveCell =>
      have hcell : c = liveCell := Option.some.inj (hc.symm.trans (by
        simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread, Option.some_or]))
      have htrue := (laterLiveReadout_numerical 0 ((R).get k) liveCell hread).1
      rw [← hcell, hen] at htrue
      cases htrue
  | none =>
      have hcol : laterCollectionReadout 0 ((R).get k) = some c := by
        simpa only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hread, Option.none_or] using hc
      obtain ⟨P, L, started, weights, out, _hcall, _hdiag, hrun, _hen, hclock,
        _hxi, _hy, _hout, hgate, _harr⟩ := laterCollectionReadout_call 0 ((R).get k) c hcol
      let input := CoordinatorRecorderComplementBridge.recorderInput
        (collectionRecordingInput ((R).get k).output.preparation P started weights)
      have hfrozen : CoordinatorRecordingOperation.isFrozen input := by
        have hnot : ¬ (((R).get k).input.time.val + 1 < started.clock.g) :=
          of_decide_eq_false (hclock.symm.trans hen)
        change 0 < P.sigma.val + 1 ∧ ((R).get k).input.time.val + 1 ≥ started.clock.g
        omega
      obtain ⟨_valid, hzero⟩ := collectionRecorder_output_cases input rfl out hrun
      simp only [hfrozen, not_true_eq_false, and_false, false_and, ite_false] at hzero
      have hmarker : c.recordedArm = none := by rw [← hgate, hzero]; rfl
      refine ⟨hm.trans hmarker, ?_⟩
      intro a
      rw [ha a]
      exact RecordedQueueRun.quantizedArrival_eq_zero
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) c a
        (by rw [hmarker]; intro h; cases h)

/-- Every arm's source calendar begins at zero, including an empty terminal suffix. -/
theorem sourceCalendarReplay_origin (a : Fin p.K) :
    sourceCalendarReplay rate rewards C_star C_h z a 0 = (0, 0) := rfl

/-- Conservation holds on every original prefix, including post-overflow prefixes. -/
theorem sourceCalendarReplay_conservation (a : Fin p.K) (h : ℕ) :
    (sourceCalendarReplay rate rewards C_star C_h z a h).1 +
      (sourceCalendarReplay rate rewards C_star C_h z a h).2 =
        RecordedQueueRun.acceptedTotal
          (((physicalRawWord rate W).take h).map fun cell => (cell.1, cell.2 a)) :=
  actualCalendarReplay_conservation rate W a h

/-- The source-bound recurrence at every nonterminal physical date. Enabled
zero arrivals serve backlog; disabled dates preserve both registers. -/
theorem sourceCalendarReplay_recurrence (k : Fin (R).length) (a : Fin p.K) :
    let physical := (W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩
    let before := sourceCalendarReplay rate rewards C_star C_h z a k.val
    sourceCalendarReplay rate rewards C_star C_h z a (k.val + 1) =
      if physical.enabled then
        let service := min (4 * rate.n) (before.2 + physical.arrival a)
        (before.1 + service, before.2 + physical.arrival a - service)
      else before := by
  have hk : k.val < (physicalRawWord rate W).length := by
    simp only [physicalRawWord, List.length_map, actualPhysicalWord_length]
    exact k.isLt
  simpa only [sourceCalendarReplay, actualCalendarReplay, physicalRawWord,
    List.get_eq_getElem, List.getElem_map] using
    physicalReplay_recurrence rate (physicalRawWord rate W) a k.val hk

/-- Explicit source arrival and service update: disabled arrivals and
service are zero, while enabled zero arrivals still serve the old backlog. -/
theorem sourceCalendarReplay_update (k : Fin (R).length) (a : Fin p.K) :
    let physical := (W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩
    let before := sourceCalendarReplay rate rewards C_star C_h z a k.val
    let delta := if physical.enabled then physical.arrival a else 0
    let service := if physical.enabled then min (4 * rate.n) (before.2 + delta) else 0
    sourceCalendarReplay rate rewards C_star C_h z a (k.val + 1) =
      (before.1 + service, before.2 + delta - service) := by
  have h := sourceCalendarReplay_recurrence rate rewards C_star C_h z k a
  dsimp only at h ⊢
  split_ifs at h ⊢ <;> simpa only [Nat.add_zero, Nat.sub_zero] using h

/-- Unique zero-origin source recurrence on every boundary of the whole
physical suffix. The recurrence is never stopped at analytical overflow. -/
theorem sourceCalendarReplay_unique (registers : ℕ → Fin p.K → ℕ × ℕ)
    (hzero : ∀ a, registers 0 a = (0, 0))
    (hstep : ∀ (k : Fin (R).length) a,
      let physical := (W).get ⟨k.val, by rw [actualPhysicalWord_length]; exact k.isLt⟩
      registers (k.val + 1) a = QueueReplay.transition (4 * rate.n)
        (registers k.val a) (physical.enabled, physical.arrival a)) :
    ∀ h a, h ≤ (R).length →
      registers h a = sourceCalendarReplay rate rewards C_star C_h z a h := by
  have hs' : ∀ h (hh : h < (physicalRawWord rate W).length) a,
      registers (h + 1) a = QueueReplay.transition (4 * rate.n) (registers h a)
        (((physicalRawWord rate W).get ⟨h, hh⟩).1, ((physicalRawWord rate W).get ⟨h, hh⟩).2 a) := by
    intro h hh a
    have hi : h < (R).length := by
      simpa only [physicalRawWord, List.length_map, actualPhysicalWord_length] using hh
    simpa only [physicalRawWord, List.get_eq_getElem, List.getElem_map] using hstep ⟨h, hi⟩ a
  intro h a hh
  exact physicalReplay_unique rate (physicalRawWord rate W) registers hzero hs' h a
    (by simpa only [physicalRawWord, List.length_map, actualPhysicalWord_length] using hh)

end CompleteWord

end Bandits.Support.ReferenceCompletePhysicalCalendarQueueTruth

end
