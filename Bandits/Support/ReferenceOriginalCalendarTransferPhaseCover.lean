/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSignedFirstBadCalendar
public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.Tactic

/-!
# Actual stopped transfer phases on the original calendar

This module keeps the original physical suffix and identifies collection,
handover, and release records from their actual selected coordinator
operations. Its analytic endpoint is the literal first-bad date; it does not
stop the physical execution.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceLaterCollectionArrivalReadout
open Bandits.Support.ReferenceCollectionSegmentExtraction
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCalendarTransferPhaseCover

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := BootstrapPrivateRoundStreams.SourceInput p
abbrev Source (p : Parameters) :=
  ReferenceActualLiveEmptySignedRewardCalendar.Source p
abbrev GridRewardTable (p : Parameters) :=
  ActualInitializationPhysicalStep.GridRewardTable p

variable {p : Parameters}
variable (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (z : SourceInput p)

/-- The unchanged, complete physical suffix used by every phase predicate. -/
public def actualRecords :=
  ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h

/-- The physical start coordinate, including the terminal launch sentinel. -/
public def physicalStart :=
  ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h

/-- The actual launch round of the generated initialization input. -/
public def actualLaunchRound :=
  ReferenceCompleteSignedFirstBadCalendar.actualLaunchRound rate rewards C_star C_h z

/-- The literal first decoder-failure or overflow-update date. -/
public def firstBadDate :=
  ReferenceCompleteSignedFirstBadCalendar.firstBadDate rate rewards C_star C_h z

/-- The one-based date of an original physical suffix record. -/
public def recordDate (k : Fin (actualRecords rate rewards C_star C_h z).length) : ℕ :=
  ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time.val + 1

private theorem actualRecord_get_time_nat (n : ℕ)
    (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get ⟨n, hn⟩).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[n]?) htimes
  have hn' : n < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hn
  have hrange := List.getElem?_range'
    (s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (step := 1) hn'
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_eq_getElem hn, hrange] using hget

private theorem actualRecord_get_time
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    ((actualRecords rate rewards C_star C_h z).get ⟨k.val, k.isLt⟩).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
  simpa only [actualRecords] using
    actualRecord_get_time_nat rate rewards C_star C_h z k.val k.isLt

private theorem actualLaunchRound_eq_succ_of_corrected_launch
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = some active) :
    actualLaunchRound rate rewards C_star C_h z =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := by
  have hcross :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
  have hcross' : (ReferenceInitializationRun.output
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedInput] using hcross
  change ReferenceInitializationRun.launchRound
      (ReferenceCompletePhysicalHistory.generatedInput rate z rewards C_star C_h) =
    ReferenceInitializationRun.elapsed p
      (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).completed + 1
  unfold ReferenceInitializationRun.launchRound
  rw [hcross']
  rfl

private theorem actualLaunchRound_eq_sentinel_of_no_launch
    (hno : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none) :
    actualLaunchRound rate rewards C_star C_h z = p.T + 1 := by
  simpa [actualLaunchRound, ReferenceCompleteSignedFirstBadCalendar.actualLaunchRound] using
    ReferenceCompletePhysicalHistory.no_launch_sentinel_round
      rate z rewards C_star C_h hno

/-- Actual option presence for a collection choice, including the cutoff
round and the continuing collection choices from the original dispatcher. -/
public def actualCollectionChoice
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
    ReferenceCollectionSegmentExtraction.choice r.input = some c

/-- The actual selected live operation while the coordinator still has a
missing DOWN confirmation. -/
public def actualHandoverSelection
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ selected : Selection r.input,
    r.output.preparation.coordinator.selection = some selected ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff
        r.input.time ∧
      selected.view.pendingAtChoice.Nonempty

/-- The actual selected live operation after all coordinator DOWN
confirmations are present. The signed reward difference remains unrestricted. -/
public def actualReleaseSelection
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) : Prop :=
  ∃ selected : Selection r.input,
    r.output.preparation.coordinator.selection = some selected ∧
      CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload selected.view.cutoff
        r.input.time ∧
      selected.view.pendingAtChoice = ∅

/-- The inclusive analytic date gate. Physical records after this gate remain
in `actualRecords`. -/
public def retainedByFirstBadDate
    (k : Fin (actualRecords rate rewards C_star C_h z).length) : Prop :=
  actualLaunchRound rate rewards C_star C_h z ≤ recordDate rate rewards C_star C_h z k ∧
    recordDate rate rewards C_star C_h z k ≤ min (firstBadDate rate rewards C_star C_h z) p.T

/-- Collection record indices retained through the inclusive first-bad date. -/
public def collectionPhaseIndices : Finset
    (Fin (actualRecords rate rewards C_star C_h z).length) :=
  Finset.univ.filter fun k => retainedByFirstBadDate rate rewards C_star C_h z k ∧
    actualCollectionChoice rate
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)

/-- Handover record indices retained through the inclusive first-bad date. -/
public def handoverPhaseIndices : Finset
    (Fin (actualRecords rate rewards C_star C_h z).length) :=
  Finset.univ.filter fun k => retainedByFirstBadDate rate rewards C_star C_h z k ∧
    actualHandoverSelection rate
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)

/-- Release record indices retained through the inclusive first-bad date. -/
public def releasePhaseIndices : Finset
    (Fin (actualRecords rate rewards C_star C_h z).length) :=
  Finset.univ.filter fun k => retainedByFirstBadDate rate rewards C_star C_h z k ∧
    actualReleaseSelection rate
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)

/-- The three stopped phase sets on original calendar dates. -/
public def collectionPhaseDates : Finset (Fin p.T) :=
  (collectionPhaseIndices rate rewards C_star C_h z).image fun k =>
    ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time

public def handoverPhaseDates : Finset (Fin p.T) :=
  (handoverPhaseIndices rate rewards C_star C_h z).image fun k =>
    ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time

public def releasePhaseDates : Finset (Fin p.T) :=
  (releasePhaseIndices rate rewards C_star C_h z).image fun k =>
    ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time

/-- The literal source-date interval from the actual launch through the
inclusive first-bad date, clipped only at the physical horizon. -/
public def retainedSuffixDates : Finset (Fin p.T) :=
  Finset.univ.filter fun t =>
    actualLaunchRound rate rewards C_star C_h z ≤ t.val + 1 ∧
      t.val + 1 ≤ min (firstBadDate rate rewards C_star C_h z) p.T

/-- The un-subtracted release diagnostic on the actual whole row, using the
selected payload and that same record's coordinator action. -/
public def releaseRaw (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection r.input) : ℝ :=
  ReleaseRoundKernel.slowReward
      (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t)
      selected.view.payload.slowSet +
    (ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t).val
      (r.actions (ActiveRoundActions.coordinator p.two_le_m))

/-- The signed release charge on the actual whole row, retaining its original
subtraction of the record's exact own-feedback total. -/
public def releaseDelta (t : Fin p.T)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : Selection r.input) : ℝ :=
  releaseRaw rate rewards t r selected - r.totalReward

private theorem mem_collectionPhaseDates_iff (t : Fin p.T) :
    t ∈ collectionPhaseDates rate rewards C_star C_h z ↔
      ∃ k, k ∈ collectionPhaseIndices rate rewards C_star C_h z ∧
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = t := by
  simp [collectionPhaseDates]

private theorem mem_handoverPhaseDates_iff (t : Fin p.T) :
    t ∈ handoverPhaseDates rate rewards C_star C_h z ↔
      ∃ k, k ∈ handoverPhaseIndices rate rewards C_star C_h z ∧
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = t := by
  simp [handoverPhaseDates]

private theorem mem_releasePhaseDates_iff (t : Fin p.T) :
    t ∈ releasePhaseDates rate rewards C_star C_h z ↔
      ∃ k, k ∈ releasePhaseIndices rate rewards C_star C_h z ∧
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = t := by
  simp [releasePhaseDates]

private theorem actual_source_record_lookup
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time z =
      some ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) := by
  let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
  have htime : r.input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
    simpa [r] using actualRecord_get_time rate rewards C_star C_h z k
  have hstart : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ r.input.time.val := by
    rw [htime]
    omega
  have hindex : r.input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k.val := by
    rw [htime]
    omega
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left hstart]
  change (actualRecords rate rewards C_star C_h z)[r.input.time.val -
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]? = some r
  rw [hindex]
  exact List.getElem?_eq_getElem k.isLt

/-- On every retained actual release selection, the accepted signed diagnostic
is attached to its genuine source-calendar entry. The fast term is the actual
coordinator arm, and the subtraction remains signed. -/
theorem actual_release_calendar_diagnostic
    (k : Fin (actualRecords rate rewards C_star C_h z).length)
    (hk : k ∈ releasePhaseIndices rate rewards C_star C_h z) :
    let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
    ∃ selected : Selection r.input,
      r.output.preparation.coordinator.selection = some selected ∧
      (r.input.time,
        ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards
          r.input.time (ReferenceActiveHorizonMeasurability.roundRecordCode r)) ∈
        ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z ∧
      ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards
        r.input.time (ReferenceActiveHorizonMeasurability.roundRecordCode r) =
        some (releaseRaw rate rewards r.input.time r selected,
          r.totalReward, releaseDelta rate rewards r.input.time r selected) := by
  dsimp only
  rcases Finset.mem_filter.mp hk with ⟨_, ⟨_, hrelease⟩⟩
  obtain ⟨selected, hselected, hlive, hempty⟩ := hrelease
  let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
  have hsource := actual_source_record_lookup rate rewards C_star C_h z k
  have hcalendar :=
    ReferenceActualLiveEmptySignedRewardCalendar.actualRecord_calendar_value
      rate rewards C_star C_h z r.input.time r hsource
  let code := ReferenceActiveHorizonMeasurability.roundRecordCode r
  let selectedData := ReferenceLiveDispatchOutputMeasurability.encodeSelection selected
  have hliveCode :
      ReferenceCoordinatorRecorderCallTrace.live code selectedData = true := by
    rw [ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      code selectedData r.input.time rfl]
    exact decide_eq_true hlive
  have hgate : ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyGate code selectedData := by
    exact ⟨hliveCode, hempty⟩
  obtain ⟨_, _, _, _, _, haction, _, _, hobs, _⟩ :=
    ReferenceActualLiveEmptySignedRewardCalendar.actual_live_empty_diagnostic
      rate rewards C_star C_h r.input.time z r hsource selected hselected hgate
  have hcodeAction :=
    (ReferenceActiveHorizonMeasurability.roundRecordCode_front r).2.2.1
  have hraw :
      ReferenceActualLiveEmptySignedRewardCalendar.physicalDiagnostic
          rate rewards r.input.time code selectedData =
        releaseRaw rate rewards r.input.time r selected := by
    dsimp [ReferenceActualLiveEmptySignedRewardCalendar.physicalDiagnostic,
      releaseRaw, selectedData, code,
      ReferenceLiveDispatchOutputMeasurability.encodeSelection]
    rw [hcodeAction, haction]
  refine ⟨selected, hselected, ?_, ?_⟩
  · exact hcalendar
  · simpa only [r, code, selectedData, hraw, releaseDelta] using hobs

/-- Splitting an actual live selection by the coordinator's actual
missing-confirmation set. -/
private theorem actual_live_selection_pending_partition
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (selected : Selection r.input)
    (hselected : r.output.preparation.coordinator.selection = some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff r.input.time) :
    actualHandoverSelection rate r ∨
      actualReleaseSelection rate r := by
  by_cases hpending : selected.view.pendingAtChoice.Nonempty
  · exact Or.inl ⟨selected, hselected, hlive, hpending⟩
  · have hempty : selected.view.pendingAtChoice = ∅ := by
      by_contra hne
      exact hpending (Finset.nonempty_iff_ne_empty.mpr hne)
    exact Or.inr ⟨selected, hselected, hlive, hempty⟩

/-- Handover and release are disjoint because they use the same actual
selection and the same coordinator missing-confirmation set. -/
private theorem actual_handover_release_disjoint
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)} :
    ¬ (actualHandoverSelection rate r ∧
      actualReleaseSelection rate r) := by
  rintro ⟨⟨h, hselH, _, hnonempty⟩, ⟨rel, hselR, _, hempty⟩⟩
  -- Both predicates refer to the unique value of the same actual Option.
  -- Keep the two equality witnesses instead of selecting a second snapshot.
  have hEq : h = rel := by
    have hvalue : some h = some rel := hselH.symm.trans hselR
    exact Option.some.inj hvalue
  subst rel
  simp [hempty] at hnonempty

private theorem actual_collection_choice_not_live
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (choice : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice r.input = some choice)
    (selected : Selection r.input)
    (_hselected : r.output.preparation.coordinator.selection = some selected)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff r.input.time) : False := by
  have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
    rw [r.output_eq]
    rfl
  have hchoiceOfCut :
      ReferenceCollectionSegmentExtraction.choiceOfCut
        r.output.preparation.coordinator = some choice := by
    simpa [ReferenceCollectionSegmentExtraction.choice, hprep,
      _hselected] using hchoice
  cases hcoord : r.output.preparation.coordinator with
  | first outcome =>
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceOfCut
      cases hchoiceOfCut
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinitialized hledger hdomains hclock hpending hno arm =>
          have hmap := congrArg
            (Option.map fun s : Selection r.input => s.view.cutoff) _hselected
          rw [hcoord] at hmap
          have hcut : selected.view.cutoff =
              CoordinatorLiveChoiceRecorderStep.cutoffFromClock
                p dispatched.startResult.clock.u := by
            have hEq : some
                (CoordinatorLiveChoiceRecorderStep.cutoffFromClock
                  p dispatched.startResult.clock.u) = some selected.view.cutoff := by
              simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt] using hmap
            exact (Option.some.inj hEq).symm
          have hlt := hlive.2
          rw [hcut, CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock, hclock] at hlt
          simp [ReferenceActivePhysicalStep.liveInput,
            ReferenceActivePhysicalStep.liveRegistersAt,
            CoordinatorLocalArmChoice.sourceRound] at hlt
      | _ =>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceOfCut
          cases hchoiceOfCut
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary checked =>
          have hcutoff :
              CoordinatorLiveChoiceRecorderStep.cutoffFromClock
                p snapshot.clockStarted.clock.u =
                some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
            rw [snapshot.clockStarted_frame.1]
            change CoordinatorLiveChoiceRecorderStep.cutoffFromClock p clock.u = _
            have hc : clock.u = some cutoff := snapshot.inputsValid.clock_cutoff_eq
            rw [hc]
            rfl
          have hmap := congrArg
            (Option.map fun s : Selection r.input => s.view.cutoff) _hselected
          rw [hcoord] at hmap
          have hcut : selected.view.cutoff =
              some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
            have hEq : some (some (CoordinatorCollectionUpRoundStep.localCutoff cutoff)) =
                some selected.view.cutoff := by
              simpa [ReferenceActivePhysicalStep.DispatchCut.selection,
                ReferenceActivePhysicalStep.selectionAt, hcutoff] using hmap
            exact (Option.some.inj hEq).symm
          have hvalid := core.ledger_valid
          simp only [CoordinatorCollectionLedger.validLedger,
            CoordinatorCollectionLedger.validLedgerCheck, Bool.and_eq_true,
            decide_eq_true_eq] at hvalid
          have hcutoffLe : ledger.cutoff ≤ ledger.cursor := by tauto
          have hcursor := core.ledger_cursor_eq
          change ledger.cursor =
            CoordinatorCollectionUpRoundStep.sourceRound r.input.time at hcursor
          have hledgerCutoff : ledger.cutoff =
              CoordinatorCollectionUpRoundStep.sourceCutoff cutoff := by
            simpa [ReferenceActivePhysicalStep.collectionInput] using core.ledger_cutoff_eq
          have hlt := hlive.2
          rw [hcut, CoordinatorCollectionUpRoundStep.localCutoff_round] at hlt
          have hcutoffTime :
              CoordinatorCollectionUpRoundStep.sourceCutoff cutoff ≤
                CoordinatorCollectionUpRoundStep.sourceRound r.input.time := by
            calc
              CoordinatorCollectionUpRoundStep.sourceCutoff cutoff = ledger.cutoff :=
                hledgerCutoff.symm
              _ ≤ ledger.cursor := hcutoffLe
              _ = CoordinatorCollectionUpRoundStep.sourceRound r.input.time := hcursor
          dsimp [CoordinatorCollectionUpRoundStep.sourceRound,
            CoordinatorLocalArmChoice.sourceRound] at hlt hcutoffTime
          omega
      | _ =>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceOfCut
          cases hchoiceOfCut
  | invalidCollectionCutoff =>
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceOfCut
      cases hchoiceOfCut
  | dagger =>
      simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceOfCut
      cases hchoiceOfCut

theorem actual_suffix_collection_handover_disjoint
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    ¬ (actualCollectionChoice rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) ∧
      actualHandoverSelection rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)) := by
  rintro ⟨⟨choice, hchoice⟩, ⟨selected, hselected, hlive, _⟩⟩
  exact actual_collection_choice_not_live rate choice hchoice selected hselected hlive

theorem actual_suffix_collection_release_disjoint
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    ¬ (actualCollectionChoice rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) ∧
      actualReleaseSelection rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)) := by
  rintro ⟨⟨choice, hchoice⟩, ⟨selected, hselected, hlive, _⟩⟩
  exact actual_collection_choice_not_live rate choice hchoice selected hselected hlive

private theorem actual_suffix_record_index_injective
    (i j : Fin (actualRecords rate rewards C_star C_h z).length)
    (htime : ((actualRecords rate rewards C_star C_h z)[i.val]'i.isLt).input.time =
      ((actualRecords rate rewards C_star C_h z)[j.val]'j.isLt).input.time) :
    i = j := by
  have htimeVal := congrArg Fin.val htime
  have hiTime :
      ((actualRecords rate rewards C_star C_h z)[i.val]'i.isLt).input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + i.val := by
    simpa using actualRecord_get_time rate rewards C_star C_h z i
  have hjTime :
      ((actualRecords rate rewards C_star C_h z)[j.val]'j.isLt).input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + j.val := by
    simpa using actualRecord_get_time rate rewards C_star C_h z j
  rw [hiTime, hjTime] at htimeVal
  apply Fin.ext
  omega

private theorem actual_connected_first_record_state
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hconnected : ReferenceActivePhysicalHorizon.Connected initial records final)
    (hnonempty : records ≠ []) :
    (records[0]'(by
      cases records with
      | nil => exact (hnonempty rfl).elim
      | cons _ _ => simp)).input.state = initial := by
  cases records with
  | nil => contradiction
  | cons head tail =>
      simpa only [ReferenceActivePhysicalHorizon.Connected, List.getElem_cons_zero]
        using hconnected.1

/-- Pairwise disjointness of the actual stopped date sets. Each phase is
recovered from its original record, whose calendar timestamp is injective. -/
theorem stopped_phase_dates_pairwise_disjoint :
    Disjoint (collectionPhaseDates rate rewards C_star C_h z)
        (handoverPhaseDates rate rewards C_star C_h z) ∧
      Disjoint (collectionPhaseDates rate rewards C_star C_h z)
        (releasePhaseDates rate rewards C_star C_h z) ∧
      Disjoint (handoverPhaseDates rate rewards C_star C_h z)
        (releasePhaseDates rate rewards C_star C_h z) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro t htC htH
    obtain ⟨i, hi, hit⟩ := (mem_collectionPhaseDates_iff rate rewards C_star C_h z t).mp htC
    obtain ⟨j, hj, hjt⟩ := (mem_handoverPhaseDates_iff rate rewards C_star C_h z t).mp htH
    have hij := actual_suffix_record_index_injective rate rewards C_star C_h z i j
      (hit.trans hjt.symm)
    subst j
    obtain ⟨_, ⟨_, hci⟩⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, ⟨_, hhi⟩⟩ := Finset.mem_filter.mp hj
    exact actual_suffix_collection_handover_disjoint rate rewards C_star C_h z i
      ⟨hci, hhi⟩
  · apply Finset.disjoint_left.mpr
    intro t htC htR
    obtain ⟨i, hi, hit⟩ := (mem_collectionPhaseDates_iff rate rewards C_star C_h z t).mp htC
    obtain ⟨j, hj, hjt⟩ := (mem_releasePhaseDates_iff rate rewards C_star C_h z t).mp htR
    have hij := actual_suffix_record_index_injective rate rewards C_star C_h z i j
      (hit.trans hjt.symm)
    subst j
    obtain ⟨_, ⟨_, hci⟩⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, ⟨_, hri⟩⟩ := Finset.mem_filter.mp hj
    exact actual_suffix_collection_release_disjoint rate rewards C_star C_h z i
      ⟨hci, hri⟩
  · apply Finset.disjoint_left.mpr
    intro t htH htR
    obtain ⟨i, hi, hit⟩ := (mem_handoverPhaseDates_iff rate rewards C_star C_h z t).mp htH
    obtain ⟨j, hj, hjt⟩ := (mem_releasePhaseDates_iff rate rewards C_star C_h z t).mp htR
    have hij := actual_suffix_record_index_injective rate rewards C_star C_h z i j
      (hit.trans hjt.symm)
    subst j
    obtain ⟨_, ⟨_, hhi⟩⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, ⟨_, hri⟩⟩ := Finset.mem_filter.mp hj
    exact actual_handover_release_disjoint rate
      (r := (actualRecords rate rewards C_star C_h z)[i.val]'i.isLt) ⟨hhi, hri⟩

private theorem actual_collection_readout_implies_choice
    (k : Fin (actualRecords rate rewards C_star C_h z).length)
    (d : RecordedQueueRun.RoundInput p.K)
    (hd : laterCollectionReadout 0
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) = some d) :
    actualCollectionChoice rate
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) := by
  let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
  have hselected : r.output.preparation.coordinator.selection ≠ none := by
    exact ((ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 k).2.1
  have hprep : (prepare r.input).coordinator = r.output.preparation.coordinator := by
    rw [r.output_eq]
    rfl
  have hbranch := (laterCollectionReadout_domain 0 r).mp
    (Option.isSome_iff_exists.mpr ⟨d, hd⟩)
  have hchoiceEq :
      ReferenceCollectionSegmentExtraction.choice r.input =
        ReferenceCollectionSegmentExtraction.choiceOfCut r.output.preparation.coordinator := by
    simp [ReferenceCollectionSegmentExtraction.choice, hprep, hselected]
  have hsome :
      (ReferenceCollectionSegmentExtraction.choiceOfCut
        r.output.preparation.coordinator).isSome = true := by
    cases hcoord : r.output.preparation.coordinator with
    | first outcome => cases outcome <;> simp [hcoord] at hbranch
    | live registers owned base outcome =>
        cases outcome <;> simp [hcoord, ReferenceCollectionSegmentExtraction.choiceOfCut]
          at hbranch ⊢
    | collection payload ledger clock cutoff outcome =>
        cases outcome <;> simp [hcoord, ReferenceCollectionSegmentExtraction.choiceOfCut]
          at hbranch ⊢
    | invalidCollectionCutoff => simp [hcoord] at hbranch
    | dagger => simp [hcoord] at hbranch
  have hchoice :
      (ReferenceCollectionSegmentExtraction.choice r.input).isSome = true := by
    rw [hchoiceEq]
    exact hsome
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hchoice
  exact ⟨c, hc⟩

/-- Every actual complete-suffix record is sourced by the actual collection
choice or by the actual selected live operation, split using the coordinator's
missing-confirmation set. This starts from complete original-calendar phase
exhaustion; no phase predicate is supplied as a hypothesis. -/
theorem actual_suffix_phase_availability
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    actualCollectionChoice rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) ∨
      actualHandoverSelection rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) ∨
      actualReleaseSelection rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) := by
  obtain ⟨_, hphase⟩ :=
    ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
      rate rewards C_star C_h z k
  rcases hphase with hlive | ⟨d, hd⟩
  · obtain ⟨selected, hselected, _, hlive, _⟩ := hlive
    exact Or.inr (actual_live_selection_pending_partition rate selected hselected hlive)
  · exact Or.inl (actual_collection_readout_implies_choice
      rate rewards C_star C_h z k d hd)

/-- The actual first postlaunch record starts the initial handover, while a
missing launch or a launch at `T` has no physical suffix record. This uses
the corrected launch, its actual first-live seed, and the connected original
suffix; the initial pending set is the producer's `univ`. -/
theorem actual_initial_suffix_phase :
    (ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h = none ∧
      actualRecords rate rewards C_star C_h z = [] ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) ∨
    (∃ active : ReferenceActivePhysicalStep.State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some active ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T ∧
      actualRecords rate rewards C_star C_h z = []) ∨
    (∃ active : ReferenceActivePhysicalStep.State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        some active ∧
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < p.T ∧
      ∃ k : Fin (actualRecords rate rewards C_star C_h z).length,
        k.val = 0 ∧
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ∧
        actualHandoverSelection rate
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) ∧
        ¬ actualCollectionChoice rate
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)) := by
  by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none
  · left
    exact ⟨hnone, by simp [actualRecords, ReferenceCompletePhysicalHistory.completeSuffixRecords,
      hnone],
      ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hnone⟩
  · obtain ⟨active, hlaunch'⟩ := Option.ne_none_iff_exists.mp hnone
    have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = some active := hlaunch'.symm
    have hlength := ReferenceCompletePhysicalHistory.completeSuffixRecords_length
      rate z rewards C_star C_h
    by_cases hterminal :
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T
    · right
      left
      refine ⟨active, hlaunch, hterminal, ?_⟩
      apply List.eq_nil_of_length_eq_zero
      rw [actualRecords, hlength, hterminal]
      simp
    · right
      right
      have hstart : ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h < p.T := by
        have hle := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h
        omega
      refine ⟨active, hlaunch, hstart, ?_⟩
      have hlenPositive : 0 < (actualRecords rate rewards C_star C_h z).length := by
        rw [actualRecords, hlength]
        omega
      let k : Fin (actualRecords rate rewards C_star C_h z).length := ⟨0, hlenPositive⟩
      have hcross :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate z rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate z rewards C_star C_h hcross
      have hlaunchSeed :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate z rewards C_star C_h hcross
      have hactive : active =
          ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hcross :=
        Option.some.inj (hlaunch.symm.trans hlaunchSeed)
      let activeRun := ReferenceActivePhysicalHorizon.run active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h active hlaunch)
      have hconnected :=
        ReferenceCompletePhysicalHistory.completeSuffix_connected_on_launch
          rate z rewards C_star C_h active hlaunch
      have hconnected' : ReferenceActivePhysicalHorizon.Connected active
          (actualRecords rate rewards C_star C_h z) activeRun.finalState := by
        simpa [actualRecords, activeRun] using hconnected
      have hrecord0State :
          ((actualRecords rate rewards C_star C_h z)[0]'(by omega)).input.state = active :=
        actual_connected_first_record_state rate
          (actualRecords rate rewards C_star C_h z) hconnected'
          (by intro hnil; simp [hnil] at hlenPositive)
      let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
      have hstate : r.input.state = active := by
        simpa [r, k] using hrecord0State
      have hfirst : r.input.state.coordinator = .first := by
        rw [hstate, hactive]
        exact seed.coordinatorFirst
      have hselected : r.output.preparation.coordinator.selection =
          some (ReferenceFirstDispatchMeasurability.firstSelectionAt r.input) := by
        have hprepare : r.output.preparation = prepare r.input := by
          rw [r.output_eq]
          rfl
        rw [hprepare]
        exact ReferenceFirstDispatchMeasurability.dispatch_first_selection r.input hfirst
      have hlive : CoordinatorLocalArmChoice.assignmentIsLive
          (ReferenceFirstDispatchMeasurability.firstSelectionAt r.input).view.payload
          (ReferenceFirstDispatchMeasurability.firstSelectionAt r.input).view.cutoff
          r.input.time := by
        simp [ReferenceFirstDispatchMeasurability.firstSelectionAt,
          ReferenceFirstDispatchMeasurability.firstChoiceViewAt,
          ReferenceFirstDispatchMeasurability.firstChoiceViewForKey,
          ReferenceFirstDispatchMeasurability.firstChoiceKeyAt,
          ReferenceFirstDispatchMeasurability.firstPayloadAt,
          CoordinatorLocalArmChoice.assignmentIsLive,
          CoordinatorLocalArmChoice.assignmentStart,
          CoordinatorLocalArmChoice.sourceRound,
          CoordinatorLocalArmChoice.cutoffRound]
      have hpending :
          (ReferenceFirstDispatchMeasurability.firstSelectionAt r.input).view.pendingAtChoice.Nonempty := by
        have hset :
            (ReferenceFirstDispatchMeasurability.firstSelectionAt r.input).view.pendingAtChoice =
              Finset.univ := by
          simp [ReferenceFirstDispatchMeasurability.firstSelectionAt,
            ReferenceFirstDispatchMeasurability.firstChoiceViewAt,
            ReferenceFirstDispatchMeasurability.firstChoiceViewForKey]
        rw [hset]
        have hm := p.two_le_m
        have hpositive : 0 < p.m - 1 := by omega
        exact ⟨⟨0, hpositive⟩, Finset.mem_univ _⟩
      have hhandover : actualHandoverSelection rate r :=
        ⟨ReferenceFirstDispatchMeasurability.firstSelectionAt r.input,
          hselected, hlive, hpending⟩
      have htime : r.input.time.val =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        simpa [r, k] using actualRecord_get_time rate rewards C_star C_h z k
      have hnotCollection : ¬ actualCollectionChoice rate r := by
        intro hcollection
        exact actual_suffix_collection_handover_disjoint rate rewards C_star C_h z k
          ⟨hcollection, hhandover⟩
      exact ⟨k, rfl, htime, hhandover, hnotCollection⟩

/-- Handover and release are disjoint on every record of the same actual
complete suffix. -/
theorem actual_suffix_handover_release_disjoint
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    ¬ (actualHandoverSelection rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) ∧
      actualReleaseSelection rate
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)) :=
  actual_handover_release_disjoint rate
    (r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)

/-- The actual collection, handover, and release options cover exactly the
retained original dates. A missing launch and a terminal launch are both
handled by the actual launch sentinel and leave this date set empty. -/
theorem stopped_phase_dates_cover :
    collectionPhaseDates rate rewards C_star C_h z ∪
        handoverPhaseDates rate rewards C_star C_h z ∪
        releasePhaseDates rate rewards C_star C_h z =
      retainedSuffixDates rate rewards C_star C_h z := by
  classical
  apply Finset.ext
  intro t
  simp only [Finset.mem_union]
  rw [mem_collectionPhaseDates_iff, mem_handoverPhaseDates_iff,
    mem_releasePhaseDates_iff]
  simp only [retainedSuffixDates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hphase
    rcases hphase with hCH | hrelease
    · rcases hCH with hcollection | hhandover
      · rcases hcollection with ⟨k, hk, htime⟩
        rcases Finset.mem_filter.mp hk with ⟨_, ⟨hretained, _hphase⟩⟩
        have htimeVal := congrArg Fin.val htime
        dsimp only [retainedByFirstBadDate, recordDate] at hretained
        rw [htimeVal] at hretained
        exact hretained
      · rcases hhandover with ⟨k, hk, htime⟩
        rcases Finset.mem_filter.mp hk with ⟨_, ⟨hretained, _hphase⟩⟩
        have htimeVal := congrArg Fin.val htime
        dsimp only [retainedByFirstBadDate, recordDate] at hretained
        rw [htimeVal] at hretained
        exact hretained
    · rcases hrelease with ⟨k, hk, htime⟩
      rcases Finset.mem_filter.mp hk with ⟨_, ⟨hretained, _hphase⟩⟩
      have htimeVal := congrArg Fin.val htime
      dsimp only [retainedByFirstBadDate, recordDate] at hretained
      rw [htimeVal] at hretained
      exact hretained
  · intro hdate
    cases hlaunch :
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h with
    | none =>
      have hL := actualLaunchRound_eq_sentinel_of_no_launch
        rate rewards C_star C_h z hlaunch
      omega
    | some active =>
      have hL := actualLaunchRound_eq_succ_of_corrected_launch
        rate rewards C_star C_h z active hlaunch
      have hL' : actualLaunchRound rate rewards C_star C_h z =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + 1 := hL
      rw [hL'] at hdate
      have hstart : ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h ≤ t.val := by
        omega
      have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h <
          (actualRecords rate rewards C_star C_h z).length := by
        rw [actualRecords, ReferenceCompletePhysicalHistory.completeSuffixRecords_length]
        omega
      let k : Fin (actualRecords rate rewards C_star C_h z).length :=
        ⟨t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
          hindex⟩
      have htimeVal :
          ((actualRecords rate rewards C_star C_h z).get ⟨k.val, k.isLt⟩).input.time.val = t.val := by
        rw [actualRecord_get_time rate rewards C_star C_h z k]
        dsimp [k]
        omega
      have htime : ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = t := by
        apply Fin.ext
        change ((actualRecords rate rewards C_star C_h z).get ⟨k.val, k.isLt⟩).input.time.val = t.val
        exact htimeVal
      have hretained : retainedByFirstBadDate rate rewards C_star C_h z k := by
        dsimp only [retainedByFirstBadDate, recordDate]
        rw [hL', congrArg Fin.val htime]
        exact hdate
      rcases actual_suffix_phase_availability rate rewards C_star C_h z k with
        hcollection | hhandover | hrelease
      · left
        left
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hretained, hcollection⟩⟩,
          htime⟩
      · left
        right
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hretained, hhandover⟩⟩,
          htime⟩
      · right
        refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hretained, hrelease⟩⟩,
          htime⟩

/-- The observation read directly from the original source lookup at a date.
An absent physical record stays absent; no synthetic round record is inserted. -/
public def actualDateObservation (t : Fin p.T) : Option (ℝ × ℝ × ℝ) :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => none
  | some r => ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards t
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)

/-- Extract the signed third coordinate of a present actual observation. The
zero branch is only the literal `Option` extraction on absent dates. -/
public def actualDateSignedDelta (t : Fin p.T) : ℝ :=
  match actualDateObservation rate rewards C_star C_h z t with
  | none => 0
  | some (_, _, delta) => delta

/-- The date charge read from the actual physical observation: capped support
on an absent observation, and its signed diagnostic when present. -/
public def actualDateCalendarCharge (t : Fin p.T) : ℝ :=
  match actualDateObservation rate rewards C_star C_h z t with
  | none => ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t
  | some (_, _, delta) => delta

/-- Original physical calendar dates, projected from the accepted complete
branch calendar. Their order is retained by the underlying list. -/
public def actualCalendarDateProjection : Finset (Fin p.T) :=
  ((ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z).map
    Prod.fst).toFinset

private theorem actual_date_observation_at_record
    (k : Fin (actualRecords rate rewards C_star C_h z).length) :
    actualDateObservation rate rewards C_star C_h z
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time =
      ReferenceActualLiveEmptySignedRewardCalendar.observation rate rewards
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time
        (ReferenceActiveHorizonMeasurability.roundRecordCode
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt)) := by
  have hlookup := actual_source_record_lookup rate rewards C_star C_h z k
  simp only [actualDateObservation, hlookup]

private theorem actual_date_observation_none_of_collection
    (k : Fin (actualRecords rate rewards C_star C_h z).length)
    (hk : k ∈ collectionPhaseIndices rate rewards C_star C_h z) :
    actualDateObservation rate rewards C_star C_h z
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = none := by
  let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
  have hlookup := actual_source_record_lookup rate rewards C_star C_h z k
  have hphase : actualCollectionChoice rate r := by
    exact (Finset.mem_filter.mp hk).2.2
  rcases hphase with ⟨choice, hchoice⟩
  have hnone := (ReferenceActualLiveEmptySignedRewardCalendar.actual_observation_eq_none_iff
    rate rewards C_star C_h r.input.time z r (by simpa [r] using hlookup)).2.2
  rw [actual_date_observation_at_record rate rewards C_star C_h z k]
  apply hnone
  right
  intro selected hselected hgate
  have hliveCode :
      ReferenceCoordinatorRecorderCallTrace.live
          (ReferenceActiveHorizonMeasurability.roundRecordCode r)
          (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected) = true :=
    hgate.1
  have hlive : CoordinatorLocalArmChoice.assignmentIsLive selected.view.payload
      selected.view.cutoff r.input.time := by
    rw [ReferenceCoordinatorRecorderCallTrace.live_eq_assignmentIsLive
      (ReferenceActiveHorizonMeasurability.roundRecordCode r)
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)
      r.input.time rfl] at hliveCode
    simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using
      (of_decide_eq_true hliveCode)
  exact actual_collection_choice_not_live rate choice hchoice selected hselected hlive

private theorem actual_date_observation_none_of_handover
    (k : Fin (actualRecords rate rewards C_star C_h z).length)
    (hk : k ∈ handoverPhaseIndices rate rewards C_star C_h z) :
    actualDateObservation rate rewards C_star C_h z
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = none := by
  let r := (actualRecords rate rewards C_star C_h z)[k.val]'k.isLt
  have hlookup := actual_source_record_lookup rate rewards C_star C_h z k
  have hphase : actualHandoverSelection rate r := (Finset.mem_filter.mp hk).2.2
  rcases hphase with ⟨selected, hselected, _hlive, hpending⟩
  have hnone := (ReferenceActualLiveEmptySignedRewardCalendar.actual_observation_eq_none_iff
    rate rewards C_star C_h r.input.time z r (by simpa [r] using hlookup)).2.2
  rw [actual_date_observation_at_record rate rewards C_star C_h z k]
  apply hnone
  right
  intro other hother hgate
  have hEq : selected = other := by
    have hval : some selected = some other := hselected.symm.trans hother
    exact Option.some.inj hval
  subst other
  have hempty : selected.view.pendingAtChoice = ∅ := by
    simpa [ReferenceLiveDispatchOutputMeasurability.encodeSelection] using hgate.2
  exact (Finset.nonempty_iff_ne_empty.mp hpending) hempty

private theorem actual_date_observation_present_of_release
    (k : Fin (actualRecords rate rewards C_star C_h z).length)
    (hk : k ∈ releasePhaseIndices rate rewards C_star C_h z) :
    ∃ selected : Selection
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input,
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).output.preparation.coordinator.selection =
        some selected ∧
      actualDateObservation rate rewards C_star C_h z
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time =
        some (releaseRaw rate rewards
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) selected,
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).totalReward,
          releaseDelta rate rewards
            ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time
            ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) selected) := by
  obtain ⟨selected, hselected, _hcalendar, hobs⟩ :=
    actual_release_calendar_diagnostic rate rewards C_star C_h z k hk
  refine ⟨selected, hselected, ?_⟩
  rw [actual_date_observation_at_record rate rewards C_star C_h z k]
  exact hobs

/-- The actual observation is absent exactly on retained collection and
handover dates, and is present exactly on retained release dates. -/
theorem retained_actual_observation_phase_characterization
    (t : Fin p.T) (ht : t ∈ retainedSuffixDates rate rewards C_star C_h z) :
    (actualDateObservation rate rewards C_star C_h z t = none ↔
        t ∈ collectionPhaseDates rate rewards C_star C_h z ∪
          handoverPhaseDates rate rewards C_star C_h z) ∧
      ((∃ e y delta, actualDateObservation rate rewards C_star C_h z t =
          some (e, y, delta)) ↔
        t ∈ releasePhaseDates rate rewards C_star C_h z) := by
  have hcover := stopped_phase_dates_cover rate rewards C_star C_h z
  have hphase : t ∈
      (collectionPhaseDates rate rewards C_star C_h z ∪
        handoverPhaseDates rate rewards C_star C_h z) ∪
        releasePhaseDates rate rewards C_star C_h z := by
    rw [hcover]
    exact ht
  have hnoneIff :
      actualDateObservation rate rewards C_star C_h z t = none ↔
        t ∈ collectionPhaseDates rate rewards C_star C_h z ∪
          handoverPhaseDates rate rewards C_star C_h z := by
    constructor
    · intro hnone
      rcases Finset.mem_union.mp hphase with hcollectionHandover | hrelease
      · exact hcollectionHandover
      · obtain ⟨k, hk, htime⟩ :=
          (mem_releasePhaseDates_iff rate rewards C_star C_h z t).mp hrelease
        obtain ⟨_selected, _hselected, hobs⟩ :=
          actual_date_observation_present_of_release rate rewards C_star C_h z k hk
        rw [← htime] at hnone
        rw [hobs] at hnone
        cases hnone
    · intro hcollectionHandover
      rcases Finset.mem_union.mp hcollectionHandover with hcollection | hhandover
      · obtain ⟨k, hk, htime⟩ :=
          (mem_collectionPhaseDates_iff rate rewards C_star C_h z t).mp hcollection
        have hnone := actual_date_observation_none_of_collection rate rewards C_star C_h z k hk
        simpa [← htime] using hnone
      · obtain ⟨k, hk, htime⟩ :=
          (mem_handoverPhaseDates_iff rate rewards C_star C_h z t).mp hhandover
        have hnone := actual_date_observation_none_of_handover rate rewards C_star C_h z k hk
        simpa [← htime] using hnone
  have hsomeIff :
      (∃ e y delta, actualDateObservation rate rewards C_star C_h z t = some (e, y, delta)) ↔
        t ∈ releasePhaseDates rate rewards C_star C_h z := by
    constructor
    · rintro ⟨e, y, delta, hsome⟩
      rcases Finset.mem_union.mp hphase with hcollectionHandover | hrelease
      · have hnone := hnoneIff.mpr hcollectionHandover
        rw [hnone] at hsome
        cases hsome
      · exact hrelease
    · intro hrelease
      obtain ⟨k, hk, htime⟩ :=
        (mem_releasePhaseDates_iff rate rewards C_star C_h z t).mp hrelease
      obtain ⟨selected, _hselected, hobs⟩ :=
        actual_date_observation_present_of_release rate rewards C_star C_h z k hk
      refine ⟨releaseRaw rate rewards t
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) selected,
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).totalReward,
        releaseDelta rate rewards t
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) selected, ?_⟩
      simpa [← htime] using hobs
  exact ⟨hnoneIff, hsomeIff⟩

/-- On a release date the extracted signed third coordinate is the original
record's actual slow-set plus coordinator-arm reward minus its own feedback. -/
theorem actual_release_date_signed_diagnostic
    (t : Fin p.T) (ht : t ∈ releasePhaseDates rate rewards C_star C_h z) :
    ∃ k : Fin (actualRecords rate rewards C_star C_h z).length,
      k ∈ releasePhaseIndices rate rewards C_star C_h z ∧
      ∃ selected : Selection
          ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input,
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).output.preparation.coordinator.selection =
          some selected ∧
        ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = t ∧
        actualDateSignedDelta rate rewards C_star C_h z t =
          releaseDelta rate rewards t
            ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt) selected ∧
        (t, actualDateObservation rate rewards C_star C_h z t) ∈
          ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z := by
  obtain ⟨k, hk, htime⟩ := (mem_releasePhaseDates_iff rate rewards C_star C_h z t).mp ht
  obtain ⟨selected, hselected, hcalendar, hobs⟩ :=
    actual_release_calendar_diagnostic rate rewards C_star C_h z k
      hk
  have htime' :
      ((actualRecords rate rewards C_star C_h z)[k.val]'k.isLt).input.time = t := htime
  refine ⟨k, hk, selected, hselected, htime', ?_, ?_⟩
  · rw [← htime']
    simp [actualDateSignedDelta, actual_date_observation_at_record, hobs]
  · rw [← htime']
    rw [actual_date_observation_at_record rate rewards C_star C_h z k]
    exact hcalendar

/-- The physical calendar has one entry per suffix date, with the exact
projected date list from its original complete-branch records. -/
theorem actual_calendar_dates_nodup :
    ((ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z).map
      Prod.fst).Nodup := by
  apply List.Nodup.of_map Fin.val
  have htimes :
      ((ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z).map
        Prod.fst).map Fin.val =
        List.range'
          (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
          (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) 1 := by
    simpa only [List.map_map, Function.comp_def] using
      (ReferenceActualLiveEmptySignedRewardCalendar.calendar_times
        rate rewards C_star C_h z)
  rw [htimes]
  exact List.nodup_range'

/-- The set projection of the physical calendar is exactly its original
complete physical suffix. -/
theorem actual_calendar_date_projection_iff (t : Fin p.T) :
    t ∈ actualCalendarDateProjection rate rewards C_star C_h z ↔
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val := by
  constructor
  · intro ht
    have hmem : t ∈
        (ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z).map
          Prod.fst := List.mem_toFinset.mp ht
    have hnat : t.val ∈
        (ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z).map
          (fun entry => entry.1.val) := by
      apply List.mem_map.mpr
      rcases List.mem_map.mp hmem with ⟨entry, he, hentry⟩
      exact ⟨entry, he, congrArg Fin.val hentry⟩
    rw [ReferenceActualLiveEmptySignedRewardCalendar.calendar_times] at hnat
    exact List.left_le_of_mem_range' hnat
  · intro ht
    have hstart := ReferenceCompletePhysicalHistory.physicalStart_le_T
      rate z rewards C_star C_h
    have hnat : t.val ∈ List.range'
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) 1 := by
      rw [List.mem_range'_1]
      omega
    have htimes := ReferenceActualLiveEmptySignedRewardCalendar.calendar_times
      rate rewards C_star C_h z
    have hmem : t.val ∈
        (ReferenceActualLiveEmptySignedRewardCalendar.calendar rate rewards C_star C_h z).map
          (fun entry => entry.1.val) := by
      rw [htimes]
      exact hnat
    rcases List.mem_map.mp hmem with ⟨entry, he, hentry⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨entry, he, Fin.ext hentry⟩

/-- The analytic retained dates are exactly the original physical calendar
projection restricted by launch and the inclusive first-bad endpoint. -/
theorem retained_suffix_dates_eq_calendar_projection :
    retainedSuffixDates rate rewards C_star C_h z =
      (actualCalendarDateProjection rate rewards C_star C_h z).filter
        (fun t => actualLaunchRound rate rewards C_star C_h z ≤ t.val + 1 ∧
          t.val + 1 ≤ min (firstBadDate rate rewards C_star C_h z) p.T) := by
  classical
  apply Finset.ext
  intro t
  constructor
  · intro ht
    have hretained := Finset.mem_filter.mp ht |>.2
    have hproject : t ∈ actualCalendarDateProjection rate rewards C_star C_h z := by
      cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h with
      | none =>
          have hL := actualLaunchRound_eq_sentinel_of_no_launch
            rate rewards C_star C_h z hlaunch
          have hT := hretained.2
          omega
      | some active =>
          have hL := actualLaunchRound_eq_succ_of_corrected_launch
            rate rewards C_star C_h z active hlaunch
          apply (actual_calendar_date_projection_iff rate rewards C_star C_h z t).2
          omega
    exact Finset.mem_filter.mpr ⟨hproject, hretained⟩
  · intro ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ht).2⟩

/-- The signed branch charge over the actual physical calendar projection is
the capped collection/handover charge plus the signed release diagnostic. -/
theorem actual_calendar_projection_signed_sum_eq_phase_sum :
    (∑ t ∈ (actualCalendarDateProjection rate rewards C_star C_h z).filter
        (fun t => actualLaunchRound rate rewards C_star C_h z ≤ t.val + 1 ∧
          t.val + 1 ≤ min (firstBadDate rate rewards C_star C_h z) p.T),
      actualDateCalendarCharge rate rewards C_star C_h z t) =
      (∑ t ∈ collectionPhaseDates rate rewards C_star C_h z ∪
        handoverPhaseDates rate rewards C_star C_h z,
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t) +
      ∑ t ∈ releasePhaseDates rate rewards C_star C_h z,
        actualDateSignedDelta rate rewards C_star C_h z t := by
  rw [← retained_suffix_dates_eq_calendar_projection rate rewards C_star C_h z]
  classical
  have hdisjoint := (stopped_phase_dates_pairwise_disjoint rate rewards C_star C_h z).2.2
  have hCHR : Disjoint
      (collectionPhaseDates rate rewards C_star C_h z ∪
        handoverPhaseDates rate rewards C_star C_h z)
      (releasePhaseDates rate rewards C_star C_h z) := by
    exact Finset.disjoint_union_left.mpr ⟨
      (stopped_phase_dates_pairwise_disjoint rate rewards C_star C_h z).2.1, hdisjoint⟩
  rw [← stopped_phase_dates_cover rate rewards C_star C_h z,
    Finset.sum_union hCHR]
  have hCHnone (t : Fin p.T) (ht : t ∈
      collectionPhaseDates rate rewards C_star C_h z ∪
        handoverPhaseDates rate rewards C_star C_h z) :
      actualDateCalendarCharge rate rewards C_star C_h z t =
        ReferenceActualLiveEmptySignedRewardCalendar.liveEmptyCap rewards t := by
    have hret : t ∈ retainedSuffixDates rate rewards C_star C_h z := by
      rw [← stopped_phase_dates_cover rate rewards C_star C_h z]
      exact Finset.mem_union.mpr (Or.inl ht)
    have hnone := (retained_actual_observation_phase_characterization
      (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
      (z := z) t hret).1.2 ht
    simp [actualDateCalendarCharge, hnone]
  have hrelease (t : Fin p.T) (ht : t ∈ releasePhaseDates rate rewards C_star C_h z) :
      actualDateCalendarCharge rate rewards C_star C_h z t =
        actualDateSignedDelta rate rewards C_star C_h z t := by
    have hret : t ∈ retainedSuffixDates rate rewards C_star C_h z := by
      rw [← stopped_phase_dates_cover rate rewards C_star C_h z]
      exact Finset.mem_union.mpr (Or.inr ht)
    obtain ⟨e, y, delta, hobs⟩ :=
      (retained_actual_observation_phase_characterization
        (rate := rate) (rewards := rewards) (C_star := C_star) (C_h := C_h)
        (z := z) t hret).2.2 ht
    simp [actualDateCalendarCharge, actualDateSignedDelta, hobs]
  rw [Finset.sum_congr rfl hCHnone, Finset.sum_congr rfl hrelease]

end Bandits.Support.ReferenceOriginalCalendarTransferPhaseCover

end
