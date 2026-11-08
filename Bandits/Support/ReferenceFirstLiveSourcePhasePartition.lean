/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveCalendarPrefixReadout
public import Bandits.Support.ReferenceFirstLiveEmptyPendingMarkerLaw
public import Bandits.Support.ReferenceFirstLiveBranchIntegralTransport

import Mathlib.Data.List.TakeWhile
import Mathlib.Tactic.FinCases

/-!
# Original first-live source phases and empty-image transport

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:145-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-104`.

The images below retain the original source, all rows, private arrays and J.
The measures are inherited and unnormalized, including zero strata. These
internal results are intended for actual first-live calendar integrated drift
and exponential estimates after the empty numerical and accepted-moment
producers. They establish no manuscript filtration or conditional law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveSourcePhasePartition

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "i0" => ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t s hs
local notation "Z" => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h t i0
local notation "muZ" => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h t i0
local notation "ret" => ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
  rate rewards C_star C_h q t s hs control0
local notation "Be" => ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty
  rate rewards C_star C_h q t s hs control0
local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "muE" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
  rate rewards C_star C_h q t s hs control0
local notation "EZ" => Set.ofPred (fun z : Z => Be (ret z))
local notation "n" => t.val - s

include control0 in
private theorem measurableSet_sourceStratum : MeasurableSet
    (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0) :=
  ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent
    rate rewards C_star C_h t control0 i0

private theorem roundInput_ext
    {left right : ReferenceActivePhysicalStep.RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  simp_all

private theorem run_finalState_congr
    (left right : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (ConstructorDimensions.M p))
    (start otherStart count : ℕ)
    (hspan : start + count ≤ p.T) (hspan' : otherStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart left start)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart right otherStart)
    (hi : left = right) (hr : rows = otherRows)
    (hj : selected = otherSelected) (ht : start = otherStart) :
    (ReferenceActivePhysicalHorizon.run left rows selected rewards start count hspan hmode).finalState =
      (ReferenceActivePhysicalHorizon.run right otherRows otherSelected rewards otherStart count
        hspan' hmode').finalState := by
  cases hi
  cases hr
  cases hj
  cases ht
  rfl

private theorem run_records_congr
    (left right : ReferenceActivePhysicalStep.State p rate)
    (rows otherRows : CompletePublicTable.CompleteRows p)
    (selected otherSelected : Fin (ConstructorDimensions.M p))
    (start otherStart count : ℕ)
    (hspan : start + count ≤ p.T) (hspan' : otherStart + count ≤ p.T)
    (hmode : ReferenceActivePhysicalHorizon.allActiveAtStart left start)
    (hmode' : ReferenceActivePhysicalHorizon.allActiveAtStart right otherStart)
    (hi : left = right) (hr : rows = otherRows)
    (hj : selected = otherSelected) (ht : start = otherStart) :
    (ReferenceActivePhysicalHorizon.run left rows selected rewards start count hspan hmode).records =
      (ReferenceActivePhysicalHorizon.run right otherRows otherSelected rewards otherStart count
        hspan' hmode').records := by
  cases hi
  cases hr
  cases hj
  cases ht
  rfl

/-- The original record is the existing horizon record of the original corrected
launch, with its original rows, selected index and entire reward grid. -/
theorem originalCurrentRecord_eq_actualRunRecordAt (z : Z) :
    ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt
        (ReferenceFirstLaunchNumericalCell.launchState
          rate z.val rewards C_star C_h z.property.2.1)
        z.val.1.2 q rewards
        (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed)
        n (ReferenceFirstLiveBranchIntegralTransport.actualSourceCells_span
          rate rewards C_star C_h q t s hs z)
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate z.val rewards C_star C_h z.property.2.1).activeAtStart := by
  let x := ret z
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl
    rate rewards C_star C_h q t s hs z
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val = z.val := by
    have h := congrArg Subtype.val
      (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover_sourceSplit
        rate rewards C_star C_h q t s hs control0 z)
    exact h
  have hstart := (ReferenceInitializationControlRemainder.launchStartRemainderEvent_control_independent
    rate rewards C_star C_h q t s x.val x.property.1 control0 u).mp x.property.2
  let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed
    rate rewards C_star C_h q t u x.val x.property.1 s hs hstart
  have hlaunch := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t u x.val x.property.1 s hs hstart).1
  rw [hsource] at hlaunch
  have hseed : generated = ReferenceFirstLaunchNumericalCell.launchState
      rate z.val rewards C_star C_h z.property.2.1 :=
    Option.some.inj (hlaunch.symm.trans
      (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
        rate z.val rewards C_star C_h z.property.2.1))
  have hinput := ReferenceTotalSourceDisintegration.sourceIncomingBoundary_generatedNextInput
    rate rewards C_star C_h t control0 i0 z
  change ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
    rate rewards C_star C_h q t s hs control0 x u = _ at hinput
  have hstate : (ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput
      rate rewards C_star C_h q t s hs control0 x u).state =
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h z.property.2.1)
        z.val.1.2 q rewards
        (ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed)
        n (by have he := z.property.2.2; dsimp [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] at he; omega)
        (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
          rate z.val rewards C_star C_h z.property.2.1).activeAtStart).finalState := by
    dsimp only [ReferenceRetainedBoundaryMeasurability.retainedGeneratedNextInput]
    change (ReferenceActivePhysicalHorizon.run generated
      (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p
        (ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val))
      rewards s n _ _).finalState = _
    have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.val = q := z.property.1
    have he : ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed = s :=
      z.property.2.2
    exact run_finalState_congr rate rewards _ _ _ _ _ _ _ _ n _ _ _ _
      hseed (congrArg (fun source : S => source.1.2) hsource)
      ((congrArg (ActualInitializationPhysicalStep.selectedRowIndex p) hsource).trans hselected)
      he.symm
  apply congrArg (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
    (⟨input, ReferenceActivePhysicalStep.step input, rfl⟩ :
      ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
  apply roundInput_ext
  · exact (congrArg ReferenceActivePhysicalStep.RoundInput.state hinput).symm.trans hstate
  · rfl
  · exact z.property.1
  · apply Fin.ext
    have he := z.property.2.2
    dsimp [ReferenceFirstLiveRecordingSourceCylinder.stratumIndex] at he
    change t.val = ReferenceInitializationRun.elapsed p (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z.val rewards C_star C_h rate)).completed + n
    omega
  · rfl

/-- Baseline controls do not change the SAME original physical record. -/
theorem originalCurrentRecord_control_independent (control1 : TimeControl p) (z : Z) :
    ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control1 z := by
  rw [originalCurrentRecord_eq_actualRunRecordAt,
    originalCurrentRecord_eq_actualRunRecordAt]

/-- The original whole first-live window is the maximal actual launched run. -/
theorem wholeFirstLiveWindow_eq_actual (z : Z) :
    ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val =
      ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val rewards C_star C_h z.property.2.1 (p.T - s)
        (by have he : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s :=
              z.property.2.2
            have hle := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z.val rewards C_star C_h
            change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + _ ≤ p.T
            omega) := by
  let sf : Fin (p.T + 1) := ⟨s, by omega⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h s :=
    ⟨z.val, z.property.2.1, z.property.2.2⟩
  exact (ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sf x).1

omit q t s hs control0 in
/-- The physical and numerical first-live lists have the same length on ALL sources. -/
theorem wholeFirstLiveCells_length (omega : S) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length := by
  classical
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate omega rewards C_star C_h).crossing.isSome = true
  · let start := ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
    let sf : Fin (p.T + 1) := ⟨start, Nat.lt_succ_of_le
      (ReferenceCompletePhysicalHistory.physicalStart_le_T rate omega rewards C_star C_h)⟩
    let x : ReferenceFirstLiveOverflowReadout.LaunchFiber rate rewards C_star C_h start :=
      ⟨omega, hc, rfl⟩
    obtain ⟨hw, hl⟩ := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h sf x
    rw [hw, hl]
    exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length _ _ _ _ _ _ _ _
  · have hn : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate omega rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate omega rewards C_star C_h).crossing <;> simp_all
    obtain ⟨hw, hl, _⟩ := ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h omega hn
    rw [hw, hl]
    rfl

omit C_star C_h q t s hs control0 in
private theorem window_record_eq_actualRunRecordAt
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
    (start count : ℕ) (hspan : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (k : ℕ) (hk : k < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records).length) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records)[k]'hk =
      ReferenceAssignmentPayloadChronology.actualRunRecordAt initial rows selected rewards start k
        (by
          have hp : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
              (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active).records).length ≤ count := by
            exact (List.takeWhile_prefix _).length_le.trans
              (ReferenceActivePhysicalHorizon.run_record_count
                initial rows selected rewards start count hspan active).le
          exact (Nat.add_le_add_left (Nat.succ_le_of_lt (lt_of_lt_of_le hk hp)) start).trans hspan) active := by
  let run := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count hspan active
  have hwp : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow run.records).IsPrefix run.records :=
    List.takeWhile_prefix _
  have hkcount : k < count := by
    have hlen := hwp.length_le
    have hcount := ReferenceActivePhysicalHorizon.run_record_count initial rows selected rewards start count hspan active
    change k < (ReferenceFirstLiveConfirmationHistory.firstLiveWindow run.records).length at hk
    change run.records.length = count at hcount
    omega
  obtain ⟨suffix, hp⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start (k + 1) (count - (k + 1)) (by omega) active
  have hp' : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (k + 1)
      (by omega) active).records.IsPrefix run.records := by
    refine ⟨suffix, ?_⟩
    simpa only [Nat.add_sub_of_le (by omega : k + 1 ≤ count)] using hp.symm
  have hn : k < (ReferenceActivePhysicalHorizon.run initial rows selected rewards start
      (k + 1) (by omega) active).records.length := by
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    omega
  apply (hwp.getElem hk).trans
  apply (hp'.getElem hn).symm.trans
  apply (List.getElem_of_eq
    (ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt
      initial rows selected rewards start k (by omega) active) hn).trans
  have hlen := ReferenceActivePhysicalHorizon.run_record_count
    initial rows selected rewards start k (by omega) active
  simp [hlen]

/-- The current indexed record is physically the SAME original record. -/
theorem wholeFirstLiveWindow_current (z : Z)
    (hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val)[n]'hn =
      ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z := by
  have hw := wholeFirstLiveWindow_eq_actual rate rewards C_star C_h q t s hs z
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.val = q := z.property.1
  have hn' := hn
  rw [hw] at hn'
  apply (List.getElem_of_eq hw hn).trans
  rw [originalCurrentRecord_eq_actualRunRecordAt]
  have h := window_record_eq_actualRunRecordAt rate rewards
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h z.property.2.1)
    z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
    (ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
    (p.T - s) _ (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z.val rewards C_star C_h z.property.2.1).activeAtStart n hn'
  simpa only [ReferenceFirstWindowNumericalStream.actualFirstLiveWindow,
    ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
    ReferenceCompletePhysicalHistory.physicalStart, ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput, hselected] using h

omit rewards C_star C_h q t s hs control0 in
private theorem strict_enabled_of_actual_clock
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
    (state : ReferenceActivePhysicalStep.State p rate)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters r) (base : Fin (p.m - 1) → ℕ)
    (time : Fin p.T) (result : CoordinatorPhaseClock.StartRoundResult p)
    (hstate : state.coordinator = .live r owned base)
    (hclock : ReferenceCoordinatorClockDomains.clockAt rows selected time.val state)
    (hstart : CoordinatorPhaseClock.startRound p rate.eta.val time
      r.priorClock r.clockPending = .ok result)
    (hlive : CoordinatorLocalArmChoice.assignmentIsLive r.payload
      (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p result.clock.u) time) :
    time.val + 1 < result.clock.g := by
  classical
  simp only [ReferenceCoordinatorClockDomains.clockAt, hstate] at hclock
  obtain ⟨_, hvalid, hsigma, hu, hgrid, hsigmaTime, hbefore, _⟩ := hclock
  have hparam := ReferenceCoordinatorClockDomains.proposalParameterValid_of_rate rate
  have htime : CoordinatorPhaseClock.startRoundTimeValid p time r.priorClock := by
    simp only [CoordinatorPhaseClock.startRoundTimeValid, hsigma, hu]
    change r.payload.sigma.val < time.val ∧ time.val + 1 ≤ r.priorClock.g
    omega
  have hnoStart : ¬ CoordinatorPhaseClock.sourceStartTest r.priorClock.sigma
      r.priorClock.u time r.clockPending := by
    rw [hsigma, hu]
    exact CoordinatorPhaseClock.sourceStartTest_false_without_cutoff _ _ _
  cases hd : CoordinatorPhaseClock.detectCutoff r.priorClock time with
  | error failure =>
      simp [CoordinatorPhaseClock.startRound, hparam, hvalid, htime, hd] at hstart
  | ok decision =>
      cases decision with
      | cutoff sigma hsigma' =>
          obtain ⟨cut, hc, hcutClock, _⟩ := CoordinatorPhaseClock.startRound_cutoff_effect
            p rate.eta.val time sigma r.priorClock r.clockPending hparam hvalid htime hsigma' hd
          have he : cut = result := Except.ok.inj (hc.symm.trans hstart)
          have hu' : result.clock.u = some time := by rw [← he, hcutClock]
          have hlt := hlive.2
          rw [hu', CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock] at hlt
          exact False.elim (Nat.lt_irrefl (time.val + 1) hlt)
      | noCutoff =>
          have he : result.clock = r.priorClock := by
            simp only [CoordinatorPhaseClock.startRound, hparam, hvalid, htime,
              hd, hnoStart, ↓reduceIte, ↓reduceDIte] at hstart
            exact (congrArg CoordinatorPhaseClock.StartRoundResult.clock (Except.ok.inj hstart)).symm
          have hg : FollowerCutoffScan.calendarRound time ≠ r.priorClock.g := by
            intro hg
            obtain ⟨cut, hc, hcutClock, _⟩ := CoordinatorPhaseClock.startRound_grid_cutoff
              p rate.eta.val time r.payload.sigma r.priorClock r.clockPending
              hparam hvalid htime hsigma hu hg
            have hresult : cut = result := Except.ok.inj (hc.symm.trans hstart)
            have hu' := congrArg CoordinatorPhaseClock.ClockRegisters.u
              ((congrArg CoordinatorPhaseClock.StartRoundResult.clock hresult).trans he)
            rw [hcutClock, hu] at hu'
            cases hu'
          rw [he]
          change time.val + 1 ≠ r.priorClock.g at hg
          omega

/-- Positive physical offsets PRODUCE a genuine strictly enabled continuing
constructor. No constructor, no-failure or clock premise is supplied. -/
theorem source_positive_current_continuing (z : Z) (hpos : 0 < n)
    (hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length) :
    let input := (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z).input
    ∃ r owned base d hsStart continuation arm,
      (ReferenceActivePhysicalStep.prepare input).coordinator =
        .live r owned base (.continuingChosen d hsStart continuation arm) ∧
      t.val + 1 < d.startResult.clock.g := by
  classical
  dsimp only
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z.val rewards C_star C_h z.property.2.1
  let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
    rate z.val rewards C_star C_h z.property.2.1
  let start := ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h
  have he : start = s := z.property.2.2
  have hspan : start + (p.T - s) ≤ p.T := by
    have hsT := ReferenceCompletePhysicalHistory.physicalStart_le_T rate z.val rewards C_star C_h
    omega
  let E := ReferenceActivePhysicalHorizon.run initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards start (p.T - s) hspan seed.activeAtStart
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  have hnW : n < W.length := by
    rw [wholeFirstLiveWindow_eq_actual rate rewards C_star C_h q t s hs z] at hn
    exact hn
  let record := W[n]'hnW
  have hr : record = ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 z := by
    have hw := wholeFirstLiveWindow_eq_actual rate rewards C_star C_h q t s hs z
    exact (List.getElem_of_eq hw.symm hnW).trans
      (wholeFirstLiveWindow_current rate rewards C_star C_h q t s hs control0 z hn)
  rw [← hr]
  have hsafety := ReferenceFirstLiveCoordinatorSafety.run_first_live_coordinator_safety
    initial z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
    rewards start (p.T - s) hspan seed.activeAtStart seed.coordinatorFirst
  obtain ⟨prior, priorOwned, priorBase, hprior⟩ :=
    (hsafety.2.1 n (Nat.le_of_lt hnW)).2 hpos
  have hrecordAt := window_record_eq_actualRunRecordAt rate rewards initial z.val.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z.val) start (p.T - s)
    hspan seed.activeAtStart n hnW
  have hincoming : record.input.state.coordinator = .live prior priorOwned priorBase := by
    have hrecordAt' : record = _ := hrecordAt
    rw [hrecordAt']
    exact hprior
  obtain ⟨hinputs, _, states, memories, hordinary, hbranches⟩ :=
    ReferenceFirstWindowRecordingTruth.run_first_live_window_recording_truth
      initial z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
      rewards start (p.T - s) hspan seed.activeAtStart seed.coordinatorFirst
      seed.followers seed.memory seed.configuration seed.S_zero seed.delta_zero
      seed.backlog_zero seed.lastDown_none seed.unoccupied seed.bufferValid
      seed.chronologicalBuffer seed.bufferStamps seed.decoderValid ⟨n, hnW⟩
  dsimp only [Fin.val_mk] at hinputs hbranches
  have hprep : record.output.preparation = ReferenceActivePhysicalStep.prepare record.input := by
    rw [record.output_eq]
    rfl
  rcases hbranches with hfirst | hcontinuing
  · obtain ⟨installed, arm, hbranch, _⟩ := hfirst
    change record.output.preparation.coordinator = _ at hbranch
    rw [hprep] at hbranch
    simp [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hincoming, CoordinatorRoundDispatch.dispatch] at hbranch
    cases CoordinatorRoundDispatch.dispatchLive
      (ReferenceActivePhysicalStep.liveInput record.input prior priorOwned priorBase) <;> cases hbranch
  · obtain ⟨r, owned, base, d, hsStart, continuation, arm, hbranch,
        _, selected, hselection, hselected, _, _, out, _, _, hlive, _⟩ := hcontinuing
    change record.output.preparation.coordinator = _ at hbranch
    have hseedClock : ReferenceCoordinatorClockDomains.clockAt z.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) start initial := by
      have hfirst : initial.coordinator = .first := seed.coordinatorFirst
      simp only [ReferenceCoordinatorClockDomains.clockAt, hfirst]
    have hmem : record ∈ E.records :=
      (List.takeWhile_prefix (fun (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
        !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (l := E.records)).subset
        (List.getElem_mem hnW)
    have hclock := (ReferenceRunClockPreservation.run_clockAt initial z.val.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z.val) rewards start (p.T - s)
      hspan seed.activeAtStart hseedClock).2.2.2 record hmem
    have horigin : record.input.state.coordinator = .live r owned base := by
      have hb := hbranch
      rw [hprep] at hb
      simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
        hincoming, CoordinatorRoundDispatch.dispatch] at hb
      obtain ⟨hregs, howned, hbase, _⟩ := ReferenceActivePhysicalStep.DispatchCut.live.inj hb
      cases hregs
      cases howned
      cases hbase
      exact hincoming
    have henabled : record.input.time.val + 1 < d.startResult.clock.g := by
      have hlive' : CoordinatorLocalArmChoice.assignmentIsLive r.payload
          (CoordinatorLiveChoiceRecorderStep.cutoffFromClock p d.startResult.clock.u) record.input.time := by
        rw [hselected] at hlive
        exact hlive
      exact strict_enabled_of_actual_clock rate z.val.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z.val) record.input.state
        r owned base record.input.time d.startResult horigin hclock.1 hsStart hlive'
    rw [hprep] at hbranch
    refine ⟨r, owned, base, d, hsStart, continuation, arm, ?_, ?_⟩
    · exact hbranch
    · have ht : record.input.time = t := by rw [hr]; rfl
      simpa only [ht] using henabled

private theorem inputAtControl_twice
    (input : ReferenceActivePhysicalStep.RoundInput p rate) (u v : TimeControl p) :
    ReferenceContinuingLiveSlicePreparation.inputAtControl
      (ReferenceContinuingLiveSlicePreparation.inputAtControl input u) v =
      ReferenceContinuingLiveSlicePreparation.inputAtControl input v := by
  classical
  apply roundInput_ext rate
  · rfl
  · simp [ReferenceContinuingLiveSlicePreparation.inputAtControl,
      ReferenceContinuingLiveSlicePreparation.rowsAtControl,
      ReferenceContinuingLiveSlicePreparation.rowAtControl,
      ReferenceActivePhysicalStep.RoundInput.row, Function.update_idem]
  · rfl
  · rfl
  · rfl

private theorem source_generatedSeed_eq_original (z : Z) :
    ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
      control0 (ret z).val (ret z).property.1 s hs (ret z).property.2 =
      ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h z.property.2.1 := by
  let x := ret z
  let u := ReferenceFirstLiveRecordingSourceCylinder.originalControl
    rate rewards C_star C_h q t s hs z
  have hsource : ReferenceGeneratedActivePrefixFactor.splitSource q t u x.val = z.val :=
    congrArg Subtype.val (ReferenceFirstLiveRecordingSourceCylinder.sourceRecover_sourceSplit
      rate rewards C_star C_h q t s hs control0 z)
  obtain ⟨active, hbase, _, horiginal, _⟩ :=
    ReferenceGeneratedActivePrefixFactor.generatedActivePrefixFactor_control_independent
      rate rewards C_star C_h q t x.val x.property.1 control0 s n hs
      (by omega) x.property.2 control0 u
  rw [hsource] at horiginal
  have hgenerated := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2).1
  exact Option.some.inj (hgenerated.symm.trans (hbase.trans (horiginal.symm.trans
    (ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
      rate z.val rewards C_star C_h z.property.2.1))))

/-- EVERY strict-prior cutoff tag agrees with the actual original prefix.
The common seed and agreement of all earlier controls are produced internally. -/
theorem source_prior_cutoffTags_eq (z : Z) :
    ((ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control0 (ret z)).records.take n).map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate z.val rewards C_star C_h z.property.2.1 n
        (by have he : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s :=
              z.property.2.2
            change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + n ≤ p.T
            omega)).records.map
        (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input) := by
  let x := ret z
  let source0 := ReferenceGeneratedActivePrefixFactor.splitSource q t control0 x.val
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate z.val rewards C_star C_h z.property.2.1
  let generated := ReferenceGeneratedActivePrefixFactor.generatedActiveSeed rate rewards C_star C_h q t
    control0 x.val x.property.1 s hs x.property.2
  have hseed : generated = initial := source_generatedSeed_eq_original
    rate rewards C_star C_h q t s hs control0 z
  let generatedMode := (ReferenceGeneratedActivePrefixFactor.generatedActiveSeed_spec
    rate rewards C_star C_h q t control0 x.val x.property.1 s hs x.property.2).2.1
  have mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial s := hseed ▸ generatedMode
  have hselected0 : ActualInitializationPhysicalStep.selectedRowIndex p source0 = q := by
    rw [← ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex_eq_selectedRowIndex]
    exact ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_coordinatorIndex
      p q t control0 x.val x.property.1
  have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.val = q := z.property.1
  have hindex : ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z.val = q := z.property.1
  have he : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := z.property.2.2
  have hcontrols : ∀ j : Fin p.T, j.val < t.val →
      (source0.1.2 q).2 j = (z.val.1.2 q).2 j := by
    intro j hj
    have hsource := ReferenceFirstLiveSourcePrefixBranchInvariance.splitSource_sourceRetained
      rate rewards C_star C_h q t s hs control0 z
    change source0 = _ at hsource
    rw [hsource]
    simp [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl, hindex,
      Function.update_of_ne (show j ≠ t from Fin.ne_of_val_ne (by omega))]
  have htags := ReferenceFirstLiveSourcePrefixBranchInvariance.run_cutoffTags_eq rate initial
    source0.1.2 z.val.1.2 q rewards s n (by omega) mode
    (fun j _ hj => hcontrols j (by omega))
    (fun j hj => congrArg (fun u : TimeControl p => u.1 ContinuousControlSlice.Label.prop)
      (hcontrols j (by omega)))
  rw [ReferenceFirstLiveSourcePrefixBranchInvariance.actualRetainedPrefixRun_take_prefix]
  have hleft : (ReferenceRetainedAssignmentReleaseHistory.retainedGeneratedPrefix
      rate rewards C_star C_h q t s hs control0 x control0 n (by omega)).records =
      (ReferenceActivePhysicalHorizon.run initial source0.1.2 q rewards s n (by omega) mode).records := by
    exact run_records_congr rate rewards _ _ _ _ _ _ _ _ n _ _ _ _ hseed rfl hselected0 rfl
  have hright : (ReferenceActivePhysicalHorizon.run initial z.val.1.2 q rewards s n (by omega) mode).records =
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z.val rewards C_star C_h
        z.property.2.1 n (by
          change ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + n ≤ p.T
          omega)).records := by
    exact run_records_congr rate rewards _ _ _ _ _ _ _ _ n _ _ _ _ rfl rfl hselected.symm he.symm
  rw [hleft, htags, hright]

omit rate rewards C_star C_h q t s hs control0 in
private theorem cutoff_free_take_of_window_length
    {p : Parameters} {rate : RateInput p}
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (k : ℕ) (hk : k ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow records).length) :
    ∀ record ∈ records.take k, ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow records
  have hp : W = records.take W.length := List.prefix_iff_eq_take.mp (List.takeWhile_prefix _)
  have ht : records.take k = W.take k := by
    rw [hp, List.take_take, Nat.min_eq_left hk]
  intro record hr
  have hm : record ∈ W := List.mem_of_mem_take (ht ▸ hr)
  have h : (!ReferenceCollectionPhaseHistory.cutoffChosen record.input) = true := List.mem_takeWhile_imp (p := fun (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) =>
    !ReferenceCollectionPhaseHistory.cutoffChosen r.input) (l := records) hm
  simpa only [Bool.not_eq_true'] using h

omit C_star C_h q t s hs control0 in
private theorem run_records_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan active).records.take a =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start a ((Nat.add_le_add_left hab start).trans hspan) active).records := by
  obtain ⟨suffix, hp⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start a (b - a) (by omega) active
  have hp' : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
      (by omega) active).records.IsPrefix
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan active).records := by
    refine ⟨suffix, ?_⟩
    simpa only [Nat.add_sub_of_le hab] using hp.symm
  simpa only [ReferenceActivePhysicalHorizon.run_record_count] using
    (List.prefix_iff_eq_take.mp hp').symm

omit C_star C_h q t s hs control0 in
private theorem window_length_of_cutoff_free_prefix
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (ConstructorDimensions.M p))
    (start a b : ℕ) (hab : a ≤ b) (hspan : start + b ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfree : ∀ record ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start a ((Nat.add_le_add_left hab start).trans hspan) active).records, ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) :
    a ≤ (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan active).records).length := by
  obtain ⟨suffix, hp⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start a (b - a) (by omega) active
  have hp' : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan active).records =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start a (by omega) active).records ++ suffix := by
    simpa only [Nat.add_sub_of_le hab] using hp
  change a ≤ (List.takeWhile _ _).length
  rw [hp', List.takeWhile_append_of_pos (by intro record hr; simp only [hfree record hr, Bool.not_false])]
  simp only [List.length_append, ReferenceActivePhysicalHorizon.run_record_count]
  exact Nat.le_add_right _ _

/-- The entire canonical strict-prior no-cutoff conjunction follows from
membership of the original current offset in the physical window. -/
theorem source_prior_not_cutoff (z : Z)
    (hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length) :
    ∀ record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control0 (ret z)).records.take n,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
  have hw := wholeFirstLiveWindow_eq_actual rate rewards C_star C_h q t s hs z
  rw [hw] at hn
  have hspan : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h + (p.T - s) ≤ p.T := by
    have he : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := z.property.2.2
    omega
  have htake := run_records_take rate rewards
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h z.property.2.1)
    z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
    (ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
    n (p.T - s) (by omega) hspan
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z.val rewards C_star C_h z.property.2.1).activeAtStart
  have hfree := cutoff_free_take_of_window_length _ n (Nat.le_of_lt hn)
  dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveRun,
    ReferenceCompletePhysicalHistory.physicalStart, ReferenceCompletePhysicalHistory.generatedBoundary,
    ReferenceCompletePhysicalHistory.generatedInput] at htake hfree
  rw [htake] at hfree
  intro record hr
  have hm : ReferenceCollectionPhaseHistory.cutoffChosen record.input ∈
      ((ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 (ret z)).records.take n).map
        (fun other => ReferenceCollectionPhaseHistory.cutoffChosen other.input) :=
    List.mem_map.mpr ⟨record, hr, rfl⟩
  rw [source_prior_cutoffTags_eq rate rewards C_star C_h q t s hs control0 z] at hm
  obtain ⟨other, hother, heq⟩ := List.mem_map.mp hm
  exact heq.symm.trans (hfree other hother)

private theorem preparedStart_data
    (input : ReferenceActivePhysicalStep.RoundInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate input = some started) :
    ∃ r owned base d hsStart continuation arm,
      (ReferenceActivePhysicalStep.prepare input).coordinator =
        .live r owned base (.continuingChosen d hsStart continuation arm) ∧ d.startResult = started := by
  cases hc : (ReferenceActivePhysicalStep.prepare input).coordinator with
  | live r owned base outcome =>
      cases outcome with
      | continuingChosen d hsStart continuation arm =>
          simp only [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hc,
            Option.some.injEq] at hstart
          exact ⟨r, owned, base, d, hsStart, continuation, arm, rfl, hstart⟩
      | _ => simp [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hc] at hstart
  | _ => simp [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hc] at hstart

private theorem preparedStart_atControl
    (input : ReferenceActivePhysicalStep.RoundInput p rate) (u : TimeControl p) :
    ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
      (ReferenceContinuingLiveSlicePreparation.inputAtControl input u) =
      ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate input := by
  cases h0 : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate input with
  | some started =>
      obtain ⟨r, owned, base, d, hsStart, c, arm, hc, hd⟩ := preparedStart_data rate input started h0
      obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
        input r owned base d hsStart c arm hc u
      simp only [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hu, hd]
  | none =>
      cases h1 : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
          (ReferenceContinuingLiveSlicePreparation.inputAtControl input u) with
      | none => rfl
      | some started =>
          obtain ⟨r, owned, base, d, hsStart, c, arm, hc, hd⟩ := preparedStart_data rate _ started h1
          obtain ⟨cu, au, hu⟩ := ReferenceContinuingLiveSlicePreparation.continuing_cut_at_control
            _ r owned base d hsStart c arm hc (input.row.2 input.time)
          have hback : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
              (ReferenceContinuingLiveSlicePreparation.inputAtControl
                (ReferenceContinuingLiveSlicePreparation.inputAtControl input u) (input.row.2 input.time)) =
              some started := by
            simp only [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hu, hd]
          rw [inputAtControl_twice, ReferenceContinuingLiveSlicePreparation.inputAtControl_actual, h0] at hback
          cases hback

/-- The actual continuing start-result is the SAME original start-result. -/
theorem source_preparedStart_eq_original (z : Z) :
    ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
      (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
        rate rewards C_star C_h q t s hs control0 (ret z)) =
      ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
          rate rewards C_star C_h q t s hs control0 z).input := by
  have h := preparedStart_atControl rate
    (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
      rate rewards C_star C_h q t s hs control0 (ret z))
    (ReferenceFirstLiveRecordingSourceCylinder.originalControl rate rewards C_star C_h q t s hs z)
  change ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
    (ReferenceFirstLiveRecordingReadoutMeasurability.sourceInputAtControl (ret z) _) = _ at h
  rw [ReferenceFirstLiveRecordingSourceCylinder.sourceInputAtControl_eq_original] at h
  exact h.symm

/-- Both canonical branches are produced from the positive physical cell. -/
theorem source_branches_of_positive_cell (z : Z) (hpos : 0 < n)
    (hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
      rate rewards C_star C_h q t s hs control0 (ret z) ∨ Be (ret z) := by
  classical
  obtain ⟨r, owned, base, d, hsStart, continuation, arm, hcoord, henabled⟩ :=
    source_positive_current_continuing rate rewards C_star C_h q t s hs control0 z hpos hn
  have hstart : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
      (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
        rate rewards C_star C_h q t s hs control0 (ret z)) = some d.startResult := by
    rw [source_preparedStart_eq_original]
    simp only [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hcoord]
  obtain ⟨r0, owned0, base0, d0, hs0, c0, a0, hc0, hd0⟩ := preparedStart_data rate _ _ hstart
  have hpast := source_prior_not_cutoff rate rewards C_star C_h q t s hs control0 z hn
  by_cases hpending : d.startResult.pending.Nonempty
  · left
    exact ⟨hpos, hpast, by simp only [hc0, hd0]; exact ⟨hpending, henabled⟩⟩
  · right
    exact ⟨hpos, hpast, by simp only [hc0, hd0]; exact ⟨Finset.not_nonempty_iff_eq_empty.mp hpending, henabled⟩⟩

private theorem emptyBranch_iff_start (z : Z) :
    ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty rate rewards C_star C_h q t s hs control0 (ret z) ↔
      0 < n ∧
      (∀ record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 (ret z)).records.take n,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ∧
      ∃ started, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
          rate rewards C_star C_h q t s hs control0 (ret z)) = some started ∧
        started.pending = ∅ ∧ t.val + 1 < started.clock.g := by
  unfold ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  cases hc : (ReferenceActivePhysicalStep.prepare
      (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
        rate rewards C_star C_h q t s hs control0 (ret z))).coordinator with
  | live r owned base outcome =>
      cases outcome <;> simp [hc, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart]
  | _ => simp [hc, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart]

private theorem nonemptyBranch_iff_start (z : Z) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch rate rewards C_star C_h q t s hs control0 (ret z) ↔
      0 < n ∧
      (∀ record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
        rate rewards C_star C_h q t s hs control0 (ret z)).records.take n,
        ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ∧
      ∃ started, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
          rate rewards C_star C_h q t s hs control0 (ret z)) = some started ∧
        started.pending.Nonempty ∧ t.val + 1 < started.clock.g := by
  unfold ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
  apply and_congr Iff.rfl
  apply and_congr Iff.rfl
  cases hc : (ReferenceActivePhysicalStep.prepare
      (ReferenceFirstLiveRecordingSourceBranch.actualCurrentInput
        rate rewards C_star C_h q t s hs control0 (ret z))).coordinator with
  | live r owned base outcome =>
      cases outcome <;> simp [hc, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart]
  | _ => simp [hc, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart]

private theorem source_window_of_free_current_prefix (z : Z)
    (hfree : ∀ record ∈ (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate z.val rewards C_star C_h z.property.2.1 (n + 1)
      (ReferenceFirstLiveBranchIntegralTransport.actualSourceCells_span rate rewards C_star C_h q t s hs z)).records,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) :
    n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val).length := by
  rw [wholeFirstLiveWindow_eq_actual rate rewards C_star C_h q t s hs z]
  have he : ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h = s := z.property.2.2
  have h := window_length_of_cutoff_free_prefix rate rewards
    (ReferenceFirstLaunchNumericalCell.launchState rate z.val rewards C_star C_h z.property.2.1)
    z.val.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z.val)
    (ReferenceCompletePhysicalHistory.physicalStart rate z.val rewards C_star C_h)
    (n + 1) (p.T - s) (by omega) (by omega)
    (ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
      rate z.val rewards C_star C_h z.property.2.1).activeAtStart hfree
  exact lt_of_lt_of_le (Nat.lt_succ_self n) h

/-- Exhaustion by the two existing branches, on EVERY original stratum source. -/
theorem source_positive_cell_iff_branches (z : Z) :
    (0 < n ∧ n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h z.val).length) ↔
      ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
        rate rewards C_star C_h q t s hs control0 (ret z) ∨ Be (ret z) := by
  constructor
  · rintro ⟨hpos, hn⟩
    exact source_branches_of_positive_cell rate rewards C_star C_h q t s hs control0 z hpos hn
  · rintro (hb | he)
    · refine ⟨hb.1, source_window_of_free_current_prefix rate rewards C_star C_h q t s hs z ?_⟩
      have hw := (ReferenceFirstLiveSourceCellReadout.source_current_window
        rate rewards C_star C_h q t s hs control0 ⟨z, hb⟩).1
      have hf := List.takeWhile_eq_self_iff.mp hw
      intro record hr
      have h := hf record hr
      simpa only [Bool.not_eq_true'] using h
    · refine ⟨he.1, source_window_of_free_current_prefix rate rewards C_star C_h q t s hs z ?_⟩
      have hw := ReferenceFirstLiveEmptyPendingMarkerLaw.actualRetainedPrefixRun_current_in_firstLiveWindow
        rate rewards C_star C_h q t s hs control0 (ret z) he
      have hpast := cutoff_free_take_of_window_length _ n (Nat.le_of_lt hw.1)
      have htags := source_prior_cutoffTags_eq rate rewards C_star C_h q t s hs control0 z
      have horiginalPast : ∀ record ∈ (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate z.val rewards C_star C_h z.property.2.1 n (by
            have hspan := ReferenceFirstLiveBranchIntegralTransport.actualSourceCells_span
              rate rewards C_star C_h q t s hs z
            omega)).records, ReferenceCollectionPhaseHistory.cutoffChosen record.input = false := by
        have hbool : ∀ b ∈ ((ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
            rate rewards C_star C_h q t s hs control0 (ret z)).records.take n).map
            (fun record => ReferenceCollectionPhaseHistory.cutoffChosen record.input), b = false := by
          simpa only [List.forall_mem_map] using hpast
        rw [htags] at hbool
        simpa only [List.forall_mem_map] using hbool
      obtain ⟨_, _, started, hstart, _, _⟩ := (emptyBranch_iff_start
        rate rewards C_star C_h q t s hs control0 z).mp he
      rw [source_preparedStart_eq_original] at hstart
      obtain ⟨r, owned, base, d, hsStart, c, arm, hc, hd⟩ := preparedStart_data rate _ _ hstart
      have hcurrent : ReferenceCollectionPhaseHistory.cutoffChosen
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z).input = false := by
        simp only [ReferenceCollectionPhaseHistory.cutoffChosen, hc]
      have hselected : ActualInitializationPhysicalStep.selectedRowIndex p z.val = q := z.property.1
      dsimp only [ReferenceFirstWindowNumericalStream.actualFirstLiveRun] at horiginalPast ⊢
      rw [ReferenceAssignmentPayloadChronology.run_successor_actualRunRecordAt]
      intro record hr
      rcases List.mem_append.mp hr with hp | hc
      · exact horiginalPast record hp
      · simp only [List.mem_singleton] at hc
        subst record
        rw [originalCurrentRecord_eq_actualRunRecordAt] at hcurrent
        simpa only [hselected] using hcurrent

/-- The computed empty/nonempty branches are disjoint without deleting any source. -/
theorem source_branches_disjoint (z : Z) :
    ¬ (ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch
      rate rewards C_star C_h q t s hs control0 (ret z) ∧ Be (ret z)) := by
  rintro ⟨hp, he⟩
  exact ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty_not_continuing
    rate rewards C_star C_h q t s hs control0 ⟨ret z, he⟩ hp

private theorem source_prior_tests_control_independent (control1 : TimeControl p) (z : Z) :
    (∀ record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control0 (ret z)).records.take n,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) ↔
    (∀ record ∈ (ReferenceFirstLiveRecordingSourceBranch.actualRetainedPrefixRun
      rate rewards C_star C_h q t s hs control1
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control1 z)).records.take n,
      ReferenceCollectionPhaseHistory.cutoffChosen record.input = false) := by
  have h := (source_prior_cutoffTags_eq rate rewards C_star C_h q t s hs control0 z).trans
    (source_prior_cutoffTags_eq rate rewards C_star C_h q t s hs control1 z).symm
  simpa only [List.forall_mem_map] using Iff.of_eq
    (congrArg (fun values : List Bool => ∀ b ∈ values, b = false) h)

theorem source_emptyBranch_control_independent (control1 : TimeControl p) (z : Z) :
    ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty rate rewards C_star C_h q t s hs control0 (ret z) ↔
      ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty rate rewards C_star C_h q t s hs control1
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control1 z) := by
  rw [emptyBranch_iff_start, emptyBranch_iff_start]
  apply and_congr Iff.rfl
  apply and_congr (source_prior_tests_control_independent rate rewards C_star C_h q t s hs control0 control1 z)
  rw [source_preparedStart_eq_original, source_preparedStart_eq_original,
    originalCurrentRecord_control_independent rate rewards C_star C_h q t s hs control0 control1 z]

theorem source_nonemptyBranch_control_independent (control1 : TimeControl p) (z : Z) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch rate rewards C_star C_h q t s hs control0 (ret z) ↔
      ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch rate rewards C_star C_h q t s hs control1
        (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained rate rewards C_star C_h q t s hs control1 z) := by
  rw [nonemptyBranch_iff_start, nonemptyBranch_iff_start]
  apply and_congr Iff.rfl
  apply and_congr (source_prior_tests_control_independent rate rewards C_star C_h q t s hs control0 control1 z)
  rw [source_preparedStart_eq_original, source_preparedStart_eq_original,
    originalCurrentRecord_control_independent rate rewards C_star C_h q t s hs control0 control1 z]

private theorem source_current_start_enabled (z : Z) (hpos : 0 < n)
    (hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h z.val).length)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (hstart : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
      (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
        rate rewards C_star C_h q t s hs control0 z).input = some started) :
    t.val + 1 < started.clock.g := by
  obtain ⟨r, owned, base, d, hsStart, c, arm, hc, henabled⟩ :=
    source_positive_current_continuing rate rewards C_star C_h q t s hs control0 z hpos hn
  have hd : d.startResult = started := Option.some.inj (by
    simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart, hc] using hstart)
  exact hd ▸ henabled

theorem source_empty_cell_iff (z : Z) :
    ReferenceFirstLiveEmptyPendingMarkerLaw.Bempty rate rewards C_star C_h q t s hs control0 (ret z) ↔
      0 < n ∧ ∃ hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z.val).length,
        match (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hn).input).coordinator with
        | .live _ _ _ (.continuingChosen d _ _ _) => d.startResult.pending = ∅
        | _ => False := by
  constructor
  · intro hb
    have hcell := (source_positive_cell_iff_branches rate rewards C_star C_h q t s hs control0 z).mpr
      (Or.inr hb)
    refine ⟨hcell.1, hcell.2, ?_⟩
    obtain ⟨_, _, started, hstart, hpending, _⟩ := (emptyBranch_iff_start
      rate rewards C_star C_h q t s hs control0 z).mp hb
    rw [source_preparedStart_eq_original] at hstart
    have hstartW : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hcell.2).input = some started := by
      rw [wholeFirstLiveWindow_current rate rewards C_star C_h q t s hs control0 z hcell.2]
      exact hstart
    obtain ⟨rW, oW, bW, dW, hsW, cW, aW, hcW, hdW⟩ := preparedStart_data rate _ _ hstartW
    simpa only [hcW, hdW] using hpending
  · rintro ⟨hpos, hn, htest⟩
    have hex : ∃ started, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hn).input = some started ∧ started.pending = ∅ := by
      cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hn).input).coordinator with
      | live r owned base outcome =>
          cases outcome <;> simp [hc, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart] at htest ⊢
          exact htest
      | _ => simp [hc] at htest
    obtain ⟨started, hstart, hpending⟩ := hex
    rw [wholeFirstLiveWindow_current rate rewards C_star C_h q t s hs control0 z hn] at hstart
    apply (emptyBranch_iff_start rate rewards C_star C_h q t s hs control0 z).mpr
    refine ⟨hpos, source_prior_not_cutoff rate rewards C_star C_h q t s hs control0 z hn,
      started, ?_, hpending, source_current_start_enabled rate rewards C_star C_h q t s hs control0 z hpos hn started hstart⟩
    rw [source_preparedStart_eq_original]
    exact hstart

theorem source_nonempty_cell_iff (z : Z) :
    ReferenceFirstLiveRecordingSourceBranch.continuingRecordingBranch rate rewards C_star C_h q t s hs control0 (ret z) ↔
      0 < n ∧ ∃ hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h z.val).length,
        match (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hn).input).coordinator with
        | .live _ _ _ (.continuingChosen d _ _ _) => d.startResult.pending.Nonempty
        | _ => False := by
  constructor
  · intro hb
    have hcell := (source_positive_cell_iff_branches rate rewards C_star C_h q t s hs control0 z).mpr
      (Or.inl hb)
    refine ⟨hcell.1, hcell.2, ?_⟩
    obtain ⟨_, _, started, hstart, hpending, _⟩ := (nonemptyBranch_iff_start
      rate rewards C_star C_h q t s hs control0 z).mp hb
    rw [source_preparedStart_eq_original] at hstart
    have hstartW : ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hcell.2).input = some started := by
      rw [wholeFirstLiveWindow_current rate rewards C_star C_h q t s hs control0 z hcell.2]
      exact hstart
    obtain ⟨rW, oW, bW, dW, hsW, cW, aW, hcW, hdW⟩ := preparedStart_data rate _ _ hstartW
    simpa only [hcW, hdW] using hpending
  · rintro ⟨hpos, hn, htest⟩
    have hex : ∃ started, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart rate
        ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hn).input = some started ∧ started.pending.Nonempty := by
      cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z.val)[n]'hn).input).coordinator with
      | live r owned base outcome =>
          cases outcome <;> simp [hc, ReferenceFirstLiveSourcePrefixBranchInvariance.preparedContinuingStart] at htest ⊢
          exact htest
      | _ => simp [hc] at htest
    obtain ⟨started, hstart, hpending⟩ := hex
    rw [wholeFirstLiveWindow_current rate rewards C_star C_h q t s hs control0 z hn] at hstart
    apply (nonemptyBranch_iff_start rate rewards C_star C_h q t s hs control0 z).mpr
    refine ⟨hpos, source_prior_not_cutoff rate rewards C_star C_h q t s hs control0 z hn,
      started, ?_, hpending, source_current_start_enabled rate rewards C_star C_h q t s hs control0 z hpos hn started hstart⟩
    rw [source_preparedStart_eq_original]
    exact hstart

/-- Literal image of the existing empty branch in the original source. -/
def originalEmptyEvent : Set S := (Subtype.val : Z → S) '' EZ

theorem mem_originalEmptyEvent_iff (omega : S) :
    omega ∈ originalEmptyEvent rate rewards C_star C_h q t s hs control0 ↔
      ∃ hE : omega ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent
          rate rewards C_star C_h t i0,
        Be (ret (⟨omega, hE⟩ : Z)) := by
  constructor
  · rintro ⟨z, hz, hω⟩
    subst omega
    exact ⟨z.property, hz⟩
  · rintro ⟨hE, hB⟩
    exact ⟨⟨omega, hE⟩, hB, rfl⟩

theorem mem_originalEmptyEvent_physical_iff (omega : S) :
    omega ∈ originalEmptyEvent rate rewards C_star C_h q t s hs control0 ↔
      omega ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0 ∧
      0 < n ∧ ∃ hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h omega).length,
        match (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[n]'hn).input).coordinator with
        | .live _ _ _ (.continuingChosen d _ _ _) => d.startResult.pending = ∅
        | _ => False := by
  rw [mem_originalEmptyEvent_iff]
  constructor
  · rintro ⟨hE, hb⟩
    obtain ⟨hpos, hn, htest⟩ := (source_empty_cell_iff
      rate rewards C_star C_h q t s hs control0 ⟨omega, hE⟩).mp hb
    refine ⟨hE, hpos, hn, ?_⟩
    cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h omega)[n]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simpa only [hc] using htest
    | _ => simpa only [hc] using htest
  · rintro ⟨hE, hpos, hn, htest⟩
    refine ⟨hE, (source_empty_cell_iff rate rewards C_star C_h q t s hs control0 ⟨omega, hE⟩).mpr ⟨hpos, hn, ?_⟩⟩
    cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h omega)[n]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simpa only [hc] using htest
    | _ => simpa only [hc] using htest

theorem mem_originalBranchEvent_physical_iff (omega : S) :
    omega ∈ ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t s hs control0 ↔
      omega ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0 ∧
      0 < n ∧ ∃ hn : n < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h omega).length,
        match (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[n]'hn).input).coordinator with
        | .live _ _ _ (.continuingChosen d _ _ _) => d.startResult.pending.Nonempty
        | _ => False := by
  rw [ReferenceFirstLiveBranchIntegralTransport.mem_originalBranchEvent_iff]
  constructor
  · rintro ⟨hE, hb⟩
    obtain ⟨hpos, hn, htest⟩ := (source_nonempty_cell_iff
      rate rewards C_star C_h q t s hs control0 ⟨omega, hE⟩).mp hb
    refine ⟨hE, hpos, hn, ?_⟩
    cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h omega)[n]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simpa only [hc] using htest
    | _ => simpa only [hc] using htest
  · rintro ⟨hE, hpos, hn, htest⟩
    refine ⟨hE, (source_nonempty_cell_iff rate rewards C_star C_h q t s hs control0 ⟨omega, hE⟩).mpr ⟨hpos, hn, ?_⟩⟩
    cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h omega)[n]'hn).input).coordinator with
    | live r owned base outcome => cases outcome <;> simpa only [hc] using htest
    | _ => simpa only [hc] using htest

/-- Both baselines select the same subset of original sources. -/
theorem originalEmptyEvent_control_independent (control1 : TimeControl p) :
    originalEmptyEvent rate rewards C_star C_h q t s hs control0 =
      originalEmptyEvent rate rewards C_star C_h q t s hs control1 := by
  ext omega
  constructor <;> rintro ⟨z, hz, rfl⟩
  · exact ⟨z, (source_emptyBranch_control_independent
      rate rewards C_star C_h q t s hs control0 control1 z).mp hz, rfl⟩
  · exact ⟨z, (source_emptyBranch_control_independent
      rate rewards C_star C_h q t s hs control0 control1 z).mpr hz, rfl⟩

theorem originalBranchEvent_control_independent (control1 : TimeControl p) :
    ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t s hs control0 =
      ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent rate rewards C_star C_h q t s hs control1 := by
  ext omega
  constructor <;> rintro ⟨z, hz, rfl⟩
  · exact ⟨z, (source_nonemptyBranch_control_independent
      rate rewards C_star C_h q t s hs control0 control1 z).mp hz, rfl⟩
  · exact ⟨z, (source_nonemptyBranch_control_independent
      rate rewards C_star C_h q t s hs control0 control1 z).mpr hz, rfl⟩

/-- Forget only the two subtype proofs, retaining the same original source. -/
def forgetEmpty (z : Ze) : S := z.val.val

theorem measurableSet_originalEmptyEvent :
    MeasurableSet (originalEmptyEvent rate rewards C_star C_h q t s hs control0) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_sourceStratum
    rate rewards C_star C_h q t s hs control0)).measurableSet_image.mpr
      (ReferenceFirstLiveEmptyPendingMarkerLaw.measurableSet_sourceEmpty
        rate rewards C_star C_h q t s hs control0)

theorem measurableEmbedding_forgetEmpty :
    MeasurableEmbedding (forgetEmpty rate rewards C_star C_h q t s hs control0) :=
  (MeasurableEmbedding.subtype_coe (measurableSet_sourceStratum
    rate rewards C_star C_h q t s hs control0)).comp
      (MeasurableEmbedding.subtype_coe
        (ReferenceFirstLiveEmptyPendingMarkerLaw.measurableSet_sourceEmpty
          rate rewards C_star C_h q t s hs control0))

private theorem emptySubtype_map :
    (muE).map (Subtype.val : Ze → Z) = (muZ).restrict EZ :=
  map_comap_subtype_coe
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurableSet_sourceEmpty
      rate rewards C_star C_h q t s hs control0) muZ

/-- Exact original-law restriction, without positive-mass or normalization premises. -/
theorem muEmpty_map_original :
    (muE).map (forgetEmpty rate rewards C_star C_h q t s hs control0) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (originalEmptyEvent rate rewards C_star C_h q t s hs control0) := by
  let hOuter := MeasurableEmbedding.subtype_coe
    (measurableSet_sourceStratum rate rewards C_star C_h q t s hs control0)
  let hInner := MeasurableEmbedding.subtype_coe
    (ReferenceFirstLiveEmptyPendingMarkerLaw.measurableSet_sourceEmpty
      rate rewards C_star C_h q t s hs control0)
  have hPre : (Subtype.val : Z → S) ⁻¹'
      originalEmptyEvent rate rewards C_star C_h q t s hs control0 = EZ := by
    ext z
    constructor
    · rintro ⟨y, hy, hEq⟩
      have hzy : y = z := Subtype.ext hEq
      simpa only [hzy] using hy
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hSubset : originalEmptyEvent rate rewards C_star C_h q t s hs control0 ⊆
      ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0 := by
    rintro omega ⟨z, hz, rfl⟩
    exact z.property
  calc
    (muE).map (forgetEmpty rate rewards C_star C_h q t s hs control0) =
        ((muE).map (Subtype.val : Ze → Z)).map (Subtype.val : Z → S) := by
      change (muE).map (Subtype.val ∘ Subtype.val) = _
      exact (Measure.map_map hOuter.measurable hInner.measurable).symm
    _ = ((muZ).restrict EZ).map (Subtype.val : Z → S) := by
      rw [emptySubtype_map rate rewards C_star C_h q t s hs control0]
    _ = ((muZ).map (Subtype.val : Z → S)).restrict
        (originalEmptyEvent rate rewards C_star C_h q t s hs control0) := by
      have h := hOuter.restrict_map muZ
        (originalEmptyEvent rate rewards C_star C_h q t s hs control0)
      rw [hPre] at h
      exact h.symm
    _ = ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
        (ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t i0)).restrict
          (originalEmptyEvent rate rewards C_star C_h q t s hs control0) := by
      rw [ReferenceTotalSourceDisintegration.sourceStratumMeasure_map
        rate rewards C_star C_h t control0 i0]
    _ = _ := Measure.restrict_restrict_of_subset hSubset

theorem muEmpty_mass_original :
    muE Set.univ = BootstrapPrivateRoundStreams.sourceInputLaw p
      (originalEmptyEvent rate rewards C_star C_h q t s hs control0) := by
  calc
    muE Set.univ = ((muE).map
        (forgetEmpty rate rewards C_star C_h q t s hs control0)) Set.univ := by
      rw [Measure.map_apply
        (measurableEmbedding_forgetEmpty rate rewards C_star C_h q t s hs control0).measurable
        MeasurableSet.univ]
      simp
    _ = _ := by
      rw [muEmpty_map_original rate rewards C_star C_h q t s hs control0]
      simp [Measure.restrict_apply]

/-- Measurable embeddings transport arbitrary real functions, including nonintegrable ones. -/
theorem integral_originalEmpty (f : S → ℝ) :
    (∫ z : Ze, f z.val.val ∂muE) =
      ∫ omega in originalEmptyEvent rate rewards C_star C_h q t s hs control0,
        f omega ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let h := measurableEmbedding_forgetEmpty rate rewards C_star C_h q t s hs control0
  calc
    (∫ z : Ze, f (forgetEmpty rate rewards C_star C_h q t s hs control0 z) ∂muE) =
        ∫ omega, f omega ∂((muE).map
          (forgetEmpty rate rewards C_star C_h q t s hs control0)) := (h.integral_map f).symm
    _ = _ := by rw [muEmpty_map_original rate rewards C_star C_h q t s hs control0]

theorem integrableOn_originalEmpty_iff (f : S → ℝ) :
    IntegrableOn f (originalEmptyEvent rate rewards C_star C_h q t s hs control0)
        (BootstrapPrivateRoundStreams.sourceInputLaw p) ↔
      Integrable (fun z : Ze => f z.val.val) muE := by
  change Integrable f ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict
    (originalEmptyEvent rate rewards C_star C_h q t s hs control0)) ↔ _
  rw [← muEmpty_map_original rate rewards C_star C_h q t s hs control0]
  exact (measurableEmbedding_forgetEmpty
    rate rewards C_star C_h q t s hs control0).integrable_map_iff

theorem integrable_emptyPullback_Potential (v : ℕ) :
    Integrable (fun z : Ze => (ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h v) z.val.val) muE :=
  (integrableOn_originalEmpty_iff rate rewards C_star C_h q t s hs control0 _).mp
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
      rate rewards C_star C_h v).integrableOn

theorem integrable_emptyPullback_WeightedBacklog (v : ℕ) :
    Integrable (fun z : Ze => (ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt rate rewards C_star C_h v) z.val.val) muE :=
  (integrableOn_originalEmpty_iff rate rewards C_star C_h q t s hs control0 _).mp
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowWeightedBacklogAt
      rate rewards C_star C_h v).integrableOn

theorem integrable_emptyPullback_Backlog (j : Fin p.K) (v : ℕ) :
    Integrable (fun z : Ze => (ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt rate rewards C_star C_h j v) z.val.val) muE :=
  (integrableOn_originalEmpty_iff rate rewards C_star C_h q t s hs control0 _).mp
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowBacklogAt
      rate rewards C_star C_h j v).integrableOn

theorem integrable_emptyPullback_ExpBacklog (j : Fin p.K) (v : ℕ) :
    Integrable (fun z : Ze => ((fun omega => Real.exp (ReferenceFirstLiveSourceSavedMoments.beta rate *
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowBacklogAt
          rate rewards C_star C_h j v omega))) z.val.val) muE :=
  (integrableOn_originalEmpty_iff rate rewards C_star C_h q t s hs control0 _).mp
    (ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowExpBacklogAt
      rate rewards C_star C_h j v).integrableOn

section Baseline

variable (control1 : TimeControl p)

local notation "Ze1" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control1
local notation "switchEmpty" => (fun z : Ze =>
  (Subtype.mk (Subtype.val z) (Iff.mp (source_emptyBranch_control_independent
    rate rewards C_star C_h q t s hs control0 control1 (Subtype.val z)) (Subtype.property z)) : Ze1))

/-- Equality of actual optional selections gives both payload and complete start-result. -/
theorem empty_selection_data_control_independent (z : Ze) :
    ((ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z)).view.payload,
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control0
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z)).started) =
    ((ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control1
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control1 (switchEmpty z))).view.payload,
      (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control1
        (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control1 (switchEmpty z))).started) := by
  have h0 := ReferenceFirstLiveEmptyPendingMarkerLaw.original_selection_data
    rate rewards C_star C_h q t s hs control0 z
  have h1 := ReferenceFirstLiveEmptyPendingMarkerLaw.original_selection_data
    rate rewards C_star C_h q t s hs control1 (switchEmpty z)
  rw [originalCurrentRecord_control_independent
    rate rewards C_star C_h q t s hs control0 control1 z.val] at h0
  exact Option.some.inj (h0.symm.trans h1)

theorem selEmpty_payload_control_independent (z : Ze) :
    (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z)).view.payload =
    (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control1
      (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control1 (switchEmpty z))).view.payload :=
  congrArg Prod.fst (empty_selection_data_control_independent rate rewards C_star C_h q t s hs control0 control1 z)

theorem selEmpty_started_control_independent (z : Ze) :
    (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z)).started =
    (ReferenceFirstLiveEmptyPendingMarkerLaw.selEmpty rate rewards C_star C_h q t s hs control1
      (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control1 (switchEmpty z))).started :=
  congrArg Prod.snd (empty_selection_data_control_independent rate rewards C_star C_h q t s hs control0 control1 z)

theorem xiEmpty_control_independent (z : Ze) (j : Fin p.K) :
    ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z) j =
    ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control1
      (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control1 (switchEmpty z)) j := by
  unfold ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty
  rw [selEmpty_payload_control_independent rate rewards C_star C_h q t s hs control0 control1 z]

theorem actualEmptyMarker_control_independent (z : Ze) :
    ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker rate rewards C_star C_h q t s hs control0 z =
      ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker rate rewards C_star C_h q t s hs control1
        (switchEmpty z) := by
  unfold ReferenceFirstLiveEmptyPendingMarkerLaw.actualEmptyMarker
  rw [ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty_payload_eq,
    ReferenceFirstLiveEmptyPendingMarkerLaw.originalSelEmpty_payload_eq,
    selEmpty_payload_control_independent rate rewards C_star C_h q t s hs control0 control1 z,
    originalCurrentRecord_control_independent rate rewards C_star C_h q t s hs control0 control1 z.val]

end Baseline

section Phases

omit q s hs control0

/-- Six analytical sets of ORIGINAL sources. Every bounded lookup is an actual
record; the last phase includes the first-live exit and all later dates. -/
def sourcePhase (which : Fin 6) : Set S :=
  let cross := fun omega : S => (ReferenceCompletePhysicalHistory.generatedBoundary
    rate omega rewards C_star C_h).crossing.isSome = true
  let start := fun omega : S => ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
  let W := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
  match which.val with
  | 0 => {omega | (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing = none}
  | 1 => {omega | cross omega ∧ t.val < start omega}
  | 2 => {omega | cross omega ∧ t.val = start omega}
  | 3 => {omega | cross omega ∧ start omega < t.val ∧ ∃ hk : t.val - start omega < (W omega).length,
      match (ReferenceActivePhysicalStep.prepare ((W omega)[t.val - start omega]'hk).input).coordinator with
      | .live _ _ _ (.continuingChosen d _ _ _) => d.startResult.pending.Nonempty
      | _ => False}
  | 4 => {omega | cross omega ∧ start omega < t.val ∧ ∃ hk : t.val - start omega < (W omega).length,
      match (ReferenceActivePhysicalStep.prepare ((W omega)[t.val - start omega]'hk).input).coordinator with
      | .live _ _ _ (.continuingChosen d _ _ _) => d.startResult.pending = ∅
      | _ => False}
  | _ => {omega | cross omega ∧ start omega < t.val ∧ (W omega).length ≤ t.val - start omega}

/-- Actual selected-index and start membership, with no discarded exceptional source. -/
theorem source_actual_stratum (omega : S)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val) :
    omega ∈ ReferenceTotalSourcePairCoupling.sourceStratumEvent rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex
        (BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega) t
        (ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h) hstart) :=
  ⟨rfl, hc, rfl⟩

theorem source_phases_exhaustive (omega : S) :
    ∃ which : Fin 6, omega ∈ sourcePhase rate rewards C_star C_h t which := by
  classical
  let start := ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true
  · rcases lt_trichotomy t.val start with hfuture | hbirth | hpast
    · exact ⟨1, hc, hfuture⟩
    · exact ⟨2, hc, hbirth⟩
    · by_cases hexit : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega).length ≤ t.val - start
      · exact ⟨5, hc, hpast, hexit⟩
      · let q0 := BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega
        have hs0 : start ≤ t.val := hpast.le
        let z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q0 t start hs0) :=
          ⟨omega, source_actual_stratum rate rewards C_star C_h t omega hc hs0⟩
        let u := (omega.1.2 q0).2 t
        have hb := source_branches_of_positive_cell rate rewards C_star C_h q0 t start hs0 u z
          (by omega) (by change t.val - start <
            (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length; omega)
        rcases hb with hb | hb
        · obtain ⟨_, hn, htest⟩ := (source_nonempty_cell_iff
            rate rewards C_star C_h q0 t start hs0 u z).mp hb
          dsimp only [z] at hn htest
          refine ⟨3, hc, hpast, hn, ?_⟩
          cases hcoord : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
              rate rewards C_star C_h omega)[t.val - start]'hn).input).coordinator with
          | live r owned base outcome => cases outcome <;> simpa only [hcoord] using htest
          | _ => simpa only [hcoord] using htest
        · obtain ⟨_, hn, htest⟩ := (source_empty_cell_iff
            rate rewards C_star C_h q0 t start hs0 u z).mp hb
          dsimp only [z] at hn htest
          refine ⟨4, hc, hpast, hn, ?_⟩
          cases hcoord : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
              rate rewards C_star C_h omega)[t.val - start]'hn).input).coordinator with
          | live r owned base outcome => cases outcome <;> simpa only [hcoord] using htest
          | _ => simpa only [hcoord] using htest
  · have hn : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing <;> simp_all
    exact ⟨0, hn⟩

private theorem source_phases_disjoint_of_lt (i j : Fin 6) (hlt : i.val < j.val) :
    Disjoint (sourcePhase rate rewards C_star C_h t i) (sourcePhase rate rewards C_star C_h t j) := by
  classical
  apply Set.disjoint_left.mpr
  intro omega hi hj
  fin_cases i <;> fin_cases j <;> norm_num at hlt
  all_goals simp only [sourcePhase, Set.mem_ofPred_eq] at hi hj
  all_goals try omega
  all_goals try
    have hc := hj.1
    rw [hi] at hc
    cases hc
  all_goals try
    obtain ⟨_, _, hn, _⟩ := hi
    have he := hj.2.2
    omega
  all_goals
    obtain ⟨_, _, hni, hpi⟩ := hi
    obtain ⟨_, _, hnj, hpj⟩ := hj
    cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h omega)[t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate omega rewards C_star C_h]'hni).input).coordinator with
    | live r owned base outcome =>
        cases outcome with
        | continuingChosen d hsStart c arm =>
            have hp : d.startResult.pending.Nonempty := by simpa only [hc] using hpi
            have he : d.startResult.pending = ∅ := by simpa only [hc] using hpj
            exact Finset.not_nonempty_empty (he ▸ hp)
        | _ => simp only [hc] at hpi
    | _ => simp only [hc] at hpi

theorem source_phases_disjoint :
    Pairwise (fun i j => Disjoint (sourcePhase rate rewards C_star C_h t i)
      (sourcePhase rate rewards C_star C_h t j)) := by
  intro i j hij
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact source_phases_disjoint_of_lt rate rewards C_star C_h t i j hlt
  · exact (source_phases_disjoint_of_lt rate rewards C_star C_h t j i hgt).symm

private theorem source_phase_images (control : TimeControl p) :
    sourcePhase rate rewards C_star C_h t 3 =
      ⋃ q, ⋃ v : Fin (t.val + 1), ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control ∧
    sourcePhase rate rewards C_star C_h t 4 =
      ⋃ q, ⋃ v : Fin (t.val + 1), originalEmptyEvent
        rate rewards C_star C_h q t v.val (Nat.lt_succ_iff.mp v.isLt) control := by
  constructor
  all_goals
    ext omega
    simp only [Set.mem_iUnion]
    constructor
    · intro hp
      have hstart : ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h ≤ t.val := hp.2.1.le
      refine ⟨BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega, ⟨_, Nat.lt_succ_of_le hstart⟩, ?_⟩
      first | rw [mem_originalBranchEvent_physical_iff] | rw [mem_originalEmptyEvent_physical_iff]
      refine ⟨source_actual_stratum rate rewards C_star C_h t omega hp.1 hstart, Nat.sub_pos_of_lt hp.2.1, ?_⟩
      obtain ⟨hn, htest⟩ := hp.2.2
      refine ⟨hn, ?_⟩
      cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[t.val - ReferenceCompletePhysicalHistory.physicalStart
            rate omega rewards C_star C_h]'hn).input).coordinator with
      | live r owned base outcome => cases outcome <;> simpa only [hc] using htest
      | _ => simpa only [hc] using htest
    · rintro ⟨q, ⟨v, hv⟩, hmem⟩
      first | rw [mem_originalBranchEvent_physical_iff] at hmem | rw [mem_originalEmptyEvent_physical_iff] at hmem
      obtain ⟨hE, hpos, hn, htest⟩ := hmem
      have he : ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h = v := hE.2.2
      subst v
      refine ⟨hE.2.1, by
        change 0 < t.val - ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h at hpos
        change ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h < t.val
        omega, hn, ?_⟩
      cases hc : (ReferenceActivePhysicalStep.prepare ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h omega)[t.val - ReferenceCompletePhysicalHistory.physicalStart
            rate omega rewards C_star C_h]'hn).input).coordinator with
      | live r owned base outcome => cases outcome <;> simpa only [hc] using htest
      | _ => simpa only [hc] using htest

/-- Ambient Borel measurability, including zero, future and terminal launch strata. -/
theorem measurableSet_sourcePhase (control : TimeControl p) (which : Fin 6) :
    MeasurableSet (sourcePhase rate rewards C_star C_h t which) := by
  have h0 : MeasurableSet (sourcePhase rate rewards C_star C_h t 0) :=
    ReferenceCorrectedLaunchMeasurability.measurableSet_generated_no_crossing rate rewards C_star C_h
  have h1 : MeasurableSet (sourcePhase rate rewards C_star C_h t 1) := by
    have heq : sourcePhase rate rewards C_star C_h t 1 =
        ⋃ v : {v : ℕ // t.val < v}, {omega : S |
          (ReferenceCompletePhysicalHistory.generatedBoundary rate omega rewards C_star C_h).crossing.isSome = true ∧
          ReferenceCompletePhysicalHistory.physicalStart rate omega rewards C_star C_h = v.val} := by
      ext omega
      constructor
      · intro h
        exact Set.mem_iUnion.mpr ⟨⟨_, h.2⟩, h.1, rfl⟩
      · intro h
        obtain ⟨v, hc, he⟩ := Set.mem_iUnion.mp h
        exact ⟨hc, lt_of_lt_of_eq v.property he.symm⟩
    rw [heq]
    exact MeasurableSet.iUnion fun v =>
      ReferenceCorrectedLaunchMeasurability.measurableSet_generated_launch_start_fiber rate rewards C_star C_h v.val
  have h2 : MeasurableSet (sourcePhase rate rewards C_star C_h t 2) := by
    convert ReferenceCorrectedLaunchMeasurability.measurableSet_generated_launch_start_fiber
      rate rewards C_star C_h t.val using 1
    ext omega
    exact and_congr Iff.rfl eq_comm
  have h3 : MeasurableSet (sourcePhase rate rewards C_star C_h t 3) := by
    rw [(source_phase_images rate rewards C_star C_h t control).1]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun v =>
      ReferenceFirstLiveBranchIntegralTransport.measurableSet_originalBranchEvent _ _ _ _ q t v.val _ control
  have h4 : MeasurableSet (sourcePhase rate rewards C_star C_h t 4) := by
    rw [(source_phase_images rate rewards C_star C_h t control).2]
    exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun v =>
      measurableSet_originalEmptyEvent _ _ _ _ q t v.val _ control
  have hfirst : ∀ i : Fin 5, MeasurableSet (sourcePhase rate rewards C_star C_h t ⟨i.val, by omega⟩) := by
    intro i
    fin_cases i <;> assumption
  have hlast : sourcePhase rate rewards C_star C_h t 5 =
      (⋃ i : Fin 5, sourcePhase rate rewards C_star C_h t ⟨i.val, by omega⟩)ᶜ := by
    ext omega
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro h i hi
      exact Set.disjoint_left.mp (source_phases_disjoint rate rewards C_star C_h t
        (by intro he; have hv := congrArg Fin.val he; dsimp at hv; omega)) hi h
    · intro h
      obtain ⟨i, hi⟩ := source_phases_exhaustive rate rewards C_star C_h t omega
      have hiv : i.val = 5 := by
        by_contra hn
        exact h ⟨i.val, by have hlt := i.isLt; omega⟩ hi
      have hie : i = 5 := Fin.ext hiv
      exact hie ▸ hi
  fin_cases which
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact hlast.symm ▸ (MeasurableSet.iUnion hfirst).compl

/-- A genuine birth before the horizon has a real first physical cell. -/
theorem source_birth_window_pos (control : TimeControl p) (omega : S)
    (hbirth : omega ∈ sourcePhase rate rewards C_star C_h t 2) :
    0 < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h omega).length := by
  let q := BootstrapPrivateRoundStreams.sourceCoordinatorIndex p omega
  let z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) := ⟨omega, rfl, hbirth.1, hbirth.2.symm⟩
  have h := congrArg List.length (ReferenceFirstLiveCalendarPrefixReadout.firstWindowBirthCells_take_one
    rate rewards C_star C_h q t control z)
  simp only [List.length_take, List.length_singleton] at h
  have hlen := wholeFirstLiveCells_length rate rewards C_star C_h omega
  change min 1 (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h omega).length = 1 at h
  omega

end Phases

end Bandits.Support.ReferenceFirstLiveSourcePhasePartition
