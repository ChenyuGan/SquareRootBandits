/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalFirstBadStrictPrefix

/-!
# Original numerical prefixes on the first live window

The optional queue prefix is read from the same original complete suffix and
the actual first-live numerical cells.  A genuine initialization crossing,
including a terminal crossing, keeps its present empty prefix at length zero;
the absent-crossing branch remains absent.

The public results identify every first-live optional prefix and characterize
the inclusive overflow cutoff at each actual first-live date.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput)
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveOriginalNumericalPrefix

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "Source" => SourceInput p
local notation "Record" => ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
local notation "Cells" => RecordedQueueRun.RoundInput p.K
local notation "start" => ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart
  rate rewards C_star C_h
local notation "window" => ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
  rate rewards C_star C_h
local notation "cells" => ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
  rate rewards C_star C_h

private theorem crossing_of_nonempty_window (z : Source)
    (hn : 0 < (window z).length) :
    (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h with
  | none =>
      have hnil := ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hlaunch
      rw [hnil] at hn
      exact False.elim (Nat.not_lt_zero _ hn)
  | some active =>
      have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h).isSome = true := by rw [hlaunch]; rfl
      exact (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate z rewards C_star C_h).mp hsome

private theorem whole_cells_length_eq_window (z : Source)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true) :
    (cells z).length = (window z).length := by
  let sFin : Fin (p.T + 1) :=
    ⟨start z, Nat.lt_succ_of_le
      (ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h)⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber
      rate rewards C_star C_h sFin.val := ⟨z, hc, rfl⟩
  have hfiber := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
    rate rewards C_star C_h sFin x
  have hcells := congrArg List.length hfiber.2
  have hwindow := congrArg List.length hfiber.1
  change (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h z).length =
    (ReferenceFirstLiveSourceStoppedHandoverEndpoint.window
      rate rewards C_star C_h z).length
  rw [hcells, ReferenceFirstLiveOverflowReadout.firstLiveCells_length,
    ReferenceFirstLiveOverflowReadout.firstLiveLength, ← hwindow]
  rfl

private theorem original_window_cell_alignment (z : Source)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true)
    (k : Fin (window z).length) :
    ∃ c : Cells,
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]? =
          some ((window z)[k.val]) ∧
        ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 ((window z)[k.val]) = some c ∧
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 ((window z)[k.val]) = none ∧
        ReferenceFirstCollectionCurrentRetainedGate.cell0 rate ((window z)[k.val]) = some c ∧
        (cells z)[k.val]? = some c := by
  classical
  have hc' : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        z rewards C_star C_h rate)).crossing.isSome = true := by
    simpa [ReferenceCompletePhysicalHistory.generatedBoundary,
      ReferenceCompletePhysicalHistory.generatedInput] using hc
  let sFin : Fin (p.T + 1) :=
    ⟨start z, Nat.lt_succ_of_le
      (ReferenceCompletePhysicalHistory.physicalStart_le_T rate z rewards C_star C_h)⟩
  let x : ReferenceFirstLiveOverflowReadout.LaunchFiber
      rate rewards C_star C_h sFin.val := ⟨z, hc', rfl⟩
  let count := p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h
  let hspan := ReferenceCompleteFirstPhaseObservationRecovery.firstPhaseSpan
    rate rewards C_star C_h z
  let runWindow := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
    rate z rewards C_star C_h hc' count hspan
  let runCells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
    rate z rewards C_star C_h hc' count hspan
  have hrecords :=
    ReferenceCompleteFirstPhaseObservationRecovery.completeSuffixRecords_eq_actualFirstLiveRun
    rate rewards C_star C_h z hc'
  have hwindow : window z = runWindow := by
    change ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h) =
      ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun rate z rewards C_star C_h
          hc count hspan).records
    exact congrArg ReferenceFirstLiveConfirmationHistory.firstLiveWindow hrecords
  have hwholeCells : cells z = runCells := by
    have hfiber := ReferenceFirstLiveOverflowReadout.wholeFirstLive_on_fiber
      rate rewards C_star C_h sFin x
    change ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z = runCells
    rw [hfiber.2]
    change ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z rewards C_star C_h
        (ReferenceFirstLiveOverflowReadout.launch_crossing rate rewards C_star C_h sFin.val x)
        count
        (ReferenceFirstLiveOverflowReadout.launch_span rate rewards C_star C_h sFin.val count
          (ReferenceFirstLiveOverflowReadout.maximal_span sFin) x) = runCells
    have hlaunchCrossing : ReferenceFirstLiveOverflowReadout.launch_crossing
        rate rewards C_star C_h sFin.val x = hc' := Subsingleton.elim _ _
    have hlaunchSpan : ReferenceFirstLiveOverflowReadout.launch_span
        rate rewards C_star C_h sFin.val count
          (ReferenceFirstLiveOverflowReadout.maximal_span sFin) x = hspan :=
      Subsingleton.elim _ _
    rw [hlaunchCrossing, hlaunchSpan]
  have hraw := ReferenceCompleteFirstPhaseObservationRecovery.actualFirstLiveRawObservationIdentity
    rate rewards C_star C_h z hc'
  obtain ⟨seed, hstart, hrawCells⟩ := hraw
  let j : Fin runWindow.length := ⟨k.val, by rw [← hwindow]; exact k.isLt⟩
  have hgetWindow : (window z)[k.val] = runWindow[j.val] := by
    have h := congrArg (fun xs : List Record => xs[k.val]?) hwindow
    have hk : k.val < (window z).length := k.isLt
    have hj : k.val < runWindow.length := j.isLt
    simp only [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hj] at h
    exact Option.some.inj h
  obtain ⟨_, _, _, _, _, _, hLive, hCollection, _, _, _, _, _, _, _, _⟩ := hrawCells j
  have hactual := ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
    rate rewards C_star C_h z k
  have htime := hactual.1
  have hlookup := hactual.2
  have hstartLe : ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h ≤ (window z)[k.val].input.time.val := by
    have htime' : (window z)[k.val].input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
      simpa only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using htime
    rw [htime']
    omega
  have hindex : (window z)[k.val].input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k.val := by
    have htime' : (window z)[k.val].input.time.val =
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val := by
      simpa only [ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using htime
    omega
  have hrecord :
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[k.val]? =
        some ((window z)[k.val]) := by
    unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hlookup
    rw [ite_eq_left hstartLe, hindex] at hlookup
    exact hlookup
  have hVbound : k.val < (cells z).length := by
    rw [whole_cells_length_eq_window rate rewards C_star C_h z hc]
    exact k.isLt
  have hrunBound : j.val < runCells.length := by
    change j.val < (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate z rewards C_star C_h hc' count hspan).length
    rw [ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate z rewards C_star C_h hc' count hspan]
    change j.val < runWindow.length
    exact j.isLt
  have hcellV : (cells z)[k.val]? = some (runCells[j.val]'hrunBound) := by
    have hh := congrArg (fun xs : List Cells => xs[k.val]?) hwholeCells
    have hrunBound' : k.val < runCells.length := by simpa [j] using hrunBound
    rw [List.getElem?_eq_getElem hrunBound'] at hh
    simpa [j] using hh
  refine ⟨runCells[j.val]'hrunBound, ?_, ?_, ?_, ?_, ?_⟩
  · exact hrecord
  · rw [hgetWindow]
    exact hLive
  · rw [hgetWindow]
    exact hCollection
  · rw [hgetWindow]
    rw [ReferenceFirstCollectionCurrentRetainedGate.cell0, hLive, hCollection]
    simp only [Option.or_none]
    dsimp [runCells, count, hspan]
  · exact hcellV

private theorem prefixInputs_on_crossing (z : Source)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true) :
    ∀ h, h ≤ (window z).length →
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (start z + h) z = some ((cells z).take h) := by
  intro h
  induction h with
  | zero =>
      intro _
      have hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h (start z) z := ⟨hc, le_rfl⟩
      have hlaunch' : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h (start z + 0) z := by simpa using hlaunch
      rw [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
        ite_eq_left hlaunch']
      have hstartEq : start z =
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := rfl
      have hsub : start z + 0 -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = 0 := by
        rw [hstartEq]
        omega
      change (((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h).take
        ((start z + 0) - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h)).map
          (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate)).mapM id =
        some ((cells z).take 0)
      rw [hsub]
      simp only [List.take_zero, List.map_nil, List.mapM_nil]
      rfl
  | succ h ih =>
      intro hle
      have hprevBound : h ≤ (window z).length := by omega
      have hprev := ih hprevBound
      have hk : h < (window z).length := by omega
      let k : Fin (window z).length := ⟨h, hk⟩
      obtain ⟨c, hr, _, _, hcell, hcellV⟩ := original_window_cell_alignment
        rate rewards C_star C_h z hc k
      have hindex : start z + h -
          ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = h := by
        change start z + h - start z = h
        omega
      have hr' :
          (ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceRecords
            rate rewards C_star C_h z)[(start z + h) -
              ReferenceFirstCollectionCorrectedSliceNumericalPrefix.sourceStart
                rate rewards C_star C_h z]? = some ((window z)[h]) := by
        change (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
          (start z + h) - ReferenceCompletePhysicalHistory.physicalStart
            rate z rewards C_star C_h]? = some ((window z)[h])
        rw [hindex]
        simpa [k] using hr
      have hcellBound : h < (cells z).length := by
        rw [whole_cells_length_eq_window rate rewards C_star C_h z hc]
        exact hk
      have hnext := ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs_append_one
        rate rewards C_star C_h (start z + h) z ((cells z).take h) hprev
        ((window z)[h]) c hr' hcell
      have htake : (cells z).take (h + 1) = (cells z).take h ++ [(cells z)[h]] :=
        List.take_succ_eq_append_getElem (l := cells z) (i := h) (h := hcellBound)
      rw [show start z + (h + 1) = (start z + h) + 1 by omega, hnext]
      have hcellValue : (cells z)[h]'hcellBound = c := by
        have hcellValue' : (cells z)[h]? = some c := by simpa [k] using hcellV
        rw [List.getElem?_eq_getElem hcellBound] at hcellValue'
        exact Option.some.inj hcellValue'
      rw [← hcellValue]
      exact congrArg some htake.symm

/-- The crossing branch keeps the present initial queue, including its empty
length-zero prefix; the no-crossing branch stays absent. -/
public theorem prefixInputs_firstLiveWindow (z : Source) (h : ℕ)
    (hle : h ≤ (window z).length) :
    ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs
        rate rewards C_star C_h (start z + h) z =
      if _hc : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate z rewards C_star C_h).crossing.isSome = true then
        some ((cells z).take h)
      else none := by
  classical
  by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true
  · rw [dite_eq_left hc]
    exact prefixInputs_on_crossing rate rewards C_star C_h z hc h hle
  · have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate z rewards C_star C_h = none := by
      cases hx : ReferenceCorrectedInitializationLaunch.correctedLaunch
          rate z rewards C_star C_h with
      | none => rfl
      | some active =>
          have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
              rate z rewards C_star C_h).isSome = true := by rw [hx]; rfl
          have := (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
            rate z rewards C_star C_h).mp hsome
          exact (hc this).elim
    have hwindow : window z = [] :=
      ReferenceFirstLiveSourceStoppedHandoverEndpoint.window_eq_nil_of_no_launch
        rate rewards C_star C_h z hlaunch
    have hs : start z = p.T :=
      ReferenceCompletePhysicalHistory.correctedLaunch_none_start_eq_T
        rate z rewards C_star C_h hlaunch
    have hzero : h = 0 := by rw [hwindow, List.length_nil] at hle; exact Nat.eq_zero_of_le_zero hle
    subst h
    simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs,
      ReferenceSourcePrefixHistoryFiltration.actualLaunchBy, hs, hc]

private theorem prefixReadout_overflow_iff (z : Source)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate z rewards C_star C_h).crossing.isSome = true)
    (h : ℕ) (hh : h ≤ (window z).length) :
    (∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
      ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
        rate rewards C_star C_h (start z + h) z = some o ∧
      ∃ a : Fin p.K,
        ((o.1 a).2 : ℝ) /
          ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
            1 / (32 * rate.eta.val)) ↔
      UnstoppedRecordedQueueComparison.firstOverflowPrefix
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cells z) ≤ h := by
  let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
  let X := cells z
  let state := RecordedQueueRun.run Q (X.take h)
  have hlength : X.length = (window z).length :=
    whole_cells_length_eq_window rate rewards C_star C_h z hc
  have hbound : h ≤ X.length := by rw [hlength]; exact hh
  have hinputs := prefixInputs_firstLiveWindow rate rewards C_star C_h z h hh
  rw [dite_eq_left hc] at hinputs
  have hread : ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
      rate rewards C_star C_h (start z + h) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state) := by
    simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
      hinputs, state, X, Q]
  have hthreshold :
      (∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
        ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
          rate rewards C_star C_h (start z + h) z = some o ∧
        ∃ a : Fin p.K,
          ((o.1 a).2 : ℝ) / (Q.n : ℝ) > 1 / (32 * rate.eta.val)) ↔
      state.overflow = true := by
    rw [hread]
    constructor
    · rintro ⟨o, ho, a, ha⟩
      have heq : o =
          ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state :=
        Option.some.inj ho.symm
      subst o
      have hnormalized :
          ((state.registers a).2 : ℝ) / (Q.n : ℝ) > 1 / (32 * Q.eta) := by
        simpa [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
          Q, ReferenceFirstLaunchNumericalCell.queueParameters] using ha
      apply (RecordedQueueRun.run_overflow_iff_cutoff Q (X.take h)).2
      refine ⟨a, ?_⟩
      exact (RecordedQueueRun.overflowCutoff_iff Q (state.registers a).2).mp hnormalized
    · intro hover
      obtain ⟨a, ha⟩ :=
        (RecordedQueueRun.run_overflow_iff_cutoff Q (X.take h)).mp hover
      refine ⟨ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout state,
        rfl, a, ?_⟩
      have hnormalized :=
        (RecordedQueueRun.overflowCutoff_iff Q (state.registers a).2).mpr ha
      simpa [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
        Q, ReferenceFirstLaunchNumericalCell.queueParameters] using hnormalized
  have hstate : state.overflow = true ↔
      UnstoppedRecordedQueueComparison.firstOverflowPrefix Q X ≤ h := by
    change (RecordedQueueRun.run Q (X.take h)).overflow = true ↔ _
    exact UnstoppedRecordedQueueComparison.prefix_overflow_iff_first_overflow_prefix_le
      Q X h hbound
  exact hthreshold.trans hstate

/-- The first detecting update is retained in its `κ`th prefix; the following
one-based calendar boundary is the excluded overflow cutoff. -/
public theorem overflowCutoff_iff_not_numericalOverflowBy
    (z : Source) (k : Fin (window z).length) :
    (window z)[k.val].input.time.val + 1 <
        ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
          rate rewards C_star C_h z ↔
      ¬ ReferenceCompleteInclusivePhysicalDecoderErrors.numericalOverflowBy
        rate rewards C_star C_h (window z)[k.val].input.time z := by
  let t := (window z)[k.val].input.time
  have hc := crossing_of_nonempty_window rate rewards C_star C_h z
    (Nat.zero_lt_of_lt k.isLt)
  have hCellsLength := whole_cells_length_eq_window rate rewards C_star C_h z hc
  have hcalendar : t.val = start z + k.val := by
    simpa [t, ReferenceFirstLiveSourceStoppedReleaseEndpoint.physicalStart] using
      (ReferenceFirstLiveSourceStoppedHandoverEndpoint.source_window_record_calendar
        rate rewards C_star C_h z k).1
  let κ := UnstoppedRecordedQueueComparison.firstOverflowPrefix
    (ReferenceFirstLaunchNumericalCell.queueParameters rate) (cells z)
  have hnumerical :
      ReferenceCompleteInclusivePhysicalDecoderErrors.numericalOverflowBy
        rate rewards C_star C_h t z ↔ κ ≤ k.val := by
    constructor
    · rintro ⟨n, hnt, o, ho, a, ha⟩
      by_cases hbefore : n < start z
      · have hnotLaunch : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
            rate rewards C_star C_h n z := by
          intro hlaunch
          exact Nat.not_le_of_gt hbefore hlaunch.2
        have hnone :
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
              rate rewards C_star C_h n z = none := by
          simp [ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixInputs, hnotLaunch]
        rw [hnone] at ho
        cases ho
      · have hstart : start z ≤ n := Nat.le_of_not_gt hbefore
        let j := n - start z
        have hj : j ≤ k.val := by
          dsimp [j]
          rw [hcalendar] at hnt
          omega
        have hjWindow : j ≤ (window z).length := le_trans hj k.isLt.le
        have hlocal := prefixReadout_overflow_iff rate rewards C_star C_h z hc j hjWindow
        have hjDate : start z + j = n := by dsimp [j]; omega
        have hreadLocal :
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
              rate rewards C_star C_h (start z + j) z = some o := by
          simpa only [hjDate] using ho
        have hcross := hlocal.mp ⟨o, hreadLocal, a, ha⟩
        change κ ≤ j at hcross
        omega
    · intro hcross
      have hlocal := prefixReadout_overflow_iff rate rewards C_star C_h z hc
        k.val (Nat.le_of_lt k.isLt)
      have hthreshold :
          ∃ o : ReferenceFirstCollectionCurrentQueueReadout.QueueReadout p.K,
            ReferenceFirstCollectionCorrectedSliceNumericalPrefix.prefixReadout
              rate rewards C_star C_h (start z + k.val) z = some o ∧
            ∃ a : Fin p.K,
              ((o.1 a).2 : ℝ) /
                ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) >
                  1 / (32 * rate.eta.val) := by
        exact hlocal.mpr (by change κ ≤ k.val; exact hcross)
      rcases hthreshold with ⟨o, ho, a, ha⟩
      refine ⟨t.val, le_rfl, o, ?_, a, ha⟩
      simpa only [← hcalendar] using ho
  have hnoNumerical :
      ¬ ReferenceCompleteInclusivePhysicalDecoderErrors.numericalOverflowBy
        rate rewards C_star C_h t z ↔ k.val < κ := by
    rw [hnumerical]
    omega
  have hwholeCellsLength : ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength
      rate rewards C_star C_h z = (window z).length := rfl
  have hwholePrefix : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowPrefix
      rate rewards C_star C_h z = κ := rfl
  have hoverflowRound : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
      rate rewards C_star C_h z =
        if κ ≤ (cells z).length then some (start z + κ) else none := by
    unfold ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
    rw [hwholePrefix, hwholeCellsLength, ← hCellsLength]
    rfl
  have hcutoff :
      t.val + 1 < ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
        rate rewards C_star C_h z ↔ k.val < κ := by
    by_cases hcross : κ ≤ (cells z).length
    · have hround : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
          rate rewards C_star C_h z = some (start z + κ) := by
        rw [hoverflowRound, ite_eq_left hcross]
      have hexcluded : ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
          rate rewards C_star C_h z = min (p.T + 1) (start z + κ + 1) := by
        unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
        rw [hround]
        rfl
      rw [hexcluded, lt_min_iff, hcalendar]
      omega
    · have hround : ReferenceFirstLiveOverflowReadout.wholeFirstLiveOverflowRound
          rate rewards C_star C_h z = none := by
        rw [hoverflowRound, ite_eq_right hcross]
      have hexcluded : ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
          rate rewards C_star C_h z = p.T + 1 := by
        unfold ReferenceFirstLiveSourceStoppedReleaseEndpoint.overflowFirstExcluded
        rw [hround]
        rfl
      rw [hexcluded]
      have hkLength : k.val < (cells z).length := by rw [hCellsLength]; exact k.isLt
      omega
  simpa only [t] using hcutoff.trans hnoNumerical.symm

end Bandits.Support.ReferenceFirstLiveOriginalNumericalPrefix
