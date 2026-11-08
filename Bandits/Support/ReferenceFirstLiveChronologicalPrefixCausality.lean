/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveChronologicalPrefixFoundation

/-!
# Calendar-past observations of the first-live logical prefix

The observation below retains every field of each accepted logical cell. Its
cutoff is the cell's actual calendar time, so a launch after round one does
not turn the calendar cutoff into a positional `take` count.

Sources: `sources/zip4/manuscript/06_interruptions.tex:381-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:142-215,323-366`, and
`sources/zip4/manuscript/08_main_theorem.tex:78-109`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality

open ReferenceFirstLiveChronologicalPrefixFoundation

variable {p : Parameters}

/-- The complete cells of the canonical first-live path strictly before an
actual calendar time. This retains the original physical code, all numerical
real fields, the complete queue registers, and every finite logical field. -/
def calendarPast (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (input : SourceInput p × AuxiliaryArray p) (n : ℕ) :
    List (LogicalCell p rate) :=
  (firstLiveChronologicalPrefix rate rewards C_star C_h input).takeWhile
    (fun cell => cell.time.val < n)

private theorem takeWhile_eq_take_length {α : Type*} (predicate : α → Bool)
    (values : List α) :
    values.takeWhile predicate = values.take (values.takeWhile predicate).length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases hpredicate : predicate head
      · have hneg : ¬ predicate head := by simp [hpredicate]
        simp only [List.takeWhile_cons_of_neg hneg, List.length_nil, List.take_zero]
      · have hpos : (head :: tail).takeWhile predicate = head :: tail.takeWhile predicate :=
          List.takeWhile_cons_of_pos hpredicate
        calc
          _ = head :: tail.takeWhile predicate := hpos
          _ = head :: tail.take (tail.takeWhile predicate).length :=
            congrArg (List.cons head) ih
          _ = (head :: tail).take ((head :: tail).takeWhile predicate).length := by
            rw [hpos, List.length_cons, List.take_succ_cons]

private theorem takeWhile_length_map_eq {α β : Type*} (f : α → β)
    (predicate : β → Bool) (left right : List α)
    (h : left.map f = right.map f) :
    (left.takeWhile (fun value => predicate (f value))).length =
      (right.takeWhile (fun value => predicate (f value))).length := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at h
  | cons head tail ih =>
      cases right with
      | nil => simp at h
      | cons otherHead otherTail =>
          have hhead : f head = f otherHead := by
            injection h with hhead _
          have htail : tail.map f = otherTail.map f := by
            injection h with _ htail
          simp only [List.takeWhile_cons]
          rw [hhead]
          cases hpredicate : predicate (f otherHead)
          · simp
          · simp [ih otherTail htail]

/-- At each index, the logical cell keeps the original record's actual
calendar time. This is the pointwise connection from the same accepted
constructor to its chronological physical window. -/
theorem firstLiveChronologicalPrefix_cellTime
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (aux : AuxiliaryArray p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    ((firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux))[k.val]'(by
      rw [firstLiveChronologicalPrefix_length]
      simpa only [ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using k.isLt)).time =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val].input.time := by
  have hget := firstLiveChronologicalPrefix_get rate rewards C_star C_h source aux k
  simpa only [appendLogicalCell] using congrArg LogicalCell.time hget

private theorem firstLiveChronologicalPrefix_time_map_eq
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (left right : AuxiliaryArray p) :
    (firstLiveChronologicalPrefix rate rewards C_star C_h (source, left)).map
        (fun cell => cell.time) =
      (firstLiveChronologicalPrefix rate rewards C_star C_h (source, right)).map
        (fun cell => cell.time) := by
  apply List.ext_getElem
  · rw [List.length_map, firstLiveChronologicalPrefix_length,
      List.length_map, firstLiveChronologicalPrefix_length]
  · intro k hleft hright
    have hk : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := by
      have hleft' : k <
          (firstLiveChronologicalPrefix rate rewards C_star C_h (source, left)).length := by
        simpa only [List.length_map] using hleft
      simpa only [firstLiveChronologicalPrefix_length,
        ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hleft'
    let index : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source).length := ⟨k, hk⟩
    simp only [List.getElem_map]
    exact (firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h
      source left index).trans
        (firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h
          source right index).symm

/-- The calendar-past length is determined by the source calendar, not by
the auxiliary array. The comparison uses only the time projection of the
same canonical path. -/
theorem calendarPast_length_auxiliary_ext
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (left right : AuxiliaryArray p) (n : ℕ) :
    (calendarPast rate rewards C_star C_h (source, left) n).length =
      (calendarPast rate rewards C_star C_h (source, right) n).length := by
  unfold calendarPast
  exact takeWhile_length_map_eq LogicalCell.time
    (fun time : Fin p.T => decide (time.val < n)) _ _
      (firstLiveChronologicalPrefix_time_map_eq rate rewards C_star C_h
        source left right)

/-- The calendar-past observation is exactly the initial segment selected by
its actual-time cutoff. The endpoint is the observed past length, not the
calendar time itself. -/
theorem calendarPast_eq_take_length
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (input : SourceInput p × AuxiliaryArray p) (n : ℕ) :
    calendarPast rate rewards C_star C_h input n =
      (firstLiveChronologicalPrefix rate rewards C_star C_h input).take
        (calendarPast rate rewards C_star C_h input n).length := by
  exact takeWhile_eq_take_length _ _

/-- Replacing auxiliary coordinates at calendar times outside the observed
past leaves the complete past-cell list unchanged. No coordinate at an
unused later time is consumed by this readout. -/
theorem calendarPast_auxiliary_ext
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (left right : AuxiliaryArray p) (n : ℕ)
    (hused : ∀ t : Fin p.T, t.val < n → left (t, 1) = right (t, 1)) :
    calendarPast rate rewards C_star C_h (source, left) n =
      calendarPast rate rewards C_star C_h (source, right) n := by
  let leftPath := firstLiveChronologicalPrefix rate rewards C_star C_h (source, left)
  let rightPath := firstLiveChronologicalPrefix rate rewards C_star C_h (source, right)
  let window := ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h source
  let count := (calendarPast rate rewards C_star C_h (source, left) n).length
  have hcount : (calendarPast rate rewards C_star C_h (source, right) n).length = count :=
    (calendarPast_length_auxiliary_ext rate rewards C_star C_h source left right n).symm
  have htakeLeft : calendarPast rate rewards C_star C_h (source, left) n =
      leftPath.take count := by
    exact calendarPast_eq_take_length rate rewards C_star C_h (source, left) n
  have htakeRight : calendarPast rate rewards C_star C_h (source, right) n =
      rightPath.take count := by
    have htake := calendarPast_eq_take_length
      rate rewards C_star C_h (source, right) n
    rw [hcount] at htake
    simpa only [rightPath] using htake
  have hpathLen : leftPath.length = window.length := by
    simp only [leftPath, window, firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength]
  have hcountLe : count ≤ window.length := by
    have hle : count ≤ leftPath.length := by
      unfold count calendarPast leftPath
      exact (List.takeWhile_prefix _).length_le
    rw [hpathLen] at hle
    exact hle
  by_cases hshort : count < window.length
  · have htake := firstLiveChronologicalPrefix_take_auxiliary_ext
      rate rewards C_star C_h source left right count hshort
    calc
      calendarPast rate rewards C_star C_h (source, left) n = leftPath.take count := htakeLeft
      _ = rightPath.take count := by
        simpa only [leftPath, rightPath] using htake
      _ = calendarPast rate rewards C_star C_h (source, right) n := htakeRight.symm
  · have hwhole : count = window.length := by omega
    by_cases hnonempty : 0 < window.length
    · let last : Fin window.length := ⟨window.length - 1, by omega⟩
      have hlastInPast :
          leftPath[last.val]'(by simpa only [leftPath, hpathLen] using last.isLt) ∈
            calendarPast rate rewards C_star C_h (source, left) n := by
        have hbound : last.val < leftPath.length := by omega
        have htakeFull : leftPath.take window.length = leftPath := by
          rw [← hpathLen, List.take_length]
        rw [htakeLeft, hwhole, htakeFull]
        exact List.getElem_mem hbound
      change leftPath[last.val]'(by simpa only [hpathLen] using last.isLt) ∈
          leftPath.takeWhile (fun cell => decide (cell.time.val < n)) at hlastInPast
      have hlastTime :
          (leftPath[last.val]'(by simpa only [leftPath, hpathLen] using last.isLt)).time.val < n :=
        of_decide_eq_true (List.mem_takeWhile_imp
          (p := fun cell : LogicalCell p rate => decide (cell.time.val < n))
          (l := leftPath) hlastInPast)
      have htimeRecord :
          (leftPath[last.val]'(by simpa only [leftPath, hpathLen] using last.isLt)).time =
            window[last.val].input.time := by
        simpa only [leftPath, window] using
          firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h source left last
      have hscalar : left (window[last.val].input.time, 1) =
          right (window[last.val].input.time, 1) :=
        hused window[last.val].input.time (by rw [← htimeRecord]; exact hlastTime)
      have hlast : last.val + 1 = window.length := by
        simp only [last]
        omega
      have hpath := firstLiveChronologicalPrefix_last_auxiliary_ext
        rate rewards C_star C_h source left right last hlast hscalar
      calc
        calendarPast rate rewards C_star C_h (source, left) n = leftPath.take count := htakeLeft
        _ = rightPath.take count := by
          simpa only [leftPath, rightPath] using
            congrArg (fun path : List (LogicalCell p rate) => path.take count) hpath
        _ = calendarPast rate rewards C_star C_h (source, right) n := htakeRight.symm
    · have hcountZero : count = 0 := by omega
      have hleftZero : calendarPast rate rewards C_star C_h (source, left) n = [] :=
        List.eq_nil_iff_length_eq_zero.mpr hcountZero
      have hrightZero : calendarPast rate rewards C_star C_h (source, right) n = [] :=
        List.eq_nil_iff_length_eq_zero.mpr (by omega)
      rw [hleftZero, hrightZero]

private theorem takeWhile_calendar_eq_take {α : Type*} (time : α → ℕ)
    (values : List α) (start n : ℕ)
    (htime : ∀ k (hk : k < values.length), time values[k] = start + k) :
    values.takeWhile (fun value => decide (time value < n)) = values.take (n - start) := by
  induction values generalizing start with
  | nil => simp only [List.takeWhile_nil, List.take_nil]
  | cons head tail ih =>
      have hhead : time head = start := htime 0 (by simp)
      have htail : ∀ k (hk : k < tail.length), time tail[k] = (start + 1) + k := by
        intro k hk
        have h := htime (k + 1) (by simpa using Nat.succ_lt_succ hk)
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 k] using h
      by_cases hstart : start < n
      · have hcount : n - start = (n - (start + 1)) + 1 := by omega
        rw [List.takeWhile_cons_of_pos (by simpa only [hhead, decide_eq_true_eq] using hstart),
          hcount, List.take_succ_cons, ih (start + 1) htail]
      · have hcount : n - start = 0 := by omega
        rw [List.takeWhile_cons_of_neg (by simpa only [hhead, decide_eq_true_eq] using hstart),
          hcount, List.take_zero]

private theorem wholeWindow_time (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (k : ℕ) (hk : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k]).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h + k := by
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hp : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).IsPrefix records := List.takeWhile_prefix _
  have hkR : k < records.length := hk.trans_le hp.length_le
  have helem := congrArg (fun values : List ℕ => values[k]?)
    (ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate source rewards C_star C_h)
  have hcalendar : k < (ReferenceActivePhysicalHorizon.calendar
      (ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)).length := by
    simpa only [ReferenceActivePhysicalHorizon.calendar, List.length_range',
      records, ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hkR
  rw [List.getElem?_eq_getElem (by simpa using hkR), List.getElem_map,
    List.getElem?_eq_getElem hcalendar] at helem
  have hvalue := Option.some.inj helem
  rw [hp.getElem hk]
  simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem_range',
    Nat.one_mul] using hvalue

/-- The calendar cutoff is a positional count only after subtracting the
actual launch offset. Future cutoff decisions need not be predictable. -/
theorem calendarPast_eq_take_elapsed
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (aux : AuxiliaryArray p) (n : ℕ) :
    calendarPast rate rewards C_star C_h (source, aux) n =
      (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux)).take
        (n - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  apply takeWhile_calendar_eq_take (fun cell : LogicalCell p rate => cell.time.val)
  intro k hk
  have hkW : k < (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length := by
    simpa only [firstLiveChronologicalPrefix_length,
      ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
  rw [firstLiveChronologicalPrefix_cellTime rate rewards C_star C_h source aux ⟨k, hkW⟩]
  exact wholeWindow_time rate rewards C_star C_h source k hkW

private theorem actualRecord_fields (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T) (source : SourceInput p) (r : Record rate)
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source = some r) :
    r.input.rows = source.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val source
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate source rewards C_star C_h hz.1
    have hrec := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
      rate rewards C_star C_h t source _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [ReferenceSourcePrefixHistoryFiltration.actualRecord_eq_none_of_not_launchBy
      rate rewards C_star C_h t source hz] at hr
    cases hr

/-- Complete actual physical record codes before the calendar cutoff factor
through the literal selected-control prefix, including absent records. -/
theorem actualRecord_code_sourcePrefix
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (source : SourceInput p) (t : Fin p.T) (ht : t.val < n) :
    (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t source).map
        ReferenceActiveHorizonMeasurability.roundRecordCode =
      (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)).map
        ReferenceActiveHorizonMeasurability.roundRecordCode := by
  open ReferenceSourcePrefixHistoryFiltration in
  have hincoming : incoming rate rewards C_star C_h t source =
      incoming rate rewards C_star C_h t (sourcePrefix control0 n source) := by
    rw [incoming_factor rate rewards C_star C_h control0 t source,
      incoming_factor rate rewards C_star C_h control0 t (sourcePrefix control0 n source),
      sourcePrefix_sourcePrefix control0 t.val n (by omega)]
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t source with
  | none =>
      cases hs : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) with
      | none => rfl
      | some s =>
          simp only [ReferenceSourcePrefixHistoryFiltration.incoming,
            hr, hs, Option.map_none, Option.map_some] at hincoming
          cases hincoming
  | some r =>
      cases hs : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) with
      | none =>
          simp only [ReferenceSourcePrefixHistoryFiltration.incoming,
            hr, hs, Option.map_none, Option.map_some] at hincoming
          cases hincoming
      | some s =>
          have hstate : r.input.state = s.input.state := by
            apply ReferenceActivePhysicalStepMeasurability.encodeState_injective
            exact Option.some.inj (by
              simpa only [ReferenceSourcePrefixHistoryFiltration.incoming, hr, hs,
                Option.map_some] using hincoming)
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_fields rate rewards C_star C_h t source r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_fields rate rewards C_star C_h t _ s hs
          have hsel : r.input.selected = s.input.selected := by
            rw [hselected, hselected', ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected]
          have hcurrent : r.input.row.2 r.input.time = s.input.row.2 s.input.time := by
            dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
            rw [hrows, hrows', hselected, hselected', htime, htime',
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left ht]
          have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
              (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
                (s.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
            intro v hv
            dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
            rw [hrows, hrows', hselected, hselected',
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
              ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control, ite_eq_left (by rw [htime] at hv; omega)]
          have hcode := ReferenceInspectedPastRoundObservations.roundRecordCode_eq_of_temporal_reads
            r.input s.input hstate hsel (htime.trans htime'.symm)
            (hrewards.trans hrewards'.symm) hcurrent hpast
          exact congrArg some hcode

private theorem wholeWindow_actualRecord (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val]).input.time source =
      some ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
        rate rewards C_star C_h source)[k.val]) := by
  have htime := wholeWindow_time rate rewards C_star C_h source k.val k.isLt
  have hp : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).IsPrefix
      (ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h) :=
    List.takeWhile_prefix _
  rw [ReferenceSourcePrefixHistoryFiltration.actualRecord, ite_eq_left (by omega)]
  have hindex : ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k.val]).input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = k.val := by
    omega
  rw [hindex, List.getElem?_eq_getElem (k.isLt.trans_le hp.length_le), hp.getElem k.isLt]

private theorem selected_view_eq_of_code {rate : RateInput p} (r s : Record rate)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode r =
      ReferenceActiveHorizonMeasurability.roundRecordCode s) :
    a.selected.view = b.selected.view := by
  have h := congrArg (fun code : ReferenceActiveHorizonMeasurability.RoundRecordCode
      (p := p) (rate := rate) => code.2.2.1.1) hcode
  change (ReferenceActiveStepCompositionMeasurability.wholeStepCode r.input).1.1 =
    (ReferenceActiveStepCompositionMeasurability.wholeStepCode s.input).1.1 at h
  rw [(ReferenceActiveStepCompositionMeasurability.wholeStepCode_front r.input).1,
    (ReferenceActiveStepCompositionMeasurability.wholeStepCode_front s.input).1] at h
  have ha : (ReferenceActivePhysicalStep.dispatch r.input).selection = some a.selected := by
    simpa only [r.output_eq, ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.prepare] using a.selection_actual
  have hb : (ReferenceActivePhysicalStep.dispatch s.input).selection = some b.selected := by
    simpa only [s.output_eq, ReferenceActivePhysicalStep.step,
      ReferenceActivePhysicalStep.prepare] using b.selection_actual
  rw [ha, hb, Option.map_some, Option.map_some] at h
  exact congrArg Prod.fst (Option.some.inj h)

private theorem appendLogicalCell_temporal_congr {rate : RateInput p} (r s : Record rate)
    (a : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell r)
    (b : ReferenceFirstWindowNumericalStream.ActualLiveSourceCell s)
    (state : RecordedQueueRun.RunState p.K) (aux : AuxiliaryArray p)
    (htime : r.input.time = s.input.time)
    (hcode : ReferenceActiveHorizonMeasurability.roundRecordCode r =
      ReferenceActiveHorizonMeasurability.roundRecordCode s)
    (hinput : a.input = b.input)
    (hcurrent : r.input.row.2 r.input.time = s.input.row.2 s.input.time) :
    appendLogicalCell r a state aux = appendLogicalCell s b state aux := by
  have hview := selected_view_eq_of_code r s a b hcode
  have hproposal : FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      r.input.row r.input.time = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
      s.input.row s.input.time := by
    unfold FollowerCutoffScan.completeRowProposalBit CompletePublicTable.completeRowLearning
    rw [hcurrent]
  have hfast : (reservedFastArm r a).val = (reservedFastArm s b).val := by
    unfold reservedFastArm
    rcases a with ⟨astates, amemories, aordinary, aselected, aactual,
      alive, avalid, ainput, aeq, aenabled, aarm, aquantized⟩
    rcases b with ⟨bstates, bmemories, bordinary, bselected, bactual,
      blive, bvalid, binput, beq, benabled, barm, bquantized⟩
    rcases aselected with ⟨aview, astarted, apending, acutoff, aarm', achoice⟩
    rcases bselected with ⟨bview, bstarted, bpending, bcutoff, barm', bchoice⟩
    dsimp only at hview ⊢
    cases hview
    rw [hcurrent]
  unfold appendLogicalCell
  dsimp only
  rw [hproposal]
  simp only [hinput, htime, hcode, hview, hfast]

private theorem wholeCells_take (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (source : SourceInput p)
    (hc : (ReferenceCompletePhysicalHistory.generatedBoundary
      rate source rewards C_star C_h).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + count ≤ p.T) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
      rate rewards C_star C_h source).take count =
      ReferenceFirstWindowNumericalStream.actualLiveSourceCells
        rate source rewards C_star C_h hc count hspan := by
  rw [ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells, dite_eq_left hc]
  exact ReferenceFirstLiveCalendarPrefixReadout.actualLiveSourceCells_take_of_le
    rate source rewards C_star C_h hc count
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h)
    (by omega) _

private theorem wholeCells_past_sourcePrefix
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (source : SourceInput p)
    (hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h t.val source) :
    (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h source).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source)).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h) := by
  let start := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  let q := ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p source
  have hs : start ≤ t.val := hlaunch.2
  let z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLiveRecordingSourceCylinder.stratumIndex q t start hs) :=
    ⟨source, ⟨rfl, hlaunch.1, rfl⟩⟩
  obtain ⟨w, hw⟩ := ReferenceFirstLiveNumericalPrefixTemporal.actualSourcePrefix_in_sourceStratum
    rate rewards C_star C_h q t start hs control0 z
  have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t start hs z
  have hwfacts := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
    rate rewards C_star C_h q t start hs w
  have hnumerical := ReferenceFirstLiveNumericalPrefixTemporal.numerical_past_prefix_eq
    rate rewards C_star C_h q t start hs control0 z w hw
  rw [ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor
      rate rewards C_star C_h q t start hs control0 z,
    ReferenceFirstLiveNumericalPrefixTemporal.actualNumericalCells_take_successor
      rate rewards C_star C_h q t start hs control0 w] at hnumerical
  have hstartW : ReferenceCompletePhysicalHistory.physicalStart
      rate w.val rewards C_star C_h = start := hwfacts.2.2
  have hleft := wholeCells_take rate rewards C_star C_h z.val hz.2.1 (t.val - start)
    (by change start + (t.val - start) ≤ p.T; have ht := t.isLt; omega)
  have hright := wholeCells_take rate rewards C_star C_h w.val hwfacts.2.1 (t.val - start)
    (by rw [hstartW]; have ht := t.isLt; omega)
  have hresult := hleft.trans (hnumerical.trans hright.symm)
  simpa only [z, hw, start] using hresult

private theorem wholeWindow_prefix_pair
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (source : SourceInput p)
    (k : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source).length)
    (l : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)).length)
    (hindex : k.val = l.val)
    (hstart : ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h =
      ReferenceCompletePhysicalHistory.physicalStart rate
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) rewards C_star C_h)
    (hpast : ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h + k.val < n) :
    let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
      rate rewards C_star C_h source)[k.val]
    let s := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source))[l.val]
    r.input.time = s.input.time ∧
      ReferenceActiveHorizonMeasurability.roundRecordCode r =
        ReferenceActiveHorizonMeasurability.roundRecordCode s ∧
      r.input.row.2 r.input.time = s.input.row.2 s.input.time := by
  dsimp only
  let r := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
    rate rewards C_star C_h source)[k.val]
  let s := (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source))[l.val]
  have htime : r.input.time = s.input.time := by
    apply Fin.ext
    rw [wholeWindow_time rate rewards C_star C_h source k.val k.isLt,
      wholeWindow_time rate rewards C_star C_h _ l.val l.isLt, hindex, hstart]
  have hr := wholeWindow_actualRecord rate rewards C_star C_h source k
  have hs := wholeWindow_actualRecord rate rewards C_star C_h _ l
  have ht : r.input.time.val < n := by
    rw [wholeWindow_time rate rewards C_star C_h source k.val k.isLt]
    exact hpast
  have hcode := actualRecord_code_sourcePrefix rate rewards C_star C_h control0 n
    source r.input.time ht
  rw [hr, htime, hs, Option.map_some, Option.map_some] at hcode
  have hfields := actualRecord_fields rate rewards C_star C_h r.input.time source r hr
  have hfields' := actualRecord_fields rate rewards C_star C_h s.input.time _ s hs
  refine ⟨htime, Option.some.inj hcode, ?_⟩
  dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
  rw [hfields.1, hfields'.1, hfields.2.1, hfields'.2.1,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
    ite_eq_left (by rw [← htime]; exact ht), ← htime]

private theorem calendarPast_eq_nil_of_not_launchBy
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (aux : AuxiliaryArray p) (n : ℕ) (hn : n ≤ p.T)
    (hlaunch : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
      rate rewards C_star C_h n source) :
    calendarPast rate rewards C_star C_h (source, aux) n = [] := by
  have hstart : n ≤ ReferenceCompletePhysicalHistory.physicalStart
      rate source rewards C_star C_h := by
    by_cases hc : (ReferenceCompletePhysicalHistory.generatedBoundary
        rate source rewards C_star C_h).crossing.isSome = true
    · have hs : ¬ ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h ≤ n := fun hs => hlaunch ⟨hc, hs⟩
      omega
    · have hnone : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate source rewards C_star C_h).crossing = none := by
        cases h : (ReferenceCompletePhysicalHistory.generatedBoundary
          rate source rewards C_star C_h).crossing with
        | none => rfl
        | some value => exact False.elim (hc (by rw [h]; rfl))
      have hs : ReferenceCompletePhysicalHistory.physicalStart
          rate source rewards C_star C_h = p.T :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
          rate source rewards C_star C_h hnone).2.1
      rw [hs]
      exact hn
  rw [calendarPast_eq_take_elapsed, Nat.sub_eq_zero_of_le hstart, List.take_zero]

/-- The SAME complete first-live logical calendar past factors through the
literal original-source prefix. Every source and numerical comparison is
proved from the actual run; no path, equality, law, or history is an input.
The observed shape and length are included in this list equality. -/
theorem calendarPast_sourcePrefix
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (source : SourceInput p) (aux : AuxiliaryArray p) :
    calendarPast rate rewards C_star C_h (source, aux) n =
      calendarPast rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source, aux) n := by
  by_cases hterminal : p.T ≤ n
  · rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_self control0 n hterminal]
  · let t : Fin p.T := ⟨n, by omega⟩
    by_cases hlaunch : ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
        rate rewards C_star C_h n source
    · have hstart := (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_preserves_actual_launch
        rate rewards C_star C_h control0 n hn source hlaunch).1
      have hnumerical := wholeCells_past_sourcePrefix
        rate rewards C_star C_h control0 t source hlaunch
      let count := n - ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      have hcounts :
          min count (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
            rate rewards C_star C_h source).length =
          min count (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)).length := by
        have h := congrArg List.length hnumerical
        simpa only [List.length_take, wholeFirstLiveCells_length, t, count] using h
      rw [calendarPast_eq_take_elapsed, calendarPast_eq_take_elapsed, ← hstart]
      change (firstLiveChronologicalPrefix rate rewards C_star C_h (source, aux)).take count =
        (firstLiveChronologicalPrefix rate rewards C_star C_h
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source, aux)).take count
      apply List.ext_getElem
      · simpa only [List.length_take, firstLiveChronologicalPrefix_length,
          ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hcounts
      · intro k hk hl
        have hk' : k < min count (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
            rate rewards C_star C_h source).length := by
          simpa only [List.length_take, firstLiveChronologicalPrefix_length,
            ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hk
        have hl' : k < min count (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
            rate rewards C_star C_h
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)).length := by
          simpa only [List.length_take, firstLiveChronologicalPrefix_length,
            ReferenceFirstLiveOverflowReadout.wholeFirstLiveLength] using hl
        have hkcount : k < count := (Nat.lt_min.mp hk').1
        let ki : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h source).length := ⟨k, (Nat.lt_min.mp hk').2⟩
        let li : Fin (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow rate rewards C_star C_h
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)).length :=
          ⟨k, (Nat.lt_min.mp hl').2⟩
        obtain ⟨htime, hcode, hcurrent⟩ := wholeWindow_prefix_pair
          rate rewards C_star C_h control0 n source ki li rfl hstart (by
            dsimp only [ki, count] at hkcount ⊢
            omega)
        have hbefore :
            RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
                rate rewards C_star C_h source).take k) =
            RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              ((ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells rate rewards C_star C_h
                (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)).take k) := by
          have h := congrArg (fun inputs : List (RecordedQueueRun.RoundInput p.K) => inputs.take k)
            hnumerical
          simp only [List.take_take, show min k (t.val - ReferenceCompletePhysicalHistory.physicalStart
            rate source rewards C_star C_h) = k from Nat.min_eq_left (by exact Nat.le_of_lt hkcount)] at h
          exact congrArg (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)) h
        have hinput :
            (wholeLiveCell rate rewards C_star C_h source _ (List.getElem_mem ki.isLt)).input =
            (wholeLiveCell rate rewards C_star C_h
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source)
              _ (List.getElem_mem li.isLt)).input := by
          rw [wholeLiveCell_input_eq rate rewards C_star C_h source ki,
            wholeLiveCell_input_eq rate rewards C_star C_h _ li]
          have h := congrArg (fun inputs : List (RecordedQueueRun.RoundInput p.K) => inputs[k]?)
            hnumerical
          rw [List.getElem?_eq_getElem (by
            simpa only [List.length_take, wholeFirstLiveCells_length, t, count] using hk'),
            List.getElem?_eq_getElem (by
            simpa only [List.length_take, wholeFirstLiveCells_length, t, count] using hl'),
            List.getElem_take, List.getElem_take] at h
          exact Option.some.inj h
        have hgetLeft := firstLiveChronologicalPrefix_get
          rate rewards C_star C_h source aux ki
        have hgetRight := firstLiveChronologicalPrefix_get
          rate rewards C_star C_h _ aux li
        rw [hbefore] at hgetLeft
        simp only [List.getElem_take]
        exact hgetLeft.trans ((appendLogicalCell_temporal_congr
          _ _ _ _ _ aux htime hcode hinput hcurrent).trans hgetRight.symm)
    · have hprefixLaunch : ¬ ReferenceSourcePrefixHistoryFiltration.actualLaunchBy
          rate rewards C_star C_h n
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source) := by
        intro h
        exact hlaunch ((ReferenceSourcePrefixHistoryFiltration.actualLaunchBy_factor
          rate rewards C_star C_h control0 n hn source).mpr h)
      rw [calendarPast_eq_nil_of_not_launchBy rate rewards C_star C_h source aux n hn hlaunch,
        calendarPast_eq_nil_of_not_launchBy rate rewards C_star C_h _ aux n hn hprefixLaunch]

/-- The observed number of complete cells is also a strict-past function of
exactly the same original-source prefix. -/
theorem calendarPast_length_sourcePrefix
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) (hn : n ≤ p.T)
    (source : SourceInput p) (aux : AuxiliaryArray p) :
    (calendarPast rate rewards C_star C_h (source, aux) n).length =
      (calendarPast rate rewards C_star C_h
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 n source, aux) n).length := by
  exact congrArg List.length
    (calendarPast_sourcePrefix rate rewards C_star C_h control0 n hn source aux)

end Bandits.Support.ReferenceFirstLiveChronologicalPrefixCausality

end
