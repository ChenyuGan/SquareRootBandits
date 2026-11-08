/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpResetPrefixBridge
public import Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf

/-!
# Original-source UP test calendar

Sources: `sources/zip4/manuscript/appendix_a_local_protocol.tex:112-138`,
`sources/zip4/manuscript/05_binary_transport.tex:20-42,74-124`,
`sources/zip4/manuscript/06_interruptions.tex:277-284,327-348`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

All events below use the original continuous source and all original private
coordinates. The finite calendar groups actual launch times before any measure
is applied. These are deterministic internal results, with no conditional law,
false/ambiguous-event coverage, or manuscript closure assertion.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedUpBatchPrefixEvent
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.AdaptiveAffineBatchTail
open scoped Classical

namespace Bandits.Support.ReferenceGeneratedUpSourceCalendar

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters} {rate : RateInput p}

private theorem fold_records_take
    (s : ℕ) (input : ReferenceActiveHorizonMeasurability.ActiveRunInput
      (p := p) (rate := rate) s)
    (entries : List (ReferenceActivePhysicalHorizon.CalendarEntry p s))
    (acc : ReferenceActivePhysicalHorizon.Run input.val.1) :
    ((entries.foldl (ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 s input.property) acc).records).take
        acc.records.length = acc.records := by
  induction entries generalizing acc with
  | nil => simp only [List.foldl_nil, List.take_length]
  | cons entry rest ih =>
      let next := ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 s input.property acc entry
      have hlen : acc.records.length ≤ next.records.length := by
        simp only [next, ReferenceActivePhysicalHorizon.foldRound,
          List.length_append, List.length_singleton]
        omega
      change ((rest.foldl _ next).records).take acc.records.length = acc.records
      rw [← Nat.min_eq_left hlen, ← List.take_take, ih]
      simp only [next, ReferenceActivePhysicalHorizon.foldRound,
        List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]

private theorem run_records_take (s count n : ℕ) (hspan : s + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (hn : n ≤ count) :
    (ReferenceActiveHorizonMeasurability.runOfInput s n (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records.take n := by
  have hsplit := ReferenceActivePhysicalHorizon.run_append input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s n (count - n) (by omega) input.property
  have htake := fold_records_take s input
    (ReferenceActivePhysicalHorizon.calendarEntries s (s + n) (count - n) (by omega)
      (by omega))
    (ReferenceActiveHorizonMeasurability.runOfInput s n (by omega) input)
  have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s n (by omega) input.property
  have hsplit' := hsplit
  simp only [Nat.add_sub_of_le hn] at hsplit'
  change _ = (ReferenceActivePhysicalHorizon.run input.val.1 input.val.2.1 input.val.2.2.1
    input.val.2.2.2 s count hspan input.property).records.take n
  rw [hsplit']
  simpa only [ReferenceActivePhysicalHorizon.foldCalendar,
    ReferenceActiveHorizonMeasurability.runOfInput, hlen] using htake.symm

/-- Real initialization has only one elapsed launch boundary, independently
of the current time and selected channel. -/
theorem generatedLaunchBranch_start_unique
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t t' : Fin p.T)
    (s s' : ℕ) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s)
    (hz' : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t' (1, i) s') : s = s' :=
  hz.2.2.symm.trans hz'.2.2

private theorem run_input_ext {s : ℕ}
    (a b : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (hstate : a.val.1 = b.val.1) (hdata : a.val.2 = b.val.2) : a = b :=
  Subtype.ext (Prod.ext hstate hdata)

private theorem original_input_data
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    (originalSourceRunInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z).val.2 =
        (z.1.1.2, ActualInitializationPhysicalStep.selectedRowIndex p z.1, rewards) := rfl

/-- Restoring original rows/J/rewards gives the same whole run input at
every current-time slice and every baseline control on the same source. -/
theorem originalSourceRunInput_coherent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t t' : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (hs' : s ≤ t'.val) (control0 control0' : TimeControl p)
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s)
    (hz' : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t' (1, i) s) :
    originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i ⟨z, hz⟩ =
      originalSourceRunInput (rate := rate) rewards C_star C_h q t' s hs' control0' i ⟨z, hz'⟩ := by
  have hleft := originalSourceRunInput_launch (rate := rate)
    rewards C_star C_h q t s hs control0 i ⟨z, hz⟩
  have hright := originalSourceRunInput_launch (rate := rate)
    rewards C_star C_h q t' s hs' control0' i ⟨z, hz'⟩
  apply run_input_ext
  · exact Option.some.inj (hleft.symm.trans hright)
  · exact (original_input_data rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).trans
      (original_input_data rewards C_star C_h q t' s hs' control0' i ⟨z, hz'⟩).symm

/-- Literal tests after birth in the same full actual physical run to T.
Each test retains its time, affine sample, and optional sent word. -/
def originalSourceTests
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha : ℕ)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    List (Test (AffineBatchDecoder.width p)) :=
  recordsUpTests i ((ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s)
    (by omega) (originalSourceRunInput (rate := rate)
      rewards C_star C_h q t s hs control0 i z)).records.drop (alpha - s))

/-- The full test list is independent of the current slicing time and
baseline control; its source, birth, and channel remain fixed. -/
theorem originalSourceTests_coherent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t t' : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (hs' : s ≤ t'.val) (control0 control0' : TimeControl p)
    (alpha : ℕ) (i : Fin (p.m - 1)) (z : SourceInput p)
    (hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t (1, i) s)
    (hz' : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q t' (1, i) s) :
    originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i ⟨z, hz⟩ =
      originalSourceTests (rate := rate) rewards C_star C_h q t' s hs' control0' alpha i ⟨z, hz'⟩ := by
  unfold originalSourceTests
  rw [originalSourceRunInput_coherent rewards C_star C_h q t t' s hs hs'
    control0 control0' i z hz hz']

private theorem record_test_fields (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : Test (AffineBatchDecoder.width p))
    (htest : evidenceUpTest i record.evidence = some test) :
    test.time = record.input.time.val ∧
      test.sample = ((record.input.rows record.input.selected).2 record.input.time).2 (1, i) ∧
      test.sent = ReferenceActiveAffinePositiveTest.upSent record.input := by
  classical
  change upTestOfDiagnostic i record.output.coordinator.up = some test at htest
  cases hd : record.output.coordinator.up with
  | none => simp only [hd, upTestOfDiagnostic, reduceCtorEq] at htest
  | some d =>
      rw [hd] at htest
      by_cases h : d.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)
      · obtain ⟨other, ho, htime, hsample, hsent⟩ := actualRecordUpTest_fields i record d hd h.1 h.2
        have heq : test = other := Option.some.inj (htest.symm.trans ho)
        subst other
        exact ⟨htime, hsample, hsent.trans (actualRecordUpDiagnostic_expected record d hd)⟩
      · simp only [upTestOfDiagnostic, h, ↓reduceIte, reduceCtorEq] at htest

private theorem records_tests_ordered (i : Fin (p.m - 1))
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (horder : records.Pairwise (fun a b => a.input.time.val < b.input.time.val)) :
    (recordsUpTests i records).Pairwise (fun a b => a.time < b.time) := by
  rw [recordsUpTests, List.filterMap_map]
  apply horder.filterMap
  intro a b hab x hx y hy
  rw [(record_test_fields i a x hx).1, (record_test_fields i b y hy).1]
  exact hab

/-- Actual gap-free physical record times imply strictly increasing focal
test times. In particular there is at most one focal test per round. -/
theorem originalSourceTests_ordered
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha : ℕ)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    (originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z).Pairwise
      (fun a b => a.time < b.time) := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hcalendar := ReferenceActivePhysicalHorizon.run_time_values input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s (p.T - s) (by omega) input.property
  have horder := List.pairwise_lt_range' (s := s) (n := p.T - s)
  rw [← ReferenceActivePhysicalHorizon.calendar, ← hcalendar, List.pairwise_map] at horder
  exact records_tests_ordered i _ horder.drop

private theorem current_record_append
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega) input).records =
      (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records ++
        [originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z] := by
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput]
  rw [ReferenceActivePhysicalHorizon.run_successor_step]
  have hentry : (⟨s + (t.val - s), by omega, by omega⟩ :
      ReferenceActivePhysicalHorizon.CalendarEntry p s) = ⟨t.val, hs, t.isLt⟩ :=
    Subtype.ext (Nat.add_sub_of_le hs)
  rw [hentry]
  rfl

private theorem filterMap_split {X Y : Type*} (f : X → Option Y)
    (xs : List X) (n : ℕ) (x : X) (y : Y)
    (hx : xs[n]? = some x) (hy : f x = some y) :
    ∃ rest, xs.filterMap f = (xs.take n).filterMap f ++ y :: rest := by
  obtain ⟨hn, hx'⟩ := List.getElem?_eq_some_iff.mp hx
  refine ⟨(xs.drop (n + 1)).filterMap f, ?_⟩
  conv_lhs => rw [← List.take_append_drop n xs]
  rw [List.filterMap_append, List.drop_eq_getElem_cons hn, hx', List.filterMap_cons_some hy]

private theorem current_record_get
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records[
      t.val - s]? = some
        (originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z) := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hsucc := run_records_take s (p.T - s) (t.val - s + 1) (by omega) input (by omega)
  rw [current_record_append] at hsucc
  have hlen : (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
      (by omega) input).records.length = t.val - s :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  change (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
    (by omega) input).records ++ [_] = _ at hsucc
  rw [← List.getElem?_take_of_succ, ← hsucc, List.getElem?_append_right (by omega), hlen]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

/-- The before-current tests are exactly the prefix preceding the actual
current test in the one full original-source list. -/
theorem originalSourceTests_split_current
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha : ℕ)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource (rate := rate) rewards C_star C_h q t s i)
    (ha : s ≤ alpha) (hat : alpha ≤ t.val)
    (test : Test (AffineBatchDecoder.width p))
    (htest : upTestOfDiagnostic i
      (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some test) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let prior := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input
    ∃ rest, originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z =
      upBatchTestsSince i s alpha (prior.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
        ++ test :: rest := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let records := (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  have hpre := run_records_take s (p.T - s) (t.val - s) (by omega) input (by omega)
  have hsucc := run_records_take s (p.T - s) (t.val - s + 1) (by omega) input (by omega)
  rw [current_record_append] at hsucc
  have hlen : (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
      (by omega) input).records.length = t.val - s :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  change (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
    (by omega) input).records ++ [current] = records.take (t.val - s + 1) at hsucc
  have hget : records[t.val - s]? = some current := by
    rw [← List.getElem?_take_of_succ, ← hsucc, List.getElem?_append_right (by omega), hlen]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  have hdrop : (records.drop (alpha - s))[t.val - s - (alpha - s)]? = some current := by
    rw [List.getElem?_drop]
    convert hget using 1
    congr 1
    omega
  obtain ⟨rest, hsplit⟩ := filterMap_split (fun record => evidenceUpTest i record.evidence)
    (records.drop (alpha - s)) (t.val - s - (alpha - s)) current test hdrop htest
  refine ⟨rest, ?_⟩
  rw [originalSourceTests, recordsUpTests, List.filterMap_map]
  change (records.drop (alpha - s)).filterMap (fun record => evidenceUpTest i record.evidence) = _
  rw [hsplit]
  congr 1
  rw [upBatchTestsSince, hpre, ← List.map_drop, List.filterMap_map, List.drop_take]
  rfl

/-- At an actual current focal test, tests-since-birth before that round
are exactly the strict-time prefix of the full actual list. -/
theorem originalSourceTests_filter_before_current
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha : ℕ)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (ha : s ≤ alpha) (hat : alpha ≤ t.val)
    (test : Test (AffineBatchDecoder.width p))
    (htest : upTestOfDiagnostic i (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q t s hs control0 i z).output.coordinator.up = some test) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    upBatchTestsSince i s alpha
        ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.map
          ReferenceActivePhysicalHorizon.RoundRecord.evidence) =
      (originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z).filter
        (fun previous => decide (previous.time < t.val)) := by
  dsimp only
  obtain ⟨rest, hsplit⟩ := originalSourceTests_split_current rewards C_star C_h q t s hs
    control0 alpha i z ha hat test htest
  have horder := originalSourceTests_ordered rewards C_star C_h q t s hs control0 alpha i z
  rw [hsplit, List.pairwise_append] at horder
  have htime : test.time = t.val := (record_test_fields i
    (originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z)
    test htest).1
  rw [hsplit, List.filter_append]
  have hbefore := List.filter_eq_self.mpr (fun (previous : Test (AffineBatchDecoder.width p)) hprevious =>
    show decide (previous.time < t.val) = true from by
      rw [decide_eq_true_eq, ← htime]
      exact horder.2.2 previous hprevious test (List.mem_cons_self))
  rw [hbefore]
  have hafter : (test :: rest).filter (fun previous => decide (previous.time < t.val)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro previous hprevious
    rw [decide_eq_true_eq]
    rcases List.mem_cons.mp hprevious with rfl | hrest
    · omega
    · have hlt := (List.pairwise_cons.mp horder.2.1).1 previous hrest
      omega
  rw [hafter, List.append_nil]

private theorem attempt_iff_get {B : ℕ} (candidate : AffineChannelLaw.Word B)
    (n : ℕ) (tests : List (Test B)) :
    attempt candidate n tests ↔
      ∃ test, tests[n]? = some test ∧ test.sent ≠ some candidate ∧
        ∀ previous ∈ tests.take n, good candidate previous := by
  induction n generalizing tests with
  | zero => cases tests <;> simp [attempt]
  | succ n ih =>
      cases tests with
      | nil => simp only [attempt, List.getElem?_nil, reduceCtorEq, false_and,
          exists_false]
      | cons head tail =>
          simp only [attempt, ih, List.getElem?_cons_succ, List.take_succ_cons,
            List.mem_cons, forall_eq_or_imp]
          aesop

private theorem qthAt_of_split {B : ℕ} (candidate : AffineChannelLaw.Word B)
    (before after : List (Test B)) (test : Test B)
    (hgood : survives candidate before.length before) (hsent : test.sent ≠ some candidate) :
    qthAt candidate before.length (before ++ test :: after) test.time := by
  have hget : (before ++ test :: after)[before.length]? = some test := by simp
  refine ⟨(attempt_iff_get candidate _ _).mpr ⟨test, hget, hsent, ?_⟩, ?_⟩
  · simpa only [List.take_left, List.take_length] using
      (survives_iff candidate before.length before).mp hgood |>.2
  · simp only [occurrenceTime, hget, Option.map_some]

/-- The literal last-hash-unchecked contribution identifies a unique qth
test in the actual full list, without an abstract policy or replacement law. -/
theorem actualUpPrefixPositiveSourceEvent_qthAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (hevent : z ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i) :
    ∃ hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s,
      qthAt candidate (ell - 1)
        (originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i ⟨z, hz⟩)
        t.val := by
  obtain ⟨hz, hmarker, test, htest, hsent⟩ := hevent
  obtain ⟨ha, hat, _, _, _, _, hlength, hgood⟩ := hmarker
  obtain ⟨rest, hsplit⟩ := originalSourceTests_split_current rewards C_star C_h q t s hs
    control0 alpha i ⟨z, hz⟩ ha hat test htest
  have hfields := record_test_fields i
    (originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i ⟨z, hz⟩)
    test htest
  have htime : test.time = t.val := hfields.1
  let input := originalSourceRunInput (rate := rate)
    rewards C_star C_h q t s hs control0 i ⟨z, hz⟩
  let before := upBatchTestsSince i s alpha
    ((ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records.map
      ReferenceActivePhysicalHorizon.RoundRecord.evidence)
  change before.length = ell - 1 at hlength
  change survives candidate (ell - 1) before at hgood
  refine ⟨hz, ?_⟩
  rw [hsplit]
  have hq := qthAt_of_split candidate before rest test
    (by simpa only [hlength] using hgood) hsent
  simpa only [hlength, htime] using hq

/-- The current hash-checked constituent supplies a genuinely good actual
test with its original focal sample. The sent option is retained literally,
so this also covers `sent = none`. -/
theorem actualUpPrefixPositiveHashOneSourceEvent_good
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (z : SourceInput p)
    (hevent : z ∈ actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i) :
    ∃ (hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s) (test : Test (AffineBatchDecoder.width p)),
      upTestOfDiagnostic i (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q t s hs control0 i ⟨z, hz⟩).output.coordinator.up = some test ∧
      test.time = t.val ∧ test.sample = ((z.1.2 q).2 t).2 (1, i) ∧ good candidate test := by
  obtain ⟨hz, _, test, htest, htime, hsample, _⟩ :=
    actualUpPrefixPositiveSourceEvent_test_fields
      rewards C_star C_h q t s hs control0 alpha ell candidate i z hevent.1
  obtain ⟨_, _, other, hother, hneq⟩ := hevent.1
  have heq : test = other := Option.some.inj (htest.symm.trans hother)
  refine ⟨hz, test, htest, htime, hsample, ?_, ?_⟩
  · simpa only [heq] using hneq
  · rw [hsample]
    exact hevent.2

/-- Contributions are disjoint over both physical current times and actual
launch times, including before the last candidate hash is checked. -/
theorem actualUpPrefixPositiveSourceEvent_disjoint
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t t' : Fin p.T) (s s' : ℕ)
    (hs : s ≤ t.val) (hs' : s' ≤ t'.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (hne : t ≠ t' ∨ s ≠ s') :
    Disjoint
      (actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q t s hs control0 alpha ell candidate i)
      (actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q t' s' hs' control0 alpha ell candidate i) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨hb, hq⟩ := actualUpPrefixPositiveSourceEvent_qthAt
    rewards C_star C_h q t s hs control0 alpha ell candidate i z hz
  obtain ⟨hb', hq'⟩ := actualUpPrefixPositiveSourceEvent_qthAt
    rewards C_star C_h q t' s' hs' control0 alpha ell candidate i z hz'
  have heqs := generatedLaunchBranch_start_unique rewards C_star C_h q t t' s s' i z hb hb'
  subst s'
  rw [← originalSourceTests_coherent rewards C_star C_h q t t' s hs hs'
    control0 control0 alpha i z hb hb'] at hq'
  have heqt : t = t' := Fin.ext (qthAt_unique candidate (ell - 1) _ hq hq')
  exact hne.elim (fun h => h heqt) (fun h => h rfl)

/-- Finite physical calendar, including every possible actual launch s≤t. -/
abbrev CalendarIndex (p : Parameters) := Sigma fun t : Fin p.T => Fin (t.val + 1)

/-- All literal unchecked qth contributions, with launch times already grouped. -/
def upSourceAttemptEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    Set (SourceInput p) :=
  ⋃ c : CalendarIndex p, actualUpPrefixPositiveSourceEvent (rate := rate)
    rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt) control0 alpha ell candidate i

/-- D₀ is the original J=q stratum. For positive ordinals, D is the finite
union of the existing literal current-hash-one events. -/
def upSourceSurvivalEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    ℕ → Set (SourceInput p)
  | 0 => {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q}
  | ell + 1 => ⋃ c : CalendarIndex p, actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
      rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
        control0 alpha (ell + 1) candidate i

theorem measurableSet_upSourceAttemptEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    MeasurableSet (upSourceAttemptEvent (rate := rate)
      rewards C_star C_h q control0 alpha ell candidate i) :=
  MeasurableSet.iUnion fun c => measurableSet_actualUpPrefixPositiveSourceEvent
    rewards C_star C_h q c.1 c.2.val _ control0 alpha ell candidate i

theorem upSourceAttemptEvent_pairwiseDisjoint
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    Pairwise (fun c c' : CalendarIndex p => Disjoint
      (actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt) control0 alpha ell candidate i)
      (actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q c'.1 c'.2.val (Nat.le_of_lt_succ c'.2.isLt) control0 alpha ell candidate i)) := by
  intro c c' hne
  apply actualUpPrefixPositiveSourceEvent_disjoint
  by_cases ht : c.1 = c'.1
  · right
    intro hs
    apply hne
    cases c with
    | mk t s =>
      cases c' with
      | mk t' s' =>
        dsimp only at ht hs
        subst t'
        exact congrArg (Sigma.mk t) (Fin.ext hs)
  · exact Or.inl ht

/-- The hash-one refinements inherit the same disjoint physical calendar. -/
theorem upSourceHashOne_pairwiseDisjoint
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    Pairwise (fun c c' : CalendarIndex p => Disjoint
      (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
        rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt) control0 alpha ell candidate i)
      (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
        rewards C_star C_h q c'.1 c'.2.val (Nat.le_of_lt_succ c'.2.isLt) control0 alpha ell candidate i)) := by
  intro c c' hne
  exact (upSourceAttemptEvent_pairwiseDisjoint rewards C_star C_h q control0 alpha ell candidate i hne).mono
    (fun _ h => h.1) (fun _ h => h.1)

theorem measurableSet_upSourceSurvivalEvent
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (ell : ℕ) :
    MeasurableSet (upSourceSurvivalEvent (rate := rate)
      rewards C_star C_h q control0 alpha candidate i ell) := by
  cases ell with
  | zero =>
      exact (BootstrapPrivateRoundStreams.measurable_sourceCoordinatorIndex p)
        (measurableSet_singleton q)
  | succ ell =>
      exact MeasurableSet.iUnion fun c => measurableSet_actualUpPrefixPositiveHashOneSourceEvent
        rewards C_star C_h q c.1 c.2.val _ control0 alpha (ell + 1) candidate i

theorem upSourceSurvivalEvent_subset_attempt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (ell : ℕ) (hell : 1 ≤ ell) :
    upSourceSurvivalEvent (rate := rate) rewards C_star C_h q control0 alpha candidate i ell ⊆
      upSourceAttemptEvent (rate := rate) rewards C_star C_h q control0 alpha ell candidate i := by
  cases ell with
  | zero => omega
  | succ ell =>
      intro z hz
      obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨c, hc.1⟩

theorem upSourceAttemptEvent_one_subset_zero
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1)) :
    upSourceAttemptEvent (rate := rate) rewards C_star C_h q control0 alpha 1 candidate i ⊆
      upSourceSurvivalEvent (rate := rate) rewards C_star C_h q control0 alpha candidate i 0 := by
  intro z hz
  obtain ⟨c, hb, _⟩ := Set.mem_iUnion.mp hz
  exact ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
    (rate := rate) rewards C_star C_h q c.1 (1, i) c.2.val ⟨z, hb⟩

private theorem record_test_diagnostic (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : Test (AffineBatchDecoder.width p))
    (htest : evidenceUpTest i record.evidence = some test) :
    ∃ d, record.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) := by
  change upTestOfDiagnostic i record.output.coordinator.up = some test at htest
  cases hd : record.output.coordinator.up with
  | none => simp only [hd, upTestOfDiagnostic, reduceCtorEq] at htest
  | some d =>
      rw [hd] at htest
      by_cases h : d.input.selectedFollower = i ∧
          AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input)
      · exact ⟨d, rfl, h⟩
      · simp only [upTestOfDiagnostic, h, ↓reduceIte, reduceCtorEq] at htest

private theorem record_test_ordinary (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : Test (AffineBatchDecoder.width p))
    (htest : evidenceUpTest i record.evidence = some test) :
    record.input.state.coordinator ≠ .dagger := by
  obtain ⟨d, hd, _⟩ := record_test_diagnostic i record test htest
  intro hdagger
  have hdispatch := ReferenceActivePhysicalStep.dispatch_dagger record.input hdagger
  have hobserve := ReferenceActivePhysicalStep.observeCoordinator_dagger
    (ReferenceActivePhysicalStep.prepare record.input) hdispatch
  rw [record.output_eq] at hd
  change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.up = some d at hd
  rw [hobserve] at hd
  cases hd

private theorem record_test_channel (i : Fin (p.m - 1))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (test : Test (AffineBatchDecoder.width p))
    (htest : evidenceUpTest i record.evidence = some test) :
    ReferenceSelectedAffinePairLaw.selectedChannel p
      ((record.input.rows record.input.selected).2 record.input.time).1 = some (1, i) := by
  obtain ⟨d, hd, hselected, heligible⟩ := record_test_diagnostic i record test htest
  obtain ⟨ledger, _, _, _, _, _, hdraw, _, hslot, _, hgate, _⟩ :=
    ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields record d hd
  have hselectedGate := heligible.1
  rw [hgate] at hselectedGate
  have hup : d.input.slot = PublicDiscreteDraws.upSlot := (of_decide_eq_true hselectedGate).2.1
  have hfollower : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      ((record.input.rows record.input.selected).2 record.input.time).1 = i :=
    hdraw.symm.trans hselected
  rw [ReferenceSelectedAffinePairLaw.selectedChannel_of_up p _ (hslot.symm.trans hup), hfollower]
  rfl

private theorem run_record_time (s count n : ℕ) (hspan : s + count ≤ p.T)
    (input : ReferenceActiveHorizonMeasurability.ActiveRunInput (p := p) (rate := rate) s)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hget : (ReferenceActiveHorizonMeasurability.runOfInput s count hspan input).records[n]? =
      some record) : record.input.time.val = s + n := by
  obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp hget
  have hlen := ReferenceActivePhysicalHorizon.run_record_count input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s count hspan input.property
  have hn' : n < count := by change n < (ReferenceActivePhysicalHorizon.run _ _ _ _ _ _ _ _).records.length at hn; omega
  have htimes := ReferenceActivePhysicalHorizon.run_time_values input.val.1 input.val.2.1
    input.val.2.2.1 input.val.2.2.2 s count hspan input.property
  have h := congrArg (fun xs : List ℕ => xs[n]?) htimes
  dsimp only [ReferenceActiveHorizonMeasurability.runOfInput] at hget
  rw [List.getElem?_map, hget] at h
  simpa only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_range', hn', ↓reduceIte,
    Nat.one_mul, Option.map_some, Option.some.injEq] using h

private theorem birth_take (i : Fin (p.m - 1)) (s alpha n : ℕ)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (records : List (ReferenceActivePhysicalHorizon.RoundEvidence (p := p) (rate := rate)))
    (ha : s ≤ alpha) (han : alpha - s ≤ n) :
    upBatchBirth i s alpha initial (records.take n) ↔ upBatchBirth i s alpha initial records := by
  by_cases heq : alpha = s
  · simp only [upBatchBirth, incomingState?, heq, ↓reduceIte, true_or, and_true]
  · have hindex : alpha - s - 1 < n := by omega
    simp only [upBatchBirth, incomingState?, heq, ↓reduceIte,
      List.getElem?_take_of_lt hindex]

/-- Every focal test in the full list produces its own actual original
selector/launch branch and the existing current-record projection at that time. -/
theorem originalSourceTests_mem_current
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha : ℕ)
    (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (ha : s ≤ alpha) (test : Test (AffineBatchDecoder.width p))
    (htest : test ∈ originalSourceTests (rate := rate)
      rewards C_star C_h q t s hs control0 alpha i z) :
    ∃ (u : Fin p.T) (hsu : s ≤ u.val) (_hau : alpha ≤ u.val)
      (hu : z.1 ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q u (1, i) s),
      upTestOfDiagnostic i (originalSourceCurrentRecord (rate := rate)
        rewards C_star C_h q u s hsu control0 i ⟨z.1, hu⟩).output.coordinator.up = some test ∧
      test.time = u.val ∧ test.sample = ((z.1.1.2 q).2 u).2 (1, i) := by
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let records := (ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input).records
  rw [originalSourceTests, recordsUpTests] at htest
  change test ∈ ((records.drop (alpha - s)).map
    ReferenceActivePhysicalHorizon.RoundRecord.evidence).filterMap (evidenceUpTest i) at htest
  obtain ⟨evidence, hevidence, hproject⟩ := List.mem_filterMap.mp htest
  obtain ⟨record, hrecord, rfl⟩ := List.mem_map.mp hevidence
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hrecord
  have hget : records[alpha - s + k]? = some record := by
    simpa only [List.getElem?_drop] using hk
  have htime := run_record_time s (p.T - s) (alpha - s + k) (by omega) input record hget
  have hrecordFull := List.mem_of_mem_drop hrecord
  obtain ⟨hrows, hj, _⟩ := ReferenceActivePhysicalHorizon.run_record_inputs input.val.1
    input.val.2.1 input.val.2.2.1 input.val.2.2.2 s (p.T - s) (by omega)
    input.property record hrecordFull
  have hJ := ReferenceGeneratedAffineHashHalf.selectedRowIndex_of_generatedLaunchBranch
    (rate := rate) rewards C_star C_h q t (1, i) s z
  have hrows' : record.input.rows = z.1.1.2 := hrows
  have hj' : record.input.selected = q := hj.trans hJ
  have hchannel := record_test_channel i record test hproject
  rw [hrows', hj'] at hchannel
  have hu : z.1 ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
      (rate := rate) rewards C_star C_h q record.input.time (1, i) s :=
    ⟨(ReferenceSelectedAffinePairLaw.selector_eq_iff p q record.input.time (1, i) z.1).mpr
      ⟨hJ, hchannel⟩, z.2.2⟩
  have hsu : s ≤ record.input.time.val := by omega
  have hau : alpha ≤ record.input.time.val := by omega
  have hinput := originalSourceRunInput_coherent rewards C_star C_h q t record.input.time s
    hs hsu control0 control0 i z.1 z.2 hu
  have hget' := current_record_get rewards C_star C_h q record.input.time s hsu control0 i ⟨z.1, hu⟩
  rw [← hinput] at hget'
  change records[record.input.time.val - s]? = some
    (originalSourceCurrentRecord (rate := rate)
      rewards C_star C_h q record.input.time s hsu control0 i ⟨z.1, hu⟩) at hget'
  have hindex : record.input.time.val - s = alpha - s + k := by omega
  rw [hindex, hget] at hget'
  have hcurrent := Option.some.inj hget'
  refine ⟨record.input.time, hsu, hau, hu, ?_, ?_, ?_⟩
  · rw [← hcurrent]
    exact hproject
  · exact (record_test_fields i record test hproject).1
  · simpa only [hrows', hj'] using (record_test_fields i record test hproject).2.1

/-- On any actual original-source launch branch, the aggregate unchecked
event is precisely a real birth and the list-level qth attempt in its one full
run. The auxiliary slicing time need not be the occurrence time. -/
theorem mem_upSourceAttemptEvent_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) :
    z.1 ∈ upSourceAttemptEvent (rate := rate)
        rewards C_star C_h q control0 alpha ell candidate i ↔
      let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
      let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
      1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧
        upBatchBirth i s alpha input.val.1
          (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
        attempt candidate (ell - 1)
          (originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z) := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
  let tests := originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z
  constructor
  · intro hz
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
    have heqs := generatedLaunchBranch_start_unique rewards C_star C_h q t c.1 s c.2.val i z.1
      z.2 hc.1
    have hsu : s ≤ c.1.val := by have h := c.2.isLt; omega
    have hc' : z.1 ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q c.1 s hsu control0 alpha ell candidate i := by
      subst s
      exact hc
    obtain ⟨hb, hq⟩ := actualUpPrefixPositiveSourceEvent_qthAt
      rewards C_star C_h q c.1 s hsu control0 alpha ell candidate i z.1 hc'
    have hinput := originalSourceRunInput_coherent rewards C_star C_h q t c.1 s hs hsu
      control0 control0 i z.1 z.2 hb
    have hmarker := hc'.choose_spec.1
    dsimp only [originalSourcePrefixMarker] at hmarker
    rw [← hinput] at hmarker
    obtain ⟨ha, hat, h1, hQ, hbirth, _⟩ := hmarker
    have hpre := run_records_take s (p.T - s) (c.1.val - s) (by omega) input (by omega)
    rw [hpre, List.map_take] at hbirth
    have hbirthFull := (birth_take i s alpha (c.1.val - s) input.val.1
      (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ha (by omega)).mp hbirth
    rw [← originalSourceTests_coherent rewards C_star C_h q t c.1 s hs hsu
      control0 control0 alpha i z.1 z.2 hb] at hq
    exact ⟨h1, hQ, hbirthFull, hq.1⟩
  · rintro ⟨h1, hQ, hbirth, hattempt⟩
    have ha : s ≤ alpha := hbirth.1
    obtain ⟨test, hget, hsent, hprevious⟩ := (attempt_iff_get candidate (ell - 1) tests).mp hattempt
    obtain ⟨u, hsu, hau, hu, htest, htime, _⟩ := originalSourceTests_mem_current
      rewards C_star C_h q t s hs control0 alpha i z ha test (List.mem_of_getElem? hget)
    let input' := originalSourceRunInput (rate := rate)
      rewards C_star C_h q u s hsu control0 i ⟨z.1, hu⟩
    let prior := ReferenceActiveHorizonMeasurability.runOfInput s (u.val - s) (by omega) input'
    let before := upBatchTestsSince i s alpha
      (prior.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
    let tests' := originalSourceTests (rate := rate)
      rewards C_star C_h q u s hsu control0 alpha i ⟨z.1, hu⟩
    have hinput := originalSourceRunInput_coherent rewards C_star C_h q t u s hs hsu
      control0 control0 i z.1 z.2 hu
    change input = input' at hinput
    have htests : tests = tests' := originalSourceTests_coherent rewards C_star C_h q t u s hs hsu
      control0 control0 alpha i z.1 z.2 hu
    obtain ⟨rest, hsplit⟩ := originalSourceTests_split_current rewards C_star C_h q u s hsu
      control0 alpha i ⟨z.1, hu⟩ ha hau test htest
    change tests' = before ++ test :: rest at hsplit
    have hget' : tests'[ell - 1]? = some test := by rw [← htests]; exact hget
    have hgetBefore : tests'[before.length]? = some test := by
      rw [hsplit, List.getElem?_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem?_cons_zero]
    have horder := originalSourceTests_ordered rewards C_star C_h q u s hsu control0 alpha i ⟨z.1, hu⟩
    have hlength : before.length = ell - 1 :=
      (countBefore_eq_index tests' horder before.length test hgetBefore).symm.trans
        (countBefore_eq_index tests' horder (ell - 1) test hget')
    have hbefore : tests.take (ell - 1) = before := by
      rw [htests, hsplit, ← hlength, List.take_left]
    have hgood : survives candidate (ell - 1) before :=
      (survives_iff candidate (ell - 1) before).mpr
        ⟨by omega, by
          rw [hbefore] at hprevious
          simpa only [← hlength, List.take_length] using hprevious⟩
    have hbirth' : upBatchBirth i s alpha input'.val.1
        (prior.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) := by
      dsimp only [prior]
      rw [run_records_take s (p.T - s) (u.val - s) (by omega) input' (by omega), List.map_take]
      apply (birth_take i s alpha (u.val - s) input'.val.1 _ ha (by omega)).mpr
      rw [← hinput]
      exact hbirth
    have hord : prior.finalState.coordinator ≠ .dagger :=
      record_test_ordinary i
        (originalSourceCurrentRecord (rate := rate) rewards C_star C_h q u s hsu control0 i ⟨z.1, hu⟩)
        test htest
    apply Set.mem_iUnion.mpr
    refine ⟨⟨u, ⟨s, by omega⟩⟩, hu, ?_, test, htest, hsent⟩
    exact ⟨ha, hau, h1, hQ, hbirth', hord, hlength, hgood⟩

private theorem survives_succ_iff_attempt_hash {B : ℕ}
    (candidate : AffineChannelLaw.Word B) (n : ℕ) (tests : List (Test B)) :
    survives candidate (n + 1) tests ↔
      attempt candidate n tests ∧
        ∃ test, tests[n]? = some test ∧ AffineChannelLaw.affineHash test.sample candidate = 1 := by
  induction n generalizing tests with
  | zero => cases tests <;> simp [survives, attempt, good]
  | succ n ih =>
      cases tests with
      | nil => simp only [survives, attempt, false_and]
      | cons head tail =>
          simp only [survives, attempt, ih, List.getElem?_cons_succ]
          aesop

private theorem event_test_index
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (z : SourceInput p)
    (hevent : z ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
      rewards C_star C_h q t s hs control0 alpha ell candidate i) :
    ∃ (hz : z ∈ ReferenceGeneratedAffineHashHalf.generatedLaunchBranch
        (rate := rate) rewards C_star C_h q t (1, i) s) (test : Test (AffineBatchDecoder.width p)),
      (originalSourceTests (rate := rate)
        rewards C_star C_h q t s hs control0 alpha i ⟨z, hz⟩)[ell - 1]? = some test ∧
      test.sample = ((z.1.2 q).2 t).2 (1, i) := by
  obtain ⟨hz, hmarker, test, htest, _, hsample, _⟩ :=
    actualUpPrefixPositiveSourceEvent_test_fields
      rewards C_star C_h q t s hs control0 alpha ell candidate i z hevent
  obtain ⟨ha, hat, _, _, _, _, hlength, _⟩ := hmarker
  obtain ⟨rest, hsplit⟩ := originalSourceTests_split_current rewards C_star C_h q t s hs
    control0 alpha i ⟨z, hz⟩ ha hat test htest
  refine ⟨hz, test, ?_, hsample⟩
  rw [hsplit, ← hlength, List.getElem?_append_right (Nat.le_refl _)]
  simp only [Nat.sub_self, List.getElem?_cons_zero]

/-- On the same original branch, D is exactly real birth and goodness of
the first ell actual tests. In particular a missing positive test cannot be
supplied by a dormant, failed, or never-tested birth. -/
theorem mem_upSourceSurvivalEvent_iff
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i) (hell : 1 ≤ ell) :
    z.1 ∈ upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha candidate i ell ↔
      let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
      let full := ReferenceActiveHorizonMeasurability.runOfInput s (p.T - s) (by omega) input
      1 ≤ ell ∧ ell ≤ AffineBatchDecoder.quota p ∧
        upBatchBirth i s alpha input.val.1
          (full.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
        survives candidate ell
          (originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z) := by
  let tests := originalSourceTests (rate := rate) rewards C_star C_h q t s hs control0 alpha i z
  have hindex (c : CalendarIndex p)
      (hc : z.1 ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
          control0 alpha ell candidate i) :
      ∃ test, tests[ell - 1]? = some test ∧ test.sample = ((z.1.1.2 q).2 c.1).2 (1, i) := by
    have heqs := generatedLaunchBranch_start_unique rewards C_star C_h q t c.1 s c.2.val i z.1
      z.2 hc.1
    have hsu : s ≤ c.1.val := by have h := c.2.isLt; omega
    have hc' : z.1 ∈ actualUpPrefixPositiveSourceEvent (rate := rate)
        rewards C_star C_h q c.1 s hsu control0 alpha ell candidate i := by
      subst s
      exact hc
    obtain ⟨hb, test, hget, hsample⟩ := event_test_index
      rewards C_star C_h q c.1 s hsu control0 alpha ell candidate i z.1 hc'
    rw [← originalSourceTests_coherent rewards C_star C_h q t c.1 s hs hsu
      control0 control0 alpha i z.1 z.2 hb] at hget
    exact ⟨test, hget, hsample⟩
  cases ell with
  | zero => omega
  | succ n =>
      constructor
      · intro hz
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
        have hp : z.1 ∈ upSourceAttemptEvent (rate := rate)
            rewards C_star C_h q control0 alpha (n + 1) candidate i :=
          Set.mem_iUnion.mpr ⟨c, hc.1⟩
        obtain ⟨h1, hQ, hbirth, hattempt⟩ := (mem_upSourceAttemptEvent_iff
          rewards C_star C_h q t s hs control0 alpha (n + 1) candidate i z).mp hp
        obtain ⟨test, hget, hsample⟩ := hindex c hc.1
        have hhash : AffineChannelLaw.affineHash test.sample candidate = 1 := by
          rw [hsample]
          exact hc.2
        refine ⟨h1, hQ, hbirth, ?_⟩
        exact (survives_succ_iff_attempt_hash candidate n tests).mpr
          ⟨hattempt, test, hget, hhash⟩
      · rintro ⟨h1, hQ, hbirth, hsurvives⟩
        obtain ⟨hattempt, test, hget, hhash⟩ :=
          (survives_succ_iff_attempt_hash candidate n tests).mp hsurvives
        have hp := (mem_upSourceAttemptEvent_iff
          rewards C_star C_h q t s hs control0 alpha (n + 1) candidate i z).mpr
            ⟨h1, hQ, hbirth, hattempt⟩
        obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hp
        obtain ⟨other, hother, hsample⟩ := hindex c hc
        have heq : test = other := Option.some.inj (hget.symm.trans hother)
        apply Set.mem_iUnion.mpr
        refine ⟨c, hc, ?_⟩
        rw [heq, hsample] at hhash
        exact hhash

/-- Every unchecked ell-th contribution for ell≥2 lies in the previous
hash-checked aggregate. Both launch times and current times are already
united; there is no extra union over possible launches for the consumer. -/
theorem upSourceAttemptEvent_subset_predecessor
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (control0 : TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (hell : 2 ≤ ell) :
    upSourceAttemptEvent (rate := rate) rewards C_star C_h q control0 alpha ell candidate i ⊆
      upSourceSurvivalEvent (rate := rate) rewards C_star C_h q control0 alpha candidate i (ell - 1) := by
  intro z hz
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hz
  let source : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q c.1 c.2.val i := ⟨z, hc.1⟩
  obtain ⟨_, hQ, hbirth, hattempt⟩ := (mem_upSourceAttemptEvent_iff
    rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
      control0 alpha ell candidate i source).mp hz
  apply (mem_upSourceSurvivalEvent_iff rewards C_star C_h q c.1 c.2.val
    (Nat.le_of_lt_succ c.2.isLt) control0 alpha (ell - 1) candidate i source (by omega)).mpr
  exact ⟨by omega, by omega, hbirth, attempt_implies_survives candidate (ell - 1) _ hattempt⟩

/-- B's canonical reset birth identifies the literal source constituent at
ell = actual pending length + 1. Birth and pending identities are produced
from the executed call; candidate survival remains exactly the event test. -/
theorem actual_current_positive_birth
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p)) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (hpositive : ReferenceActiveAffinePositiveTest.upPositive
      (originalSourceCurrentInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z) = true) :
    let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
    let prior := ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    let pending := (current.input.state.upDecoderBank i).pending
    ∃ alpha, s ≤ alpha ∧ alpha ≤ t.val ∧
      upBatchBirth i s alpha input.val.1
        (prior.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence) ∧
      let tests := upBatchTestsSince i s alpha
        (prior.records.map ReferenceActivePhysicalHorizon.RoundRecord.evidence)
      tests.length = pending.length ∧
      tests.map (fun test => (test.time, test.sample)) =
        pending.map (fun entry => (entry.time.val, entry.sample)) ∧
      1 ≤ pending.length + 1 ∧ pending.length + 1 ≤ AffineBatchDecoder.quota p ∧
      (z.1 ∈ actualUpPrefixPositiveSourceEvent (rate := rate) rewards C_star C_h q t s hs
          control0 alpha (pending.length + 1) candidate i ↔
        survives candidate pending.length tests ∧
          ReferenceActiveAffinePositiveTest.upSent current.input ≠ some candidate) := by
  dsimp only
  let input := originalSourceRunInput (rate := rate) rewards C_star C_h q t s hs control0 i z
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  obtain ⟨test, htest, _, _, hsent⟩ := originalSourceCurrentRecord_upPositive_fields
    rewards C_star C_h q t s hs control0 i z hpositive
  obtain ⟨d, hd, hselected, _⟩ := record_test_diagnostic i current test htest
  have hlength : (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s)
      (by omega) input).records.length = t.val - s :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have happend := current_record_append rewards C_star C_h q t s hs control0 i z
  change (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1) (by omega) input).records =
    (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s) (by omega) input).records ++
      [current] at happend
  have hcurrent : (ReferenceActiveHorizonMeasurability.runOfInput s (t.val - s + 1)
      (by omega) input).records[t.val - s]? = some current := by
    rw [happend, List.getElem?_append_right (by omega), hlength]
    simp only [Nat.sub_self, List.getElem?_cons_zero]
  obtain ⟨alpha, resetCount, resetState, hresetSpan, hAlpha, _, hAlphaUpper, _, _, _,
      hbirth, _, _, _, hcoordinates, htestsLength, _, _, _, _, _, h1, hQ, hmarker, _⟩ :=
    ReferenceGeneratedUpResetPrefixBridge.original_source_actual_up_marker rate
      rewards C_star C_h q t s hs control0 i z candidate input rfl current hcurrent d hd hselected
  refine ⟨alpha, by omega, hAlphaUpper, hbirth, htestsLength, hcoordinates, h1, hQ, ?_⟩
  constructor
  · rintro ⟨hz, hm, other, hother, hneq⟩
    have heq : test = other := Option.some.inj (htest.symm.trans hother)
    refine ⟨hmarker.mp hm, ?_⟩
    intro h
    apply hneq
    exact (congrArg Test.sent heq).symm.trans (hsent.trans h)
  · rintro ⟨hsurvives, hneq⟩
    refine ⟨z.2, hmarker.mpr hsurvives, test, htest, ?_⟩
    intro h
    exact hneq (hsent.symm.trans h)

/-- At quota the retained diagnostic appends the actual completed batch,
including when a subsequent physical finish fails. This asserts the diagnostic
decoder state, with no unconditional physical successor-bank equality. -/
theorem actual_current_quota_completion
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : TimeControl p) (i : Fin (p.m - 1))
    (z : ReferenceGeneratedUpBatchPrefixEvent.UpLaunchSource
      (rate := rate) rewards C_star C_h q t s i)
    (hpositive : ReferenceActiveAffinePositiveTest.upPositive
      (originalSourceCurrentInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z) = true)
    (hquota : ((originalSourceCurrentInput (rate := rate)
        rewards C_star C_h q t s hs control0 i z).state.upDecoderBank i).pending.length + 1 =
      AffineBatchDecoder.quota p) :
    let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
    ∃ d, current.output.coordinator.up = some d ∧
      d.decoderAfter.pending = [] ∧ d.decoderAfter.completed =
        (current.input.state.upDecoderBank i).completed ++
          [(current.input.state.upDecoderBank i).pending ++
            [AffineBatchDecoder.entry p
              (ReferenceCoordinatorUpDecoderReplay.constantInputTrace d.input) d.input.time]] := by
  dsimp only
  let current := originalSourceCurrentRecord (rate := rate) rewards C_star C_h q t s hs control0 i z
  obtain ⟨test, htest⟩ := (originalSourceCurrentRecord_upTest_iff
    rewards C_star C_h q t s hs control0 i z).mp hpositive
  obtain ⟨d, hd, hselected, _⟩ := record_test_diagnostic i current test htest
  have hcompletion := ReferenceGeneratedUpBatchCalendar.record_up_quota_completion
    current d hd i hselected hpositive hquota
  exact ⟨d, hd, hcompletion.1, hcompletion.2.1⟩

end Bandits.Support.ReferenceGeneratedUpSourceCalendar

end
