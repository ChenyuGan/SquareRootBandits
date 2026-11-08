/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFibreExtension
public import Bandits.Support.ReferenceCompleteOwnHistoryPrefixLocality

/-!
# Actual first renewal calls are determined by the strict physical past

Sources: `sources/zip4/manuscript/06_interruptions.tex:399-423`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:176-215`.

The update throughout is the existing whole selected-control suffix update.
The original identification array, private index and all private arrays, all
other rows, and the selected row's entire forward component are retained.
Only controls at and after the specified round may change.

An actual first collection call supplies its own corrected launch. Temporal
comparison of the existing horizon runs retains the incoming state at the
call and every earlier prechoice cell. The parameter selector at the call
reads that state and time, without reading the current assignment controls.
Old freeze boundaries and renewal parameters therefore agree as well.

These are internal deterministic locality results and their consequences on
the existing analytical fibre extension. They assert no conditional logical
law, physical law after a vector update, identification of current vectors,
manuscript score identity, overflow coupling, or regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep (RateInput State Payload Ledger)
open Bandits.Support.ReferenceActivePhysicalHorizon (RoundRecord allActiveAtStart run)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable selectedRowIndex)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput)
open Bandits.Support.ReferenceCompletePhysicalHistory
  (physicalStart completeSuffixRecords completeSuffixRecords_length
    completeSuffixRecords_time_values completeSuffixRecords_on_launch
    activeMode_of_launch_eq_some)
open Bandits.Support.ReferenceGeneratedPrefixSuffixInvariance
  (replaceSelectedControlSuffix replaceSelectedControlSuffix_selected
    replaceSelectedControlSuffix_control_before
    replaceSelectedControlSuffix_preserves_actual_launch)
open Bandits.Support.ReferenceFirstCollectionSamplerCall
  (firstCollectionCall firstCollectionCall_spec collectionCallAt collectionCallAt_spec
    collectionCallOnInput_eq_of_state_eq_time_eq)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalPastLocality

variable {p : ConstructorDimensions.Parameters}

-- All local comparisons below concern the original horizon fold. In
-- particular, no new execution or matching-trace assumption is introduced.
private theorem run_record_at
    {rate : RateInput p} (initial : State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : GridRewardTable p) (start count : ℕ)
    (hspan : start + count ≤ p.T) (hmode : allActiveAtStart initial start)
    (j : ℕ) (hj : j < count) :
    (run initial rows selected rewards start count hspan hmode).records[j]? =
      some (ReferenceActiveStoppedPrefixCoupling.referenceRecordAt
        initial rows selected rewards start j (by omega) hmode) := by
  rw [← List.getElem?_take_of_succ,
    ReferenceActiveStoppedPrefixCoupling.reference_run_prefix_records
      initial rows selected rewards start count hspan hmode (j + 1) (by omega),
    (ReferenceActiveStoppedPrefixCoupling.reference_successor_equations
      initial rows selected rewards start j (by omega) hmode).2,
    List.getElem?_append_right
      (by rw [ReferenceActivePhysicalHorizon.run_record_count])]
  simp only [ReferenceActivePhysicalHorizon.run_record_count, Nat.sub_self,
    List.getElem?_cons_zero]

private theorem complete_record_time
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (n : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (hr : (completeSuffixRecords rate source rewards C_star C_h)[n]? = some r) :
    r.input.time.val = physicalStart rate source rewards C_star C_h + n := by
  have hn : n < p.T - physicalStart rate source rewards C_star C_h := by
    obtain ⟨hn, _⟩ := List.getElem?_eq_some_iff.mp hr
    simpa only [completeSuffixRecords_length] using hn
  have htimes := congrArg (fun l : List ℕ => l[n]?)
    (completeSuffixRecords_time_values rate source rewards C_star C_h)
  rw [List.getElem?_map, hr] at htimes
  simp only [Option.map_some, ReferenceActivePhysicalHorizon.calendar,
    List.getElem?_range' hn, Nat.one_mul] at htimes
  exact Option.some.inj htimes

private theorem launch_of_record
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (n : ℕ) (r : RoundRecord (p := p) (rate := rate))
    (hr : (completeSuffixRecords rate source rewards C_star C_h)[n]? = some r) :
    ∃ active : State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some active := by
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      simp only [completeSuffixRecords, dite_eq_left hlaunch, List.getElem?_nil] at hr
      cases hr
  | some active => exact ⟨active, rfl⟩

private theorem launch_and_start_preserved
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hs : physicalStart rate source rewards C_star C_h ≤ t.val) :
    physicalStart rate (replaceSelectedControlSuffix source t suffix)
        rewards C_star C_h = physicalStart rate source rewards C_star C_h ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate (replaceSelectedControlSuffix source t suffix) rewards C_star C_h =
        some active := by
  have hsome : (ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h).isSome = true := by
    rw [hlaunch]
    rfl
  have hcross :=
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
      rate source rewards C_star C_h).mp hsome
  have hpres := replaceSelectedControlSuffix_preserves_actual_launch
    (rate := rate) rewards C_star C_h (selectedRowIndex p source) t
    (physicalStart rate source rewards C_star C_h) hs source rfl suffix hcross rfl
  exact ⟨hpres.2.2.1, hpres.2.2.2.symm.trans hlaunch⟩

private theorem run_prefix_suffix_comparison
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (k : ℕ) (hk : physicalStart rate source rewards C_star C_h + k ≤ t.val) :
    let s := physicalStart rate source rewards C_star C_h
    let mode := activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch
    (run active source.1.2 (selectedRowIndex p source) rewards s k
        (by omega) mode).finalState =
      (run active (replaceSelectedControlSuffix source t suffix).1.2
        (selectedRowIndex p source) rewards s k (by omega) mode).finalState ∧
    (run active source.1.2 (selectedRowIndex p source) rewards s k
        (by omega) mode).records.map RoundRecord.evidence =
      (run active (replaceSelectedControlSuffix source t suffix).1.2
        (selectedRowIndex p source) rewards s k (by omega) mode).records.map
        RoundRecord.evidence := by
  dsimp only
  apply ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads
  · intro v _ hv
    exact (replaceSelectedControlSuffix_control_before source t v suffix (by omega)).symm
  · intro _ _ _
    rfl
  · intro _ v hv
    exact congrArg (fun control : ContinuousLearningRows.TimeControl p =>
      control.1 ContinuousControlSlice.Label.prop)
      (replaceSelectedControlSuffix_control_before source t v suffix (by omega)).symm

private theorem complete_record_at_launch
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (j : ℕ) (hj : j < p.T - physicalStart rate source rewards C_star C_h) :
    (completeSuffixRecords rate source rewards C_star C_h)[j]? =
      some (ReferenceActiveStoppedPrefixCoupling.referenceRecordAt
        active source.1.2 (selectedRowIndex p source) rewards
        (physicalStart rate source rewards C_star C_h) j (by omega)
        (activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch)) := by
  rw [completeSuffixRecords_on_launch rate source rewards C_star C_h active hlaunch]
  exact run_record_at active source.1.2 (selectedRowIndex p source) rewards
    (physicalStart rate source rewards C_star C_h)
    (p.T - physicalStart rate source rewards C_star C_h) _ _ j hj

private theorem indexed_records_suffix_comparison
    (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (active : State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some active)
    (hs : physicalStart rate source rewards C_star C_h ≤ t.val)
    (j : ℕ) (hj : physicalStart rate source rewards C_star C_h + j ≤ t.val) :
    ∃ a b : RoundRecord (p := p) (rate := rate),
      (completeSuffixRecords rate source rewards C_star C_h)[j]? = some a ∧
      (completeSuffixRecords rate (replaceSelectedControlSuffix source t suffix)
        rewards C_star C_h)[j]? = some b ∧
      a.input.state = b.input.state ∧ a.input.time = b.input.time := by
  obtain ⟨hstart, hlaunch'⟩ := launch_and_start_preserved
    rate rewards C_star C_h source t suffix active hlaunch hs
  let s := physicalStart rate source rewards C_star C_h
  have hmode := activeMode_of_launch_eq_some rate source rewards C_star C_h active hlaunch
  have hspan : s + (j + 1) ≤ p.T := by
    have ht := t.isLt
    dsimp only [s]
    omega
  let a := ReferenceActiveStoppedPrefixCoupling.referenceRecordAt
    active source.1.2 (selectedRowIndex p source) rewards s j hspan hmode
  let b := ReferenceActiveStoppedPrefixCoupling.referenceRecordAt
    active (replaceSelectedControlSuffix source t suffix).1.2
    (selectedRowIndex p source) rewards s j hspan hmode
  have ha : (completeSuffixRecords rate source rewards C_star C_h)[j]? = some a :=
    complete_record_at_launch rate rewards C_star C_h source active hlaunch j (by omega)
  have hb : (completeSuffixRecords rate (replaceSelectedControlSuffix source t suffix)
      rewards C_star C_h)[j]? = some b := by
    have h := complete_record_at_launch rate rewards C_star C_h
      (replaceSelectedControlSuffix source t suffix) active hlaunch' j (by rw [hstart]; omega)
    simpa only [hstart, replaceSelectedControlSuffix_selected] using h
  have hrun := run_prefix_suffix_comparison rate rewards C_star C_h
    source t suffix active hlaunch j hj
  exact ⟨a, b, ha, hb, hrun.1, rfl⟩

variable (rate : RateInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)

/-- A present first call produces its actual corrected seed and elapsed
launch time. The update preserves both; no launch or success is assumed. -/
theorem actual_launch_of_firstCollectionCall
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta))) :
    ∃ active : State p rate,
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate source rewards C_star C_h = some active ∧
      physicalStart rate source rewards C_star C_h ≤ t.val ∧
      physicalStart rate (replaceSelectedControlSuffix source t suffix)
        rewards C_star C_h = physicalStart rate source rewards C_star C_h ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch
        rate (replaceSelectedControlSuffix source t suffix) rewards C_star C_h =
        some active := by
  obtain ⟨n, r, hr, htime, _, _⟩ :=
    (firstCollectionCall_spec rewards C_star C_h source u t theta).mp hcall
  obtain ⟨active, hlaunch⟩ := launch_of_record rate rewards C_star C_h source n r hr
  have hcalendar := complete_record_time rate rewards C_star C_h source n r hr
  rw [htime] at hcalendar
  have hs : physicalStart rate source rewards C_star C_h ≤ t.val := by omega
  obtain ⟨hstart, hlaunch'⟩ := launch_and_start_preserved
    rate rewards C_star C_h source t suffix active hlaunch hs
  exact ⟨active, hlaunch, hs, hstart, hlaunch'⟩

/-- Indexed actual records through the call have equal incoming states and
timestamps. Each record belongs to its own whole-source canonical suffix. -/
theorem actual_records_of_firstCollectionCall
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta))) :
    ∃ n : ℕ,
      physicalStart rate source rewards C_star C_h + n = t.val ∧
      (∀ j ≤ n, ∃ a b : RoundRecord (p := p) (rate := rate),
        (completeSuffixRecords rate source rewards C_star C_h)[j]? = some a ∧
        (completeSuffixRecords rate (replaceSelectedControlSuffix source t suffix)
          rewards C_star C_h)[j]? = some b ∧
        a.input.state = b.input.state ∧ a.input.time = b.input.time) := by
  obtain ⟨n, r, hr, htime, _, _⟩ :=
    (firstCollectionCall_spec rewards C_star C_h source u t theta).mp hcall
  obtain ⟨active, hlaunch⟩ := launch_of_record rate rewards C_star C_h source n r hr
  have hcalendar := complete_record_time rate rewards C_star C_h source n r hr
  rw [htime] at hcalendar
  refine ⟨n, hcalendar.symm, ?_⟩
  intro j hj
  apply indexed_records_suffix_comparison rate rewards C_star C_h
    source t suffix active hlaunch (by omega) j (by omega)

/-- Replacing arbitrary current and future controls preserves an actual call
at this time and its entire parameter. Earlier absent selectors are proved
from indexed records, rather than supplied as a matching-run hypothesis. -/
theorem firstCollectionCall_eq_of_replaceSelectedControlSuffix
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta))) :
    firstCollectionCall rate rewards C_star C_h
      (replaceSelectedControlSuffix source t suffix) = some (u, (t, theta)) := by
  obtain ⟨n, r, hr, htime, hlocal, hearlier⟩ :=
    (firstCollectionCall_spec rewards C_star C_h source u t theta).mp hcall
  obtain ⟨active, hlaunch⟩ := launch_of_record rate rewards C_star C_h source n r hr
  have hcalendar := complete_record_time rate rewards C_star C_h source n r hr
  rw [htime] at hcalendar
  have hs : physicalStart rate source rewards C_star C_h ≤ t.val := by omega
  obtain ⟨a, b, ha, hb, hstate, htimeAB⟩ := indexed_records_suffix_comparison
    rate rewards C_star C_h source t suffix active hlaunch hs n (by omega)
  have har : a = r := Option.some.inj (ha.symm.trans hr)
  subst a
  apply (firstCollectionCall_spec rewards C_star C_h
    (replaceSelectedControlSuffix source t suffix) u t theta).mpr
  refine ⟨n, b, hb, htimeAB.symm.trans htime, ?_, ?_⟩
  · exact (collectionCallOnInput_eq_of_state_eq_time_eq
      r.input b.input hstate htimeAB).symm.trans hlocal
  · intro j hj earlier hrecord
    obtain ⟨a, b', ha, hb', hstate', htime'⟩ := indexed_records_suffix_comparison
      rate rewards C_star C_h source t suffix active hlaunch hs j (by omega)
    have hbEarlier : b' = earlier := Option.some.inj (hb'.symm.trans hrecord)
    subst b'
    exact (ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
      a.input earlier.input hstate' htime').symm.trans (hearlier j hj a ha)

/-- Restoring the original selected controls reverses this suffix update.
All original private arrays, including the selecting scalar, are unchanged. -/
theorem replaceSelectedControlSuffix_restore
    (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    replaceSelectedControlSuffix (replaceSelectedControlSuffix source t suffix) t
      (source.1.2 (selectedRowIndex p source)).2 = source := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext q
      by_cases hq : q = selectedRowIndex p source
      · subst q
        apply Prod.ext
        · exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward
            (replaceSelectedControlSuffix source t suffix) t
            (source.1.2 (selectedRowIndex p source)).2).trans
            (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_forward
              source t suffix)
        · funext v
          by_cases hv : v.val < t.val
          · exact (replaceSelectedControlSuffix_control_before
              (replaceSelectedControlSuffix source t suffix) t v
              (source.1.2 (selectedRowIndex p source)).2 hv).trans
              (replaceSelectedControlSuffix_control_before source t v suffix hv)
          · exact ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_control_from
              (replaceSelectedControlSuffix source t suffix) t v
              (source.1.2 (selectedRowIndex p source)).2 (Nat.le_of_not_gt hv)
      · exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
          (replaceSelectedControlSuffix source t suffix) t
          (source.1.2 (selectedRowIndex p source)).2 q hq).trans
          (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_otherRow
            source t suffix q hq)
  · rfl

/-- This equivalence is restricted to a call at the update time. It makes
no assertion about future calls on sources with no call through this time. -/
theorem firstCollectionCall_eq_iff_replaceSelectedControlSuffix
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta)) ↔
      firstCollectionCall rate rewards C_star C_h
        (replaceSelectedControlSuffix source t suffix) = some (u, (t, theta)) := by
  constructor
  · exact firstCollectionCall_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h source u t theta suffix
  · intro hcall
    have hrestore := firstCollectionCall_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h (replaceSelectedControlSuffix source t suffix)
      u t theta (source.1.2 (selectedRowIndex p source)).2 hcall
    simpa only [replaceSelectedControlSuffix_restore] using hrestore

/-- The actual call records retain the same incoming collection payload,
ledger, saved proposal, cutoff and prechoice parameter. Their row fields
remain those of their respective complete sources. -/
theorem actual_call_records_of_replaceSelectedControlSuffix
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta))) :
    ∃ (n : ℕ) (a b : RoundRecord (p := p) (rate := rate))
        (old : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
      (completeSuffixRecords rate source rewards C_star C_h)[n]? = some a ∧
      (completeSuffixRecords rate (replaceSelectedControlSuffix source t suffix)
        rewards C_star C_h)[n]? = some b ∧
      a.input.time = t ∧ b.input.time = t ∧
      a.input.state = b.input.state ∧
      a.input.state.coordinator = .collection old ledger saved ∧
      b.input.state.coordinator = .collection old ledger saved ∧
      ledger.cutoff = u.val + 1 ∧
      collectionCallAt a = some (u, theta) ∧ collectionCallAt b = some (u, theta) ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? a.input = some theta ∧
      ReferenceLaterSamplerParameterMeasurability.parameters? b.input = some theta := by
  obtain ⟨n, r, hr, htime, hlocal, _⟩ :=
    (firstCollectionCall_spec rewards C_star C_h source u t theta).mp hcall
  obtain ⟨active, hlaunch⟩ := launch_of_record rate rewards C_star C_h source n r hr
  have hcalendar := complete_record_time rate rewards C_star C_h source n r hr
  rw [htime] at hcalendar
  obtain ⟨a, b, ha, hb, hstate, htimeAB⟩ := indexed_records_suffix_comparison
    rate rewards C_star C_h source t suffix active hlaunch (by omega) n (by omega)
  have har : a = r := Option.some.inj (ha.symm.trans hr)
  subst a
  obtain ⟨old, ledger, saved, hcoord, hcut, hparameter⟩ :=
    (collectionCallAt_spec r u theta).mp hlocal
  have hlocalB : collectionCallAt b = some (u, theta) :=
    (collectionCallOnInput_eq_of_state_eq_time_eq
      r.input b.input hstate htimeAB).symm.trans hlocal
  have hparameterB :=
    (ReferenceLaterSamplerParameterMeasurability.parameters?_eq_of_state_eq_time_eq
      r.input b.input hstate htimeAB).symm.trans hparameter
  exact ⟨n, r, b, old, ledger, saved, hr, hb, htime, htimeAB.symm.trans htime,
    hstate, hcoord, (congrArg ReferenceActivePhysicalStep.State.coordinator hstate).symm.trans
      hcoord, hcut, hlocal, hlocalB, hparameter, hparameterB⟩

/-- The strict-past evidence prefix agrees even though current controls and
the row-bearing call records may differ. No current-round evidence is used. -/
theorem strict_past_evidence_of_firstCollectionCall
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta))) :
    ∃ n : ℕ,
      physicalStart rate source rewards C_star C_h + n = t.val ∧
      ((completeSuffixRecords rate source rewards C_star C_h).take n).map
          RoundRecord.evidence =
        ((completeSuffixRecords rate (replaceSelectedControlSuffix source t suffix)
          rewards C_star C_h).take n).map RoundRecord.evidence := by
  obtain ⟨n, r, hr, htime, _, _⟩ :=
    (firstCollectionCall_spec rewards C_star C_h source u t theta).mp hcall
  obtain ⟨active, hlaunch⟩ := launch_of_record rate rewards C_star C_h source n r hr
  have hcalendar := complete_record_time rate rewards C_star C_h source n r hr
  rw [htime] at hcalendar
  obtain ⟨hstart, hlaunch'⟩ := launch_and_start_preserved
    rate rewards C_star C_h source t suffix active hlaunch (by omega)
  refine ⟨n, hcalendar.symm, ?_⟩
  rw [completeSuffixRecords_on_launch rate source rewards C_star C_h active hlaunch,
    completeSuffixRecords_on_launch rate (replaceSelectedControlSuffix source t suffix)
      rewards C_star C_h active hlaunch']
  simp only [hstart, replaceSelectedControlSuffix_selected]
  rw [ReferenceActiveStoppedPrefixCoupling.reference_run_prefix_records
      active source.1.2 (selectedRowIndex p source) rewards
      (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h) _ _ n (by omega),
    ReferenceActiveStoppedPrefixCoupling.reference_run_prefix_records
      active (replaceSelectedControlSuffix source t suffix).1.2 (selectedRowIndex p source)
      rewards (physicalStart rate source rewards C_star C_h)
      (p.T - physicalStart rate source rewards C_star C_h) _ _ n (by omega)]
  exact (run_prefix_suffix_comparison rate rewards C_star C_h
    source t suffix active hlaunch n (by omega)).2

/-- All players' actual own histories before the call are retained, including
initialization. This uses the complete-history locality producer directly. -/
theorem strict_past_own_history_of_replaceSelectedControlSuffix
    (source : SourceInput p) (t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (player : Fin p.m) (v : Fin p.T) (hv : v.val < t.val) :
    ReferenceCompletePhysicalHistory.completeOwnHistory
        rate source rewards C_star C_h player v =
      ReferenceCompletePhysicalHistory.completeOwnHistory rate
        (replaceSelectedControlSuffix source t suffix) rewards C_star C_h player v :=
  ReferenceCompleteOwnHistoryPrefixLocality.completeOwnHistory_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h source t suffix player v hv

/-- The old freeze boundary at an actual call reads the same incoming
ledger on both sources. There is no positive-mass or renewal premise. -/
theorem oldFreezeAt?_eq_of_replaceSelectedControlSuffix
    (source : SourceInput p) (u t : Fin p.T)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (hcall : firstCollectionCall rate rewards C_star C_h source = some (u, (t, theta))) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
        rate rewards C_star C_h t source =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt? rate rewards C_star C_h t
        (replaceSelectedControlSuffix source t suffix) := by
  obtain ⟨n, a, b, old, ledger, saved, ha, hb, hta, htb, _, hca, hcb, _⟩ :=
    actual_call_records_of_replaceSelectedControlSuffix
      rate rewards C_star C_h source u t theta suffix hcall
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
      rate rewards C_star C_h t source a (List.mem_of_getElem? ha) hta old ledger saved hca,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?_eq_of_record
      rate rewards C_star C_h t (replaceSelectedControlSuffix source t suffix)
      b (List.mem_of_getElem? hb) htb old ledger saved hcb]

/-- Actual cutoff/time cells are invariant. The proof extracts an actual
parameter rather than assuming one or imposing success of assignment sampling. -/
theorem actualCollectionCallCell_iff_replaceSelectedControlSuffix
    (source : SourceInput p) (u t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    source ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u t ↔
      replaceSelectedControlSuffix source t suffix ∈
        ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
          rate rewards C_star C_h u t := by
  change (firstCollectionCall rate rewards C_star C_h source).map
      (fun c => (c.1, c.2.1)) = some (u, t) ↔
    (firstCollectionCall rate rewards C_star C_h
      (replaceSelectedControlSuffix source t suffix)).map
      (fun c => (c.1, c.2.1)) = some (u, t)
  constructor
  · intro hcell
    obtain ⟨⟨u', t', theta⟩, hc, heq⟩ := Option.map_eq_some_iff.mp hcell
    cases heq
    rw [firstCollectionCall_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h source u' t' theta suffix hc]
    rfl
  · intro hcell
    obtain ⟨⟨u', t', theta⟩, hc, heq⟩ := Option.map_eq_some_iff.mp hcell
    cases heq
    rw [(firstCollectionCall_eq_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h source u' t' theta suffix).mpr hc]
    rfl

/-- Renewal membership is equivalent on the original and updated whole
sources, including null or empty events. -/
theorem renewalCallEvent_iff_replaceSelectedControlSuffix
    (source : SourceInput p) (u t : Fin p.T)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    source ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t ↔
      replaceSelectedControlSuffix source t suffix ∈
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t := by
  have hcell := actualCollectionCallCell_iff_replaceSelectedControlSuffix
    rate rewards C_star C_h source u t suffix
  constructor
  · rintro ⟨hc, hg⟩
    have hmap := hc
    change (firstCollectionCall rate rewards C_star C_h source).map
      (fun c => (c.1, c.2.1)) = some (u, t) at hmap
    obtain ⟨⟨u', t', theta⟩, hcall, heq⟩ := Option.map_eq_some_iff.mp hmap
    cases heq
    refine ⟨hcell.mp hc, ?_⟩
    rwa [← oldFreezeAt?_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h source u' t' theta suffix hcall]
  · rintro ⟨hc, hg⟩
    have hmap := hc
    change (firstCollectionCall rate rewards C_star C_h
      (replaceSelectedControlSuffix source t suffix)).map
      (fun c => (c.1, c.2.1)) = some (u, t) at hmap
    obtain ⟨⟨u', t', theta⟩, hcall, heq⟩ := Option.map_eq_some_iff.mp hmap
    cases heq
    have hcallOriginal := (firstCollectionCall_eq_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h source u' t' theta suffix).mpr hcall
    refine ⟨hcell.mpr hc, ?_⟩
    rwa [oldFreezeAt?_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h source u' t' theta suffix hcallOriginal]

/-- The updated renewal source is the existing source update with the
membership proof just produced. The whole original source carrier is retained. -/
def renewalSourceWithSuffix (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t :=
  ⟨replaceSelectedControlSuffix z.val t suffix,
    (renewalCallEvent_iff_replaceSelectedControlSuffix
      rate rewards C_star C_h z.val u t suffix).mp z.property⟩

/-- The subtype constructor performs exactly the prescribed source update. -/
theorem renewalSourceWithSuffix_val (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix).val =
      replaceSelectedControlSuffix z.val t suffix := rfl

/-- The complete reconstructed parameter is exactly equal on the two
renewal subtypes. Membership of the new source is a conclusion of locality. -/
theorem renewalCallParameter_eq_of_replaceSelectedControlSuffix
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t
        (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) := by
  have hcall := ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
    rate rewards C_star C_h u t z
  have hupdated := firstCollectionCall_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h z.val u t _ suffix hcall
  have hnew := ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
    rate rewards C_star C_h u t (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix)
  exact congrArg (fun call => call.2.2) (Option.some.inj (hupdated.symm.trans hnew))

/-- The produced renewal records share the actual clock result, instruction,
operation ledger and successful prechoice reconstruction. The new record's
core is proved from its incoming state. Assignment sampling may still fail. -/
theorem actual_renewal_reconstruction_of_replaceSelectedControlSuffix
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ∃ (a b : RoundRecord (p := p) (rate := rate))
        (old : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
      a ∈ completeSuffixRecords rate z.val rewards C_star C_h ∧
      b ∈ completeSuffixRecords rate (replaceSelectedControlSuffix z.val t suffix)
        rewards C_star C_h ∧
      a.input.time = t ∧ b.input.time = t ∧ a.input.state = b.input.state ∧
      a.input.state.coordinator = .collection old ledger saved ∧
      b.input.state.coordinator = .collection old ledger saved ∧
      ledger.cutoff = u.val + 1 ∧ ledger.freezeAt ≤ t.val + 1 ∧
      ∃ (started : CoordinatorPhaseClock.StartRoundResult p)
        (coreA : CoordinatorRoundDispatch.CollectionCoreValid
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
            rate u a.input old ledger saved))
        (coreB : CoordinatorRoundDispatch.CollectionCoreValid
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
            rate u b.input old ledger saved))
        (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p),
        CoordinatorPhaseClock.startRound p rate.eta.val a.input.time
          (ReferenceActivePhysicalStep.collectionClock old ledger saved u) ledger.pending =
          .ok started ∧
        CoordinatorPhaseClock.startRound p rate.eta.val b.input.time
          (ReferenceActivePhysicalStep.collectionClock old ledger saved u) ledger.pending =
          .ok started ∧
        started.assignmentStart = some instruction ∧ instruction.time = t ∧
        instruction.kind = .renewal ∧
        ∃ (out : AssignmentScoreReconstruction.ReconstructedStart
            (CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                rate u a.input old ledger saved) coreA.payload_n_eq) instruction)
          (hrec : AssignmentScoreReconstruction.reconstructLaterStart
            (CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                rate u a.input old ledger saved) coreA.payload_n_eq) instruction =
            .success _ instruction out),
          AssignmentScoreReconstruction.reconstructLaterStart
            (CoordinatorRoundDispatch.collectionOperationLedger
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                rate u b.input old ledger saved) coreB.payload_n_eq) instruction =
            .success _ instruction out ∧
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
              rate rewards C_star C_h u t z =
            LaterAssignmentStartMeasurability.selectedSamplerParameters old
              (CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                  rate u a.input old ledger saved) coreA.payload_n_eq)
              instruction out hrec ∧
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
              rate rewards C_star C_h u t
              (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) =
            LaterAssignmentStartMeasurability.selectedSamplerParameters old
              (CoordinatorRoundDispatch.collectionOperationLedger
                (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
                  rate u a.input old ledger saved) coreA.payload_n_eq)
              instruction out hrec := by
  obtain ⟨d⟩ := ReferenceFirstCollectionRenewalAuxiliaryLaw.actual_renewal_call_parameters
    rate rewards C_star C_h u t z
  obtain ⟨n, hn⟩ := List.mem_iff_getElem?.mp d.record_mem
  obtain ⟨active, hlaunch⟩ := launch_of_record rate rewards C_star C_h z.val n d.record hn
  have hcalendar := complete_record_time rate rewards C_star C_h z.val n d.record hn
  rw [d.time_eq] at hcalendar
  obtain ⟨a, b, ha, hb, hstate, htime⟩ := indexed_records_suffix_comparison
    rate rewards C_star C_h z.val t suffix active hlaunch (by omega) n (by omega)
  have had : a = d.record := Option.some.inj (ha.symm.trans hn)
  subst a
  have hview :
      ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u b.input d.old d.ledger d.saved =
      { ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
          rate u d.record.input d.old d.ledger d.saved with row := b.input.row } := by
    simp only [ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView,
      ReferenceActivePhysicalStep.collectionInput]
    rw [← hstate, ← htime]
  have coreB : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
        rate u b.input d.old d.ledger d.saved) := by
    rw [hview]
    exact ⟨d.core.payload_n_eq, d.core.ledger_valid, d.core.ledger_ready,
      d.core.assignment_eq, d.core.base_score_eq, d.core.clock_parameter_valid,
      d.core.clock_registers_valid, d.core.clock_start_time_valid,
      d.core.clock_sigma_eq, d.core.clock_cutoff_eq, d.core.ledger_sigma_eq,
      d.core.ledger_cutoff_eq, d.core.ledger_freeze_eq, d.core.ledger_cursor_eq,
      d.core.decoder_bank_valid⟩
  have hcoordB : b.input.state.coordinator = .collection d.old d.ledger d.saved :=
    (congrArg ReferenceActivePhysicalStep.State.coordinator hstate).symm.trans d.coordinator_eq
  have hclockB : CoordinatorPhaseClock.startRound p rate.eta.val b.input.time
      (ReferenceActivePhysicalStep.collectionClock d.old d.ledger d.saved u)
      d.ledger.pending = .ok d.started := by
    rw [← htime]
    exact d.clock_eq
  refine ⟨d.record, b, d.old, d.ledger, d.saved, d.record_mem,
    List.mem_of_getElem? hb, d.time_eq, htime.symm.trans d.time_eq, hstate,
    d.coordinator_eq, hcoordB, d.cutoff_eq, d.freeze_le,
    d.started, d.core, coreB, d.instruction, d.clock_eq, hclockB,
    d.instruction_eq, d.instruction_time.trans d.time_eq, d.renewal,
    d.out, d.reconstruction_eq, ?_, d.parameter_eq, ?_⟩
  · exact d.reconstruction_eq
  · exact (renewalCallParameter_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z suffix).symm.trans d.parameter_eq

/-- The analytical renewal PMF uses the same parameter after the justified
source update, rather than a newly chosen anchor or weight vector. -/
theorem renewalSlowSetPMF_eq_of_replaceSelectedControlSuffix
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF
        rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF
        rate rewards C_star C_h u t
        (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) := by
  unfold ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSlowSetPMF
  simp only [renewalCallParameter_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h u t z suffix]

/-- Equality holds for every analytical scalar, including categorical
boundary values. No almost-sure exception or positive event mass is needed. -/
theorem renewalScalarSample_eq_of_replaceSelectedControlSuffix
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (v : ContinuousControlSlice.Scalar) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample
        rate rewards C_star C_h u t z v =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample
        rate rewards C_star C_h u t
        (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) v := by
  have hmass : ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAtomMass
      rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAtomMass
        rate rewards C_star C_h u t
        (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) := by
    funext i
    unfold ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAtomMass
    rw [renewalSlowSetPMF_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z suffix]
  unfold ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalScalarSample
  simp only [hmass]

/-- The same whole auxiliary array gives the same analytical renewal draw.
The physical source update changes none of its coordinates. -/
theorem renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p)
    (a : ReferenceFirstCollectionRenewalAuxiliaryLaw.AuxiliaryArray p) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u t z a =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
        rate rewards C_star C_h u t
        (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) a :=
  renewalScalarSample_eq_of_replaceSelectedControlSuffix rate rewards C_star C_h
    u t z suffix (a (t, 1))

/-- Pointwise locality on every renewal source. The first call, old freeze,
whole parameter and all players' strict-past histories are compared together.
Every conditional input is an actual renewal-event membership proof. -/
theorem renewalSource_past_locality
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    firstCollectionCall rate rewards C_star C_h
        (replaceSelectedControlSuffix z.val t suffix) =
      some (u, (t, ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z)) ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
        rate rewards C_star C_h t z.val =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
        rate rewards C_star C_h t (replaceSelectedControlSuffix z.val t suffix) ∧
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t z =
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
        rate rewards C_star C_h u t
        (renewalSourceWithSuffix rate rewards C_star C_h u t z suffix) ∧
    ∀ (player : Fin p.m) (v : Fin p.T), v.val < t.val →
      ReferenceCompletePhysicalHistory.completeOwnHistory
          rate z.val rewards C_star C_h player v =
        ReferenceCompletePhysicalHistory.completeOwnHistory rate
          (replaceSelectedControlSuffix z.val t suffix) rewards C_star C_h player v := by
  have hcall := ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
    rate rewards C_star C_h u t z
  refine ⟨firstCollectionCall_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z.val u t _ suffix hcall,
    oldFreezeAt?_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h z.val u t _ suffix hcall,
    renewalCallParameter_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t z suffix, ?_⟩
  intro player v hv
  exact strict_past_own_history_of_replaceSelectedControlSuffix
    rate rewards C_star C_h z.val t suffix player v hv

/-- Locality lifts through the existing whole-source/whole-array marginal.
The universal suffix is inside the almost-everywhere conclusion, so a later
consumer can choose it after observing any extension coordinates. This does
not assert that the updated physical source has its original marginal law. -/
theorem ae_renewalLiftLaw_past_locality
    (u t : Fin p.T) :
    ∀ᵐ wv ∂ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw
        rate rewards C_star C_h u t,
      ∀ suffix : Fin p.T → ContinuousLearningRows.TimeControl p,
        firstCollectionCall rate rewards C_star C_h
            (replaceSelectedControlSuffix wv.1.1.val t suffix) =
          some (u, (t, ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t wv.1.1)) ∧
        ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
            rate rewards C_star C_h t wv.1.1.val =
          ReferenceFirstCollectionRenewalAuxiliaryLaw.oldFreezeAt?
            rate rewards C_star C_h t (replaceSelectedControlSuffix wv.1.1.val t suffix) ∧
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t wv.1.1 =
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t
            (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix) ∧
        ∀ (player : Fin p.m) (v : Fin p.T), v.val < t.val →
          ReferenceCompletePhysicalHistory.completeOwnHistory
              rate wv.1.1.val rewards C_star C_h player v =
            ReferenceCompletePhysicalHistory.completeOwnHistory rate
              (replaceSelectedControlSuffix wv.1.1.val t suffix)
              rewards C_star C_h player v := by
  have hbase := Filter.Eventually.of_forall
    (f := ae (ReferenceFirstCollectionRenewalFibreExtension.renewalBaseLaw
      rate rewards C_star C_h u t))
    fun w (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) =>
      renewalSource_past_locality rate rewards C_star C_h u t w.1 suffix
  rw [← ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw_map_fst
    rate rewards C_star C_h u t] at hbase
  exact ae_of_ae_map measurable_fst.aemeasurable hbase

/-- For every point of the extension, the old and updated source evaluate
every candidate assignment vector at exactly the same reconstructed parameter.
This compares sampler evaluations and makes no current-vector identification. -/
theorem renewalLiftOutcome_eq_of_replaceSelectedControlSuffix
    (u t : Fin p.T)
    (wv : ReferenceFirstCollectionRenewalFibreExtension.RenewalBase
      rate rewards C_star C_h u t × CheckedAssignmentSample.AssignmentVector p)
    (suffix : Fin p.T → ContinuousLearningRows.TimeControl p) :
    ReferenceFirstCollectionRenewalFibreExtension.renewalLiftOutcome
        rate rewards C_star C_h u t wv =
      AssignmentParameterFibreKernel.successfulSlowSet p
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
          rate rewards C_star C_h u t
          (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix)) wv.2 := by
  unfold ReferenceFirstCollectionRenewalFibreExtension.renewalLiftOutcome
  rw [renewalCallParameter_eq_of_replaceSelectedControlSuffix
    rate rewards C_star C_h u t wv.1.1 suffix]

/-- The original analytical vector still realizes the same auxiliary set
using the updated source's equal parameter and the same whole seed array.
The existing outcome theorem supplies the only almost-sure exception. -/
theorem ae_renewalLiftLaw_outcome_of_replaceSelectedControlSuffix
    (u t : Fin p.T) :
    ∀ᵐ wv ∂ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw
        rate rewards C_star C_h u t,
      ∀ suffix : Fin p.T → ContinuousLearningRows.TimeControl p,
        AssignmentParameterFibreKernel.successfulSlowSet p
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t
            (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix)) wv.2 =
          some (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u t
            (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix) wv.1.2) := by
  filter_upwards [ReferenceFirstCollectionRenewalFibreExtension.ae_renewalLiftLaw_outcome
    rate rewards C_star C_h u t] with wv hrealize
  intro suffix
  rw [← renewalCallParameter_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t wv.1.1 suffix,
    ← renewalAuxiliarySample_eq_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t wv.1.1 suffix]
  exact hrealize

/-- Joint form for chronological consumers: on the existing analytical
extension one retains actual incoming records, the whole parameter, strict
physical past, and same-parameter outcome realization. Each updated source's
renewal membership is already proved by `renewalSourceWithSuffix`. -/
theorem ae_renewalLiftLaw_actual_call_and_outcome
    (u t : Fin p.T) :
    ∀ᵐ wv ∂ReferenceFirstCollectionRenewalFibreExtension.renewalLiftLaw
        rate rewards C_star C_h u t,
      ∀ suffix : Fin p.T → ContinuousLearningRows.TimeControl p,
        (∃ (n : ℕ) (a b : RoundRecord (p := p) (rate := rate))
            (old : Payload rate) (ledger : Ledger rate) (saved : Option (Fin p.T × Bool)),
          (completeSuffixRecords rate wv.1.1.val rewards C_star C_h)[n]? = some a ∧
          (completeSuffixRecords rate (replaceSelectedControlSuffix wv.1.1.val t suffix)
            rewards C_star C_h)[n]? = some b ∧
          a.input.time = t ∧ b.input.time = t ∧ a.input.state = b.input.state ∧
          a.input.state.coordinator = .collection old ledger saved ∧
          b.input.state.coordinator = .collection old ledger saved ∧
          ledger.cutoff = u.val + 1 ∧
          collectionCallAt a = some (u,
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
              rate rewards C_star C_h u t wv.1.1) ∧
          collectionCallAt b = some (u,
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
              rate rewards C_star C_h u t wv.1.1)) ∧
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t wv.1.1 =
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t
            (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix) ∧
        (∀ (player : Fin p.m) (v : Fin p.T), v.val < t.val →
          ReferenceCompletePhysicalHistory.completeOwnHistory
              rate wv.1.1.val rewards C_star C_h player v =
            ReferenceCompletePhysicalHistory.completeOwnHistory rate
              (replaceSelectedControlSuffix wv.1.1.val t suffix)
              rewards C_star C_h player v) ∧
        AssignmentParameterFibreKernel.successfulSlowSet p
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
            rate rewards C_star C_h u t
            (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix)) wv.2 =
          some (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalAuxiliarySample
            rate rewards C_star C_h u t
            (renewalSourceWithSuffix rate rewards C_star C_h u t wv.1.1 suffix) wv.1.2) := by
  filter_upwards [ae_renewalLiftLaw_past_locality rate rewards C_star C_h u t,
    ae_renewalLiftLaw_outcome_of_replaceSelectedControlSuffix
      rate rewards C_star C_h u t] with wv hpast hrealize
  intro suffix
  have hcall := ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
    rate rewards C_star C_h u t wv.1.1
  obtain ⟨n, a, b, old, ledger, saved, ha, hb, hta, htb, hstate, hca, hcb,
    hcut, hcallA, hcallB, _⟩ := actual_call_records_of_replaceSelectedControlSuffix
      rate rewards C_star C_h wv.1.1.val u t _ suffix hcall
  exact ⟨⟨n, a, b, old, ledger, saved, ha, hb, hta, htb, hstate, hca, hcb,
      hcut, hcallA, hcallB⟩,
    (hpast suffix).2.2.1, (hpast suffix).2.2.2, hrealize suffix⟩

end Bandits.Support.ReferenceFirstCollectionRenewalPastLocality
