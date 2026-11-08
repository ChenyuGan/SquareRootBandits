/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourceReleaseWaitingReadouts
public import Bandits.Support.ReferenceGeneratedCompleteCalendarObservation
public import Mathlib.Probability.Process.Filtration

/-!
# Original-source prefix filtration and actual incoming observations

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:376-426,459-490`,
`sources/zip4/manuscript/07_public_setup.tex:121-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The observer below is a coordinate projection on the original source, retaining
all original private coordinates and all unselected complete rows. It is not an
operational replacement seed. Source round `t.val + 1` has pre-choice field
`sourcePrefixFiltration control0 (t.val + 1)` and outcome field at `t.val + 2`.
This does not identify the logical history containing the current slow set.
No probability law, conditional service bound, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceSourcePrefixHistoryFiltration

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : ConstructorDimensions.Parameters}

/-- Keep precisely the selected controls with source offsets below `n`.
The IDs, private arrays, forwards, and all other whole rows are retained. -/
def sourcePrefix (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (z : SourceInput p) : SourceInput p :=
  ((z.1.1, Function.update z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
    ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).1,
      fun v : Fin p.T => if v.val < n then
        (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v else control0)), z.2)

theorem sourcePrefix_ids (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : SourceInput p) : (sourcePrefix control0 n z).1.1 = z.1.1 := rfl

theorem sourcePrefix_private (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : SourceInput p) : (sourcePrefix control0 n z).2 = z.2 := rfl

theorem sourcePrefix_selected (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : SourceInput p) :
    ActualInitializationPhysicalStep.selectedRowIndex p (sourcePrefix control0 n z) =
      ActualInitializationPhysicalStep.selectedRowIndex p z := rfl

theorem sourcePrefix_forward (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : SourceInput p) (q : Fin (M p)) :
    ((sourcePrefix control0 n z).1.2 q).1 = (z.1.2 q).1 := by
  by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
  · subst q
    simp only [sourcePrefix, Function.update_self]
  · simp only [sourcePrefix, Function.update_of_ne hq]

theorem sourcePrefix_otherRow (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : SourceInput p) (q : Fin (M p))
    (hq : q ≠ ActualInitializationPhysicalStep.selectedRowIndex p z) :
    (sourcePrefix control0 n z).1.2 q = z.1.2 q := by
  exact Function.update_of_ne hq _ _

theorem sourcePrefix_control (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (z : SourceInput p) (v : Fin p.T) :
    ((sourcePrefix control0 n z).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v =
      if v.val < n then (z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v else control0 := by
  simp only [sourcePrefix, Function.update_self]

theorem sourcePrefix_eq_suffix (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n < p.T) (z : SourceInput p) :
    sourcePrefix control0 n z =
      ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z ⟨n, hn⟩ (fun _ => control0) := rfl

theorem sourcePrefix_eq_self (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : p.T ≤ n) (z : SourceInput p) : sourcePrefix control0 n z = z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      simp only [sourcePrefix, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      exact ite_eq_left (v.isLt.trans_le hn)
    · exact sourcePrefix_otherRow control0 n z q hq
  · rfl

theorem sourcePrefix_sourcePrefix (control0 : ContinuousLearningRows.TimeControl p)
    (a b : ℕ) (hab : a ≤ b) (z : SourceInput p) :
    sourcePrefix control0 a (sourcePrefix control0 b z) = sourcePrefix control0 a z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      simp only [sourcePrefix, ActualInitializationPhysicalStep.selectedRowIndex,
        Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < a
      · simp only [hv, ite_true, ite_eq_left (hv.trans_le hab)]
      · simp only [hv, ite_false]
    · have hq' : q ≠ ActualInitializationPhysicalStep.selectedRowIndex p
          (sourcePrefix control0 b z) := hq
      rw [sourcePrefix_otherRow control0 a _ q hq',
        sourcePrefix_otherRow control0 b _ q hq,
        sourcePrefix_otherRow control0 a _ q hq]
  · rfl

/-- Borel measurability on the original product source space. -/
theorem measurable_sourcePrefix (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Measurable (sourcePrefix control0 n) := by
  classical
  have hJ : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hrow : Measurable (fun z : SourceInput p =>
      z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) :=
    (measurable_from_prod_countable_right (f := fun v : Fin (M p) × SourceInput p =>
      v.2.1.2 v.1) (fun q =>
        (measurable_pi_apply q).comp (measurable_snd.comp measurable_fst))).comp
      (hJ.prodMk measurable_id)
  have hcontrol : Measurable (fun z : SourceInput p => fun v : Fin p.T =>
      if v.val < n then (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v
      else control0) := by
    apply Measurable.of_eval
    intro v
    by_cases hv : v.val < n
    · simp only [ite_eq_left hv]
      exact (measurable_pi_apply v).comp (measurable_snd.comp hrow)
    · simp only [ite_eq_right hv]
      exact measurable_const
  have hrows : Measurable (fun z : SourceInput p =>
      Function.update z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).1,
          fun v : Fin p.T => if v.val < n then
            (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v else control0)) := by
    apply Measurable.of_eval
    intro q
    have hset : MeasurableSet {z : SourceInput p |
        q = ActualInitializationPhysicalStep.selectedRowIndex p z} :=
      measurableSet_eq_fun measurable_const hJ
    have hmeas : Measurable (fun z : SourceInput p =>
        if q = ActualInitializationPhysicalStep.selectedRowIndex p z then
          ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).1,
            fun v : Fin p.T => if v.val < n then
              (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 v else control0)
        else z.1.2 q) :=
      Measurable.ite hset ((measurable_fst.comp hrow).prodMk hcontrol)
        ((measurable_pi_apply q).comp (measurable_snd.comp measurable_fst))
    simpa only [Function.update_apply] using hmeas
  exact ((measurable_fst.comp measurable_fst).prodMk hrows).prodMk measurable_snd

/-- One increasing original-source filtration. The repeated initial field is
intentional: offset `t` is source round `t + 1`. -/
def sourcePrefixFiltration (control0 : ContinuousLearningRows.TimeControl p) :
    Filtration ℕ (inferInstance : MeasurableSpace (SourceInput p)) where
  seq v := (inferInstance : MeasurableSpace (SourceInput p)).comap
    (sourcePrefix control0 (v - 1))
  mono' := by
    intro a b hab
    apply MeasurableSpace.comap_le_comap_of_eq_comp
      (sourcePrefix control0 (a - 1)) (measurable_sourcePrefix control0 (a - 1))
    funext z
    exact (sourcePrefix_sourcePrefix control0 (a - 1) (b - 1)
      (Nat.sub_le_sub_right hab 1) z).symm
  le' v := (measurable_sourcePrefix control0 (v - 1)).comap_le

theorem sourcePrefixFiltration_zero_eq_one (control0 : ContinuousLearningRows.TimeControl p) :
    sourcePrefixFiltration control0 0 = sourcePrefixFiltration control0 1 := rfl

theorem sourcePrefixFiltration_succ (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    sourcePrefixFiltration control0 (n + 1) =
      (inferInstance : MeasurableSpace (SourceInput p)).comap (sourcePrefix control0 n) := by
  simp only [sourcePrefixFiltration, Nat.add_sub_cancel]

theorem sourcePrefixFiltration_round (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) : sourcePrefixFiltration control0 (t.val + 1) =
      (inferInstance : MeasurableSpace (SourceInput p)).comap
        (fun z => ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix z t (fun _ => control0)) := by
  rw [sourcePrefixFiltration_succ]
  rfl

theorem prefix_successor_restore (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    sourcePrefix control0 (t.val + 1) z =
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (sourcePrefix control0 t.val z)
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t) := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      dsimp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        sourcePrefix, ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v = t
      · subst v
        simp only [Function.update_self, ite_eq_left (Nat.lt_succ_self t.val)]
      · dsimp only [Prod.snd]
        rw [Function.update_of_ne hv]
        have hval : v.val ≠ t.val := fun h => hv (Fin.ext h)
        have heq : v.val < t.val + 1 ↔ v.val < t.val := by omega
        simp only [heq]
    · have hq' : q ≠ PrivateSourceStreams.coordinatorIndex p z.2.1.2 := hq
      dsimp only [ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex, sourcePrefix,
        ActualInitializationPhysicalStep.selectedRowIndex]
      simp only [Function.update_of_ne hq']
  · rfl

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The actual initialization crossed by this calendar boundary. -/
def actualLaunchBy (n : ℕ) (z : SourceInput p) : Prop :=
  (ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h).crossing.isSome = true ∧
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ n

/-- Stopped initialization uses only the original selected prefix, with no
conditioning on a future launch. -/
theorem actualLaunchBy_factor (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p) :
    actualLaunchBy rate rewards C_star C_h n z ↔
      actualLaunchBy rate rewards C_star C_h n (sourcePrefix control0 n z) := by
  apply ReferenceInitializationStoppedLocality.source_calendar_stopped_event_iff
    rate rewards C_star C_h z (sourcePrefix control0 n z) n hn rfl rfl
  · intro v _ u
    rw [sourcePrefix_forward]
  · intro v hv
    rw [sourcePrefix_control, ite_eq_left hv]

private theorem stopped_output_eq (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p)
    (heither : actualLaunchBy rate rewards C_star C_h n z ∨
      actualLaunchBy rate rewards C_star C_h n (sourcePrefix control0 n z)) :
    ReferenceCompletePhysicalHistory.generatedBoundary rate z rewards C_star C_h =
      ReferenceCompletePhysicalHistory.generatedBoundary rate
        (sourcePrefix control0 n z) rewards C_star C_h := by
  have h := ReferenceInitializationStoppedLocality.source_calendar_stopped_output_eq_of_event
    rate rewards C_star C_h z (sourcePrefix control0 n z) n hn rfl rfl
    (by intro v _ u; rw [sourcePrefix_forward])
    (by intro v hv; rw [sourcePrefix_control, ite_eq_left hv]) heither
  exact h.2.1

/-- A bounded actual launch keeps its exact corrected seed as well as its
elapsed time. This statement is explicitly restricted to that launch branch. -/
theorem sourcePrefix_preserves_actual_launch (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (z : SourceInput p)
    (hz : actualLaunchBy rate rewards C_star C_h n z) :
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h =
        ReferenceCompletePhysicalHistory.physicalStart rate (sourcePrefix control0 n z)
          rewards C_star C_h ∧
      ReferenceCorrectedInitializationLaunch.correctedLaunch rate z rewards C_star C_h =
        ReferenceCorrectedInitializationLaunch.correctedLaunch rate
          (sourcePrefix control0 n z) rewards C_star C_h := by
  have hout := stopped_output_eq rate rewards C_star C_h control0 n hn z (Or.inl hz)
  refine ⟨congrArg (fun b : ReferenceInitializationRun.Boundary p => ReferenceInitializationRun.elapsed p b.completed) hout, ?_⟩
  by_cases hlt : n < p.T
  · rw [sourcePrefix_eq_suffix control0 n hlt]
    exact (ReferenceGeneratedPrefixSuffixInvariance.replaceSelectedControlSuffix_preserves_actual_launch
      (rate := rate) rewards C_star C_h
      (ActualInitializationPhysicalStep.selectedRowIndex p z) ⟨n, hlt⟩
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      hz.2 z rfl (fun _ => control0) hz.1 rfl).2.2.2
  · rw [sourcePrefix_eq_self control0 n (by omega)]

theorem actualLaunchStratum_factor (control0 : ContinuousLearningRows.TimeControl p)
    (n : ℕ) (hn : n ≤ p.T) (s : ℕ) (hs : s ≤ n) (z : SourceInput p) :
    (z ∈ ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s) ↔
    (sourcePrefix control0 n z ∈
      ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s) := by
  constructor
  · intro hz
    have hby : actualLaunchBy rate rewards C_star C_h n z := ⟨hz.1, hz.2 ▸ hs⟩
    have hout := stopped_output_eq rate rewards C_star C_h control0 n hn z (Or.inl hby)
    change _ ∧ _
    exact ⟨(congrArg (fun b => b.crossing.isSome) hout).symm.trans hz.1,
      (congrArg (fun b : ReferenceInitializationRun.Boundary p => ReferenceInitializationRun.elapsed p b.completed) hout).symm.trans hz.2⟩
  · intro hz
    have hby : actualLaunchBy rate rewards C_star C_h n (sourcePrefix control0 n z) :=
      ⟨hz.1, hz.2 ▸ hs⟩
    have hout := stopped_output_eq rate rewards C_star C_h control0 n hn z (Or.inr hby)
    exact ⟨(congrArg (fun b => b.crossing.isSome) hout).trans hz.1,
      (congrArg (fun b : ReferenceInitializationRun.Boundary p => ReferenceInitializationRun.elapsed p b.completed) hout).trans hz.2⟩

/-- Actual launch strata at or before the current pre-choice boundary are
measurable in the canonical prefix field. -/
theorem actualLaunchStratum_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val) :
    MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)]
      (ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s) := by
  rw [sourcePrefixFiltration_succ]
  refine ⟨ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
    (rate := rate) rewards C_star C_h s,
    ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
      (rate := rate) rewards C_star C_h s, ?_⟩
  ext z
  exact (actualLaunchStratum_factor rate rewards C_star C_h control0 t.val
    (Nat.le_of_lt t.isLt) s hs z).symm

/-- Literal full-calendar lookup in the actual complete suffix. -/
def actualRecord (t : Fin p.T) (z : SourceInput p) :
    Option (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :=
  if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
    (ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h)[
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?
  else none

/-- The actual incoming state, in the established lossless Borel state code. -/
def incoming (t : Fin p.T) (z : SourceInput p) :
    Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) :=
  (actualRecord rate rewards C_star C_h t z).map
    fun r => ReferenceActivePhysicalStepMeasurability.encodeState r.input.state

/-- Preserve the outer option and the distinction between a false gate and
a true gate with an empty pending observation. -/
def entry (b : ℕ) (t : Fin p.T) (z : SourceInput p) :=
  (incoming rate rewards C_star C_h t z).map
    (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b t)

/-- An absent observation contributes no task; no operational state is made. -/
def pending (b : ℕ) (t : Fin p.T) (z : SourceInput p) : Finset (Fin (p.m - 1)) :=
  ((entry rate rewards C_star C_h b t z).bind Prod.snd).getD ∅

/-- The raw UP test on the actual record and that record's own stored payload. -/
def actualUp (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) : Bool :=
  ((actualRecord rate rewards C_star C_h t z).bind fun r =>
    (ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator).map
      fun M => ReferencePhysicalReleaseQuota.upFlag M r i).getD false

/-- The raw DATA test; no entry support gate is conjoined. -/
def actualData (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) : Bool :=
  ((actualRecord rate rewards C_star C_h t z).bind fun r =>
    (ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator).map
      fun M => ReferencePhysicalReleaseQuota.dataFlag M r i).getD false

/-- The raw release test; absence is false only in this observation. -/
def actualRelease (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) : Bool :=
  ((actualRecord rate rewards C_star C_h t z).bind fun r =>
    (ReferenceAssignmentPayloadPersistence.storedPayload r.input.state.coordinator).map
      fun M => ReferencePhysicalReleaseQuota.releaseFlag M r i).getD false

theorem actualRecord_eq_none_of_not_launchBy (t : Fin p.T) (z : SourceInput p)
    (hz : ¬ actualLaunchBy rate rewards C_star C_h t.val z) :
    actualRecord rate rewards C_star C_h t z = none := by
  by_cases hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val
  · have hcross : (ReferenceCompletePhysicalHistory.generatedBoundary rate z
        rewards C_star C_h).crossing = none := by
      cases h : (ReferenceCompletePhysicalHistory.generatedBoundary rate z
          rewards C_star C_h).crossing with
      | none => rfl
      | some c => exact False.elim (hz ⟨by simp only [h, Option.isSome_some], hs⟩)
    have hstart := (ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
      rate z rewards C_star C_h hcross).2.1
    change ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T at hstart
    have ht := t.isLt
    omega
  · exact ite_eq_right hs

theorem actualRecord_eq_none_of_future_start (t : Fin p.T) (z : SourceInput p)
    (hs : t.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :
    actualRecord rate rewards C_star C_h t z = none := by
  exact ite_eq_right (Nat.not_le_of_lt hs)

theorem actualRecord_eq_none_of_terminal_start (t : Fin p.T) (z : SourceInput p)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = p.T) :
    actualRecord rate rewards C_star C_h t z = none := by
  exact actualRecord_eq_none_of_future_start rate rewards C_star C_h t z (by rw [hs]; exact t.isLt)

theorem actualRecord_eq_none_of_no_crossing (t : Fin p.T) (z : SourceInput p)
    (hz : (ReferenceCompletePhysicalHistory.generatedBoundary rate z
      rewards C_star C_h).crossing = none) :
    actualRecord rate rewards C_star C_h t z = none := by
  exact actualRecord_eq_none_of_terminal_start rate rewards C_star C_h t z
    (ReferenceCorrectedInitializationLaunch.correctedLaunch_no_crossing_source
      rate z rewards C_star C_h hz).2.1

/-- A genuine launch and an in-range calendar lookup give the existing
`actualRunRecordAt`, using the same whole rows and rewards. -/
theorem actualRecord_on_launch (t : Fin p.T) (z : SourceInput p)
    (active : ReferenceActivePhysicalStep.State p rate)
    (hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z
      rewards C_star C_h = some active)
    (hs : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val) :
    actualRecord rate rewards C_star C_h t z =
      some (ReferenceAssignmentPayloadChronology.actualRunRecordAt active z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
        (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
        (by omega)
        (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
          rate z rewards C_star C_h active hlaunch)) := by
  rw [actualRecord, ite_eq_left hs,
    ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
      rate z rewards C_star C_h active hlaunch]
  have hindex : t.val - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h < p.T - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h := by have ht := t.isLt; omega
  rw [List.getElem?_eq_getElem (by
    rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hindex)]
  congr 1
  exact ReferenceLocalReleaseGateChronology.run_record_at active z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
    (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h active hlaunch)
    (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (by have h := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate z rewards C_star C_h; omega) ⟨_, hindex⟩

/-- The actual incoming encoded state factors through the strict source
prefix, including absent, future-launch and terminal-launch branches. -/
theorem incoming_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    incoming rate rewards C_star C_h t z =
      incoming rate rewards C_star C_h t (sourcePrefix control0 t.val z) := by
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hz' := (actualLaunchBy_factor rate rewards C_star C_h control0 t.val
      (Nat.le_of_lt t.isLt) z).mp hz
    obtain ⟨hstart, hlaunch⟩ := sourcePrefix_preserves_actual_launch
      rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt) z hz
    let active := ReferenceLocalReleaseGateChronology.sourceSeed
      rate z rewards C_star C_h hz.1
    have hl : ReferenceCorrectedInitializationLaunch.correctedLaunch rate z
        rewards C_star C_h = some active :=
      ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have hl' : ReferenceCorrectedInitializationLaunch.correctedLaunch rate
        (sourcePrefix control0 t.val z) rewards C_star C_h = some active := hlaunch.symm.trans hl
    rw [incoming, incoming, actualRecord_on_launch rate rewards C_star C_h t z active hl hz.2,
      actualRecord_on_launch rate rewards C_star C_h t _ active hl' hz'.2]
    simp only [Option.map_some]
    apply congrArg (fun state => some (ReferenceActivePhysicalStepMeasurability.encodeState state))
    have hs := hz.2
    have hspan : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h +
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) ≤ p.T := by
      have ht := t.isLt
      omega
    have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h active hl
    have hrun := ReferenceActiveTemporalAssembly.run_eq_of_temporal_reads active z.1.2
      (sourcePrefix control0 t.val z).1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      hspan hmode
      (by intro v _ hv; rw [sourcePrefix_control, ite_eq_left (by omega)])
      (by intro _ _ _; rfl)
      (by
        intro _ v hv
        rw [sourcePrefix_control, ite_eq_left (by omega)])
    simpa only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt, ← hstart, sourcePrefix_selected] using hrun.1
  · have hz' : ¬ actualLaunchBy rate rewards C_star C_h t.val
        (sourcePrefix control0 t.val z) :=
      fun h => hz ((actualLaunchBy_factor rate rewards C_star C_h control0 t.val
        (Nat.le_of_lt t.isLt) z).mpr h)
    simp only [incoming, actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz,
      actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t _ hz', Option.map_none]

private theorem measurable_physicalStart :
    Measurable (fun z : SourceInput p =>
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
  have houtput := (ReferenceInitializationMeasurability.measurable_output
    p C_star C_h rate.eta rewards).comp
      ReferencePrelaunchCarriedMeasurability.measurable_sourceCoordinates
  have h := (measurable_of_countable (fun b : ReferenceInitializationRun.Boundary p =>
    ReferenceInitializationRun.elapsed p b.completed)).comp houtput
  convert h using 1
  funext z
  exact congrArg (fun x => ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed)
    (ReferencePrelaunchCarriedMeasurability.sourceCoordinates_referenceInput
      z rewards C_star C_h rate).symm

private theorem measurable_code_lookup {α : Type*} [MeasurableSpace α] (n : ℕ) :
    Measurable (fun records : List α => records[n]?) := by
  have hat := (measurable_pi_apply n).comp
    (measurable_snd.comp (ReferenceActiveHorizonMeasurability.measurable_listObservationCoordinates
      (α := α)))
  have hsome : Measurable (some : α → Option α) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  have hconvert : Measurable (fun v : Unit ⊕ α =>
      Sum.elim (fun _ => (none : Option α)) some v) :=
    Measurable.sumElim measurable_const hsome
  convert hconvert.comp hat using 1
  funext records
  dsimp only [Function.comp_apply, ReferenceActiveHorizonMeasurability.listObservationCoordinates,
    ReferenceActiveHorizonMeasurability.listObservationAt]
  cases records[n]? <;> rfl

/-- Ambient Borel measurability uses the genuine code list with its original
continuous state fibers; the raw row-bearing record space is not discretized. -/
theorem measurable_incoming (t : Fin p.T) :
    Measurable (incoming rate rewards C_star C_h t) := by
  classical
  let codes := ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode
    (rate := rate) rewards C_star C_h
  have hcodes : Measurable codes :=
    ReferenceGeneratedCompleteCalendarObservation.measurable_completeSuffixCode
      (rate := rate) rewards C_star C_h
  have hstart := measurable_physicalStart rate rewards C_star C_h
  have hindex : Measurable (fun z : SourceInput p =>
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) :=
    (measurable_of_countable (fun s : ℕ => t.val - s)).comp hstart
  have hlookup : Measurable (fun z : SourceInput p => (codes z)[
      t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?) :=
    (measurable_from_prod_countable_right
      (f := fun v : ℕ × List (ReferenceActiveHorizonMeasurability.RoundRecordCode
        (p := p) (rate := rate)) => v.2[v.1]?)
      (fun n => measurable_code_lookup n)).comp (hindex.prodMk hcodes)
  have hmap := ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate) ×
        SourceInput p => v.1.2.1)
    (measurable_fst.comp (measurable_snd.comp measurable_fst)) _ hlookup
  have hset : MeasurableSet {z : SourceInput p |
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val} :=
    hstart (MeasurableSpace.measurableSet_top : MeasurableSet {s : ℕ | s ≤ t.val})
  have hmeas : Measurable (fun z : SourceInput p =>
      if ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤ t.val then
        ((codes z)[t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h]?).map (fun c => c.2.1) else none) :=
    Measurable.ite hset hmap measurable_const
  convert hmeas using 1
  funext z
  unfold incoming actualRecord
  split_ifs
  · simp only [codes, ReferenceGeneratedCompleteCalendarObservation.completeSuffixCode,
      List.getElem?_map, Option.map_map, ReferenceActiveHorizonMeasurability.roundRecordCode,
      Function.comp_def]
  · rfl

/-- Actual incoming state adaptation at the pre-choice source field. -/
theorem incoming_measurable (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (incoming rate rewards C_star C_h t) := by
  rw [sourcePrefixFiltration_succ]
  have h := (measurable_incoming rate rewards C_star C_h t).comp
    (comap_measurable (sourcePrefix control0 t.val))
  convert h using 1
  funext z
  exact incoming_factor rate rewards C_star C_h control0 t z

theorem entry_factor (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (t : Fin p.T) (z : SourceInput p) :
    entry rate rewards C_star C_h b t z =
      entry rate rewards C_star C_h b t (sourcePrefix control0 t.val z) := by
  exact congrArg (Option.map (ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b t))
    (incoming_factor rate rewards C_star C_h control0 t z)

theorem pending_factor (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (t : Fin p.T) (z : SourceInput p) :
    pending rate rewards C_star C_h b t z =
      pending rate rewards C_star C_h b t (sourcePrefix control0 t.val z) := by
  exact congrArg (fun e => (e.bind Prod.snd).getD ∅)
    (entry_factor rate rewards C_star C_h control0 b t z)

theorem entry_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (entry rate rewards C_star C_h b t) := by
  let : MeasurableSpace (SourceInput p) := sourcePrefixFiltration control0 (t.val + 1)
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun v : ReferenceActivePhysicalStepMeasurability.StateCode p rate × SourceInput p =>
      ReferenceRetainedReleasePhaseObservation.localReleaseEntry rate b t v.1)
    ((ReferenceReleaseStrictPastFactor.measurable_localReleaseEntry rate b t).comp measurable_fst)
    _ (incoming_measurable rate rewards C_star C_h control0 t)

theorem pending_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (pending rate rewards C_star C_h b t) := by
  have hget : Measurable (fun e : Option (Finset (Fin (p.m - 1))) => e.getD ∅) := by
    have h := (Measurable.sumElim measurable_id measurable_const :
      Measurable (Sum.elim id (fun _ : PUnit => (∅ : Finset (Fin (p.m - 1)))))).comp
        (comap_measurable (Equiv.optionEquivSumPUnit (Finset (Fin (p.m - 1)))))
    convert h using 1
    funext e
    cases e <;> rfl
  have hread : Measurable (fun e : Option (Bool × Option (Finset (Fin (p.m - 1)))) =>
      (e.bind Prod.snd).getD ∅) := by
    have hsum : Measurable (Sum.elim
        (fun e : Bool × Option (Finset (Fin (p.m - 1))) => e.2.getD ∅)
        (fun _ : PUnit => (∅ : Finset (Fin (p.m - 1))))) :=
      (hget.comp measurable_snd).sumElim measurable_const
    have h := hsum.comp (comap_measurable (Equiv.optionEquivSumPUnit
      (Bool × Option (Finset (Fin (p.m - 1))))))
    convert h using 1
    funext e
    cases e <;> rfl
  exact hread.comp (entry_measurable rate rewards C_star C_h control0 b t)

/-- The same actual record as W's source calendar on a genuine launch
stratum. Membership is a branch condition, not a global success premise. -/
theorem actualRecord_source_calendar (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (z : ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s) :
    actualRecord rate rewards C_star C_h t z.val =
      ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) t.val := by
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z.val
  let fiber : ReferenceSourceReleaseWaitingReadouts.SourceFiber
      rate rewards C_star C_h s q := ⟨z, rfl⟩
  let active := ReferenceLocalReleaseGateChronology.sourceSeed rate z.val
    rewards C_star C_h z.property.1
  have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
    rate z.val rewards C_star C_h z.property.1
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z.val
      rewards C_star C_h = s := z.property.2
  rw [actualRecord_on_launch rate rewards C_star C_h t z.val active hl (by rw [hstart]; exact hs),
    ReferenceSourceReleaseWaitingReadouts.source_calendar_record_eq_actual_run_record
      rate rewards C_star C_h s q t hs fiber t.val hs le_rfl]
  simp only [hstart]
  rfl

theorem entry_source_calendar (b : ℕ) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (z : ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s) :
    entry rate rewards C_star C_h b t z.val =
      ReferenceLocalReleaseCalendarCounts.calendarEntry rate z.val rewards C_star C_h
        z.property.1 s (p.T - s) z.property.2 (by omega) b t.val := by
  let q := ActualInitializationPhysicalStep.selectedRowIndex p z.val
  let fiber : ReferenceSourceReleaseWaitingReadouts.SourceFiber
      rate rewards C_star C_h s q := ⟨z, rfl⟩
  have hcal := ReferenceSourceReleaseWaitingReadouts.source_calendar_record_eq_actual_run_record
    rate rewards C_star C_h s q t hs fiber t.val hs le_rfl
  rw [entry, incoming, actualRecord_source_calendar rate rewards C_star C_h t s hs z,
    ReferenceLocalReleaseCalendarCounts.calendarEntry, hcal]
  simp only [Option.map_some]
  have htime : (ReferenceAssignmentPayloadChronology.actualRunRecordAt
      (ReferenceLocalReleaseGateChronology.sourceSeed rate z.val rewards C_star C_h z.property.1)
      z.val.1.2 q rewards s (t.val - s) (by have ht := t.isLt; omega)
      (by simpa only [z.property.2] using
        (ReferenceLocalReleaseGateChronology.canonical_seed_release_inputs
          rate z.val rewards C_star C_h z.property.1).2.1)).input.time = t := by
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    omega
  rw [htime]

/-- Apply W's already proved entry normalization on the very same source
calendar. No new local strict-past normalization is reproved here. -/
theorem entry_source_factor_normalize (control0 : ContinuousLearningRows.TimeControl p)
    (b : ℕ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (z : ReferenceSourceReleaseWaitingReadouts.SourceFiber rate rewards C_star C_h s q) :
    entry rate rewards C_star C_h b t z.val.val =
      some (ReferenceReleaseStrictPastFactor.releaseEntries rate rewards C_star C_h
        q t s hs control0 b
        (ReferenceReleaseStrictPastFactor.normalize rate rewards C_star C_h q t s hs control0
          (ReferenceSourceReleaseWaitingReadouts.retainedLaunchOfSource
            rate rewards C_star C_h s q t hs control0 z))
        ⟨t.val - s, by omega⟩) := by
  rw [entry_source_calendar rate rewards C_star C_h b t s hs z.val]
  exact ReferenceSourceReleaseWaitingReadouts.source_calendar_entry_factor_normalize
    rate rewards C_star C_h s q t hs control0 z b t.val hs le_rfl ⟨t.val - s, by omega⟩ rfl

theorem pending_source_calendar (b : ℕ) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (z : ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s) :
    pending rate rewards C_star C_h b t z.val =
      (ReferenceLocalReleaseWaitingPaths.calendarPendingReadout rate rewards C_star C_h
        s (by omega) b z t.val).getD ∅ := by
  rw [pending, entry_source_calendar rate rewards C_star C_h b t s hs z]
  unfold ReferenceLocalReleaseWaitingPaths.calendarPendingReadout
    ReferenceLocalReleaseCalendarCounts.calendarPending
    ReferenceLocalReleaseCalendarCounts.calendarEntry
  cases hrec : ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) t.val with
  | none => rfl
  | some r =>
      simp only [Option.map_some, Option.bind_some]
      unfold ReferenceRetainedReleasePhaseObservation.localReleaseEntry
      cases ReferenceRetainedReleasePhaseObservation.localReleaseGate rate b r.input.time
          (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) with
      | false => rfl
      | true =>
          simp only [ite_true]
          cases ReferenceRetainedReleasePhaseObservation.localStoredPayload
            (ReferenceActivePhysicalStepMeasurability.encodeState r.input.state) <;> rfl

theorem flags_source_calendar (b : ℕ) (i : Fin (p.m - 1))
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)
    (z : ReferenceSourceReleaseWaitingReadouts.SourceEvent rate rewards C_star C_h s) :
    actualUp rate rewards C_star C_h i t z.val =
        ReferenceLocalReleaseWaitingPaths.upObservation rate rewards C_star C_h
          s (by omega) b i t.val z ∧
      actualData rate rewards C_star C_h i t z.val =
        ReferenceLocalReleaseWaitingPaths.dataObservation rate rewards C_star C_h
          s (by omega) b i t.val z ∧
      actualRelease rate rewards C_star C_h i t z.val =
        ReferenceLocalReleaseWaitingPaths.releaseObservation rate rewards C_star C_h
          s (by omega) b i t.val z := by
  unfold actualUp actualData actualRelease
  rw [actualRecord_source_calendar rate rewards C_star C_h t s hs z]
  unfold ReferenceLocalReleaseWaitingPaths.upObservation
    ReferenceLocalReleaseWaitingPaths.dataObservation
    ReferenceLocalReleaseWaitingPaths.releaseObservation
    ReferenceLocalReleaseWaitingPaths.calendarUpReadout
    ReferenceLocalReleaseWaitingPaths.calendarDataReadout
    ReferenceLocalReleaseWaitingPaths.calendarReleaseReadout
    ReferenceLocalReleaseCalendarCounts.calendarUpFlag
    ReferenceLocalReleaseCalendarCounts.calendarDataFlag
    ReferenceLocalReleaseCalendarCounts.calendarReleaseFlag
    ReferenceLocalReleaseCalendarCounts.calendarFlag
  cases ReferenceLocalReleaseCalendarCounts.calendarRecord rate z.val rewards C_star C_h
      z.property.1 s (p.T - s) z.property.2 (by omega) t.val <;> exact ⟨rfl, rfl, rfl⟩

private theorem actualRecord_input_fields (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch rate z rewards C_star C_h hz.1
    have hrec := actualRecord_on_launch rate rewards C_star C_h t z _ hl hz.2
    have heq := Option.some.inj (hr.symm.trans hrec)
    subst r
    refine ⟨rfl, rfl, ?_, rfl⟩
    apply Fin.ext
    dsimp only [ReferenceAssignmentPayloadChronology.actualRunRecordAt,
      ReferenceActivePhysicalHorizon.roundInputAt]
    have hs := hz.2
    omega
  · rw [actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz] at hr
    cases hr

/-- Comparison of actual physical tests uses the literal step's own
observations, the same incoming payload, and the current selected control.
The displayed input equalities are conditional comparison data only. -/
private theorem record_flags_eq_of_temporal_reads
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : r.input.state = r'.input.state)
    (hselected : r.input.selected = r'.input.selected)
    (htime : r.input.time = r'.input.time)
    (hrewards : r.input.rewards = r'.input.rewards)
    (hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time)
    (hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
        (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop)
    (M : ReferenceActivePhysicalStep.Payload rate) (i : Fin (p.m - 1)) :
    ReferencePhysicalReleaseQuota.upFlag M r i = ReferencePhysicalReleaseQuota.upFlag M r' i ∧
      ReferencePhysicalReleaseQuota.dataFlag M r i = ReferencePhysicalReleaseQuota.dataFlag M r' i ∧
      ReferencePhysicalReleaseQuota.releaseFlag M r i = ReferencePhysicalReleaseQuota.releaseFlag M r' i := by
  rcases r with ⟨x, output, hout⟩
  rcases r' with ⟨y, output', hout'⟩
  subst output
  subst output'
  rcases x with ⟨state, rows, selected, time, active, rewards⟩
  rcases y with ⟨state', rows', selected', time', active', rewards'⟩
  dsimp only at hstate hselected htime hrewards hcurrent hpast
  subst state'
  subst selected'
  subst time'
  subst rewards'
  change (rows selected).2 time = (rows' selected).2 time at hcurrent
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    state rows rows' selected time active rewards rewards hcurrent hpast rfl
  have hown := congrArg (fun e : ReferenceActivePhysicalHorizon.RoundEvidence
    (p := p) (rate := rate) => e.ownEntries) hevidence
  have hrow : ActiveFollowerLifecycle.publicRowOfCompleteRow (rows selected) time =
      ActiveFollowerLifecycle.publicRowOfCompleteRow (rows' selected) time := by
    unfold ActiveFollowerLifecycle.publicRowOfCompleteRow
    change (rows selected).2 time = (rows' selected).2 time at hcurrent
    rw [hcurrent]
  have hrelease : ReferencePhysicalReleaseQuota.releaseFlag M
        ⟨⟨state, rows, selected, time, active, rewards⟩, _, rfl⟩ i =
      ReferencePhysicalReleaseQuota.releaseFlag M
        ⟨⟨state, rows', selected, time, active', rewards⟩, _, rfl⟩ i := by
    unfold ReferencePhysicalReleaseQuota.releaseFlag
    dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
    change ReferenceActivePhysicalHorizon.RoundRecord.ownEntries
        ⟨⟨state, rows, selected, time, active, rewards⟩, _, rfl⟩ =
      ReferenceActivePhysicalHorizon.RoundRecord.ownEntries
        ⟨⟨state, rows', selected, time, active', rewards⟩, _, rfl⟩ at hown
    simp only [hrow, hown]
    exact decide_eq_decide.mpr Iff.rfl
  refine ⟨?_, ?_, hrelease⟩
  · unfold ReferencePhysicalReleaseQuota.upFlag
    dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
    simp only [hrelease]
    congr 1
    apply decide_eq_decide.mpr
    rw [hcurrent]
  · unfold ReferencePhysicalReleaseQuota.dataFlag
    dsimp only [ReferenceActivePhysicalStep.RoundInput.row]
    simp only [hrelease]
    congr 1
    apply decide_eq_decide.mpr
    rw [hcurrent]

/-- The three raw physical flags depend on the prefix through the end of
the current round. The proof compares actual steps, not assumed predictability. -/
theorem flags_factor (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) :
    actualUp rate rewards C_star C_h i t z =
        actualUp rate rewards C_star C_h i t (sourcePrefix control0 (t.val + 1) z) ∧
      actualData rate rewards C_star C_h i t z =
        actualData rate rewards C_star C_h i t (sourcePrefix control0 (t.val + 1) z) ∧
      actualRelease rate rewards C_star C_h i t z =
        actualRelease rate rewards C_star C_h i t (sourcePrefix control0 (t.val + 1) z) := by
  have hin : incoming rate rewards C_star C_h t z =
      incoming rate rewards C_star C_h t (sourcePrefix control0 (t.val + 1) z) := by
    rw [incoming_factor rate rewards C_star C_h control0 t z,
      incoming_factor rate rewards C_star C_h control0 t (sourcePrefix control0 (t.val + 1) z),
      sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (by omega)]
  unfold incoming at hin
  unfold actualUp actualData actualRelease
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none =>
      rw [hr] at hin
      cases hr' : actualRecord rate rewards C_star C_h t (sourcePrefix control0 (t.val + 1) z) with
      | none => exact ⟨rfl, rfl, rfl⟩
      | some r' =>
          simp only [hr', Option.map_none, Option.map_some] at hin
          cases hin
  | some r =>
      rw [hr] at hin
      cases hr' : actualRecord rate rewards C_star C_h t (sourcePrefix control0 (t.val + 1) z) with
      | none =>
          simp only [hr', Option.map_none, Option.map_some] at hin
          cases hin
      | some r' =>
          rw [hr', Option.map_some, Option.map_some] at hin
          have hstate : r.input.state = r'.input.state := by
            have h := congrArg ReferenceActivePhysicalStepMeasurability.decodeState
              (Option.some.inj hin)
            simpa only [ReferenceActivePhysicalStepMeasurability.decodeState_encodeState] using h
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_input_fields rate rewards C_star C_h t z r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_input_fields rate rewards C_star C_h t _ r' hr'
          have hcurrent : r.input.row.2 r.input.time = r'.input.row.2 r'.input.time := by
            simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
              hselected, hselected', htime, htime', sourcePrefix_selected,
              sourcePrefix_control, Nat.lt_succ_self, ite_true]
          have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
              (r.input.row.2 v).1 ContinuousControlSlice.Label.prop =
                (r'.input.row.2 v).1 ContinuousControlSlice.Label.prop := by
            intro v hv
            rw [htime] at hv
            simp only [ReferenceActivePhysicalStep.RoundInput.row, hrows, hrows',
              hselected, hselected', sourcePrefix_selected, sourcePrefix_control,
              ite_eq_left (hv.trans (Nat.lt_succ_self t.val))]
          have hflags := record_flags_eq_of_temporal_reads (rate := rate) r r' hstate
            (by rw [hselected, hselected', sourcePrefix_selected]) (htime.trans htime'.symm)
            (hrewards.trans hrewards'.symm) hcurrent hpast
          simp only [Option.bind_some, hstate]
          cases ReferenceAssignmentPayloadPersistence.storedPayload r'.input.state.coordinator with
          | none => exact ⟨rfl, rfl, rfl⟩
          | some M =>
              simp only [Option.map_some, Option.getD_some]
              exact hflags M i

private theorem measurable_of_actual_launch_strata {α : Type*} [MeasurableSpace α]
    (t : Fin p.T) (f : SourceInput p → α) (absent : α)
    (hnone : ∀ z, ¬ actualLaunchBy rate rewards C_star C_h t.val z → f z = absent)
    (hstratum : ∀ s : ℕ, s ≤ t.val →
      Measurable (fun z : ReferenceSourceReleaseWaitingReadouts.SourceEvent
        rate rewards C_star C_h s => f z.val)) : Measurable f := by
  let cover : Option (Fin (t.val + 1)) → Set (SourceInput p)
    | none => {z | ¬ actualLaunchBy rate rewards C_star C_h t.val z}
    | some s => ReferenceGeneratedDownAmbiguityMeasurability.generatedLaunchFiberSet
        (rate := rate) rewards C_star C_h s.val
  have hby : MeasurableSet {z : SourceInput p | actualLaunchBy rate rewards C_star C_h t.val z} :=
    (ReferenceCorrectedLaunchMeasurability.measurableSet_generated_crossing
      rate rewards C_star C_h).inter
      ((measurable_physicalStart rate rewards C_star C_h)
        (MeasurableSpace.measurableSet_top : MeasurableSet {s : ℕ | s ≤ t.val}))
  have hcover : ∀ tag, MeasurableSet (cover tag) := by
    intro tag
    cases tag with
    | none => exact hby.compl
    | some s =>
        exact ReferenceGeneratedDownAmbiguityMeasurability.measurableSet_generatedLaunchFiberSet
          (rate := rate) rewards C_star C_h s.val
  have huniv : (⋃ tag, cover tag) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
    · exact ⟨some ⟨ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h,
        Nat.lt_succ_of_le hz.2⟩, hz.1, rfl⟩
    · exact ⟨none, hz⟩
  let pieces : (tag : Option (Fin (t.val + 1))) → cover tag → α := fun _ z => f z.val
  have hpieces : ∀ tag, Measurable (pieces tag) := by
    intro tag
    cases tag with
    | none =>
        have heq : pieces none = fun _ => absent := by
          funext z
          exact hnone z.val z.property
        rw [heq]
        exact measurable_const
    | some s => exact hstratum s.val (Nat.le_of_lt_succ s.isLt)
  have hcompatible : ∀ (i j) (z : SourceInput p) (hi : z ∈ cover i) (hj : z ∈ cover j),
      pieces i ⟨z, hi⟩ = pieces j ⟨z, hj⟩ := by intros; rfl
  have hlift := measurable_liftCover cover hcover pieces hpieces hcompatible huniv
  convert hlift using 1
  funext z
  obtain ⟨tag, htag⟩ : ∃ tag, z ∈ cover tag := by
    have hmem : z ∈ ⋃ tag, cover tag := by rw [huniv]; trivial
    exact Set.mem_iUnion.mp hmem
  rw [Set.liftCover_of_mem (S := cover) (f := pieces) (hf := hcompatible)
    (hS := huniv) (i := tag) htag]

/-- Ambient Borel readouts glued over the genuine, bounded launch strata.
The complement uses literal absent records, including no and future launch. -/
theorem measurable_flags (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (fun z : SourceInput p =>
      (actualUp rate rewards C_star C_h i t z,
        (actualData rate rewards C_star C_h i t z,
          actualRelease rate rewards C_star C_h i t z))) := by
  apply measurable_of_actual_launch_strata rate rewards C_star C_h t _ (false, false, false)
  · intro z hz
    simp only [actualUp, actualData, actualRelease,
      actualRecord_eq_none_of_not_launchBy rate rewards C_star C_h t z hz,
      Option.bind_none, Option.getD_none]
  · intro s hs
    have h := ReferenceSourceReleaseWaitingReadouts.measurable_source_waiting_observations
      rate rewards C_star C_h s (by have ht := t.isLt; omega) control0 0 t.val i
    convert h using 1
    funext z
    obtain ⟨hup, hdata, hrelease⟩ := flags_source_calendar
      rate rewards C_star C_h 0 i t s hs z
    exact Prod.ext hup (Prod.ext hdata hrelease)

/-- The raw flags are measurable after the current physical round. -/
theorem flags_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable[sourcePrefixFiltration control0 (t.val + 2)]
      (fun z : SourceInput p =>
        (actualUp rate rewards C_star C_h i t z,
          (actualData rate rewards C_star C_h i t z,
            actualRelease rate rewards C_star C_h i t z))) := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega, sourcePrefixFiltration_succ]
  have h := (measurable_flags rate rewards C_star C_h control0 i t).comp
    (comap_measurable (sourcePrefix control0 (t.val + 1)))
  convert h using 1
  funext z
  obtain ⟨hup, hdata, hrelease⟩ := flags_factor rate rewards C_star C_h control0 i t z
  exact Prod.ext hup (Prod.ext hdata hrelease)

/-- The corresponding real zero/one observations are strongly measurable
in the outcome field. No physical flag is multiplied by an entry gate. -/
theorem flags_stronglyMeasurable (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 2)]
        (fun z => if actualUp rate rewards C_star C_h i t z then (1 : ℝ) else 0) ∧
      StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 2)]
        (fun z => if actualData rate rewards C_star C_h i t z then (1 : ℝ) else 0) ∧
      StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 2)]
        (fun z => if actualRelease rate rewards C_star C_h i t z then (1 : ℝ) else 0) := by
  have h := flags_measurable rate rewards C_star C_h control0 i t
  have h01 : Measurable (fun x : Bool => if x then (1 : ℝ) else 0) :=
    measurable_of_countable _
  exact ⟨(h01.comp (measurable_fst.comp h)).stronglyMeasurable,
    (h01.comp (measurable_fst.comp (measurable_snd.comp h))).stronglyMeasurable,
    (h01.comp (measurable_snd.comp (measurable_snd.comp h))).stronglyMeasurable⟩

end Bandits.Support.ReferenceSourcePrefixHistoryFiltration

end
