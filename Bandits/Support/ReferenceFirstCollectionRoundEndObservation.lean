/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEmptyTailObservation
public import Bandits.Support.PhaseServiceWaiting

/-!
# Round-end observation for staged first-collection service

The original staged observation factors through the selected source prefix
including the current complete control. The incoming state uses the earlier
prefix; the executed DOWN and UP tests use the public temporal identities.
Whole physical records and whole rows are never asserted to be adapted.

The natural-calendar functions below are analytical finite-horizon extensions
for `PhaseServiceWaiting`. They do not alter the operational execution.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open ReferenceSourcePrefixHistoryFiltration
open ReferenceFirstCollectionStagedConditionalService
open ReferenceFirstCollectionDownConditionalService (actualFirstCollectionDownReadout)
open ReferenceFirstCollectionUpConditionalService
  (actualFirstCollectionUpReadout positiveRewardArms positiveRewardCount)
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionRoundEndObservation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem actualRecord_input_fields
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : actualRecord rate rewards C_star C_h t z = some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  by_cases hz : actualLaunchBy rate rewards C_star C_h t.val z
  · have hl := ReferenceLocalReleaseGateChronology.sourceSeed_launch
      rate z rewards C_star C_h hz.1
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

private theorem roundInput_eq_of_fields
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (hrows : x.rows = y.rows)
    (hselected : x.selected = y.selected) (htime : x.time = y.time)
    (hrewards : x.rewards = y.rewards) : x = y := by
  cases x
  cases y
  simp_all

/-- Compare both literal positive tests using the actual temporal assembly.
The hypotheses here are comparison data, proved for source prefixes below. -/
private theorem record_positive_eq_of_temporal_reads
    (r r' : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hstate : r'.input.state = r.input.state)
    (hselected : r'.input.selected = r.input.selected)
    (htime : r'.input.time = r.input.time)
    (hrewards : r'.input.rewards = r.input.rewards)
    (hcurrent : (r.input.rows r.input.selected).2 r.input.time =
      (r'.input.rows r.input.selected).2 r.input.time)
    (hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
      ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
        ((r'.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop) :
    ReferenceActiveAffinePositiveTest.downPositive r.input =
        ReferenceActiveAffinePositiveTest.downPositive r'.input ∧
      ReferenceActiveAffinePositiveTest.upPositive r.input =
        ReferenceActiveAffinePositiveTest.upPositive r'.input := by
  have hinput : r'.input =
      ⟨r.input.state, r'.input.rows, r.input.selected, r.input.time,
        r.input.active, r.input.rewards⟩ :=
    roundInput_eq_of_fields _ _ hstate rfl hselected htime hrewards
  have hinputL : r.input =
      ⟨r.input.state, r.input.rows, r.input.selected, r.input.time,
        r.input.active, r.input.rewards⟩ :=
    roundInput_eq_of_fields _ _ rfl rfl rfl rfl rfl
  have hevidence := ReferenceActiveTemporalAssembly.computedEvidence_eq_of_temporal_reads
    r.input.state r.input.rows r'.input.rows r.input.selected r.input.time
    r.input.active r.input.rewards r.input.rewards hcurrent hpast rfl
  rw [← hinputL, ← hinput] at hevidence
  have hsender : ReferenceActivePhysicalStep.upSenderIndex r'.input =
      ReferenceActivePhysicalStep.upSenderIndex r.input := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw,
      ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw]
    change PublicDiscreteDraws.selectedFollowerDraw _ _
        ((r'.input.rows r'.input.selected).2 r'.input.time).1 =
      PublicDiscreteDraws.selectedFollowerDraw _ _
        ((r.input.rows r.input.selected).2 r.input.time).1
    rw [hselected, htime, ← hcurrent]
  have hfollowers := congrArg
    ReferenceActivePhysicalHorizon.RoundEvidence.followers hevidence
  have hgrid := congrArg
    ReferenceActivePhysicalHorizon.RoundEvidence.gridFeedback hevidence
  have hcoordinator := congrArg
    ReferenceActivePhysicalHorizon.RoundEvidence.coordinator hevidence
  change (ReferenceActivePhysicalStep.step r.input).followers =
    (ReferenceActivePhysicalStep.step r'.input).followers at hfollowers
  change (ReferenceActivePhysicalStep.step r.input).preparation.feedback.feedback =
    (ReferenceActivePhysicalStep.step r'.input).preparation.feedback.feedback at hgrid
  change (ReferenceActivePhysicalStep.step r.input).coordinator =
    (ReferenceActivePhysicalStep.step r'.input).coordinator at hcoordinator
  constructor
  · rw [ReferenceActiveAffinePositiveTest.record_downPositive,
      ReferenceActiveAffinePositiveTest.record_downPositive, hsender,
      r.output_eq, r'.output_eq, hfollowers,
      ReferenceActiveFeedbackCut.FeedbackCut.observations_eq,
      ReferenceActiveFeedbackCut.FeedbackCut.observations_eq, hgrid]
  · rw [ReferenceActiveAffinePositiveTest.record_upPositive,
      ReferenceActiveAffinePositiveTest.record_upPositive,
      r.output_eq, r'.output_eq, hcoordinator]

/-- Both actual positive readouts retain their values after replacing only
controls strictly after the current physical round. Absence is compared via
the public incoming code, so no launch or ordinary-state premise is needed. -/
theorem actual_readouts_end_factor
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t z =
        actualFirstCollectionDownReadout (rate := rate) rewards C_star C_h i t
          (sourcePrefix control0 (t.val + 1) z) ∧
      actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t z =
        actualFirstCollectionUpReadout (rate := rate) rewards C_star C_h i t
          (sourcePrefix control0 (t.val + 1) z) := by
  let pref := sourcePrefix control0 (t.val + 1) z
  have hin : incoming rate rewards C_star C_h t z =
      incoming rate rewards C_star C_h t pref := by
    rw [incoming_factor rate rewards C_star C_h control0 t z,
      incoming_factor rate rewards C_star C_h control0 t pref]
    exact congrArg (incoming rate rewards C_star C_h t)
      (sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (by omega) z).symm
  cases hr : actualRecord rate rewards C_star C_h t z with
  | none =>
      cases hr' : actualRecord rate rewards C_star C_h t pref with
      | none =>
          change actualRecord rate rewards C_star C_h t
            (sourcePrefix control0 (t.val + 1) z) = none at hr'
          simp only [actualFirstCollectionDownReadout, actualFirstCollectionUpReadout,
            hr, hr', and_self]
      | some r' =>
          simp only [incoming, hr, hr', Option.map_none, Option.map_some] at hin
          cases hin
  | some r =>
      cases hr' : actualRecord rate rewards C_star C_h t pref with
      | none =>
          simp only [incoming, hr, hr', Option.map_none, Option.map_some] at hin
          cases hin
      | some r' =>
          have hstate : r'.input.state = r.input.state := by
            apply ReferenceActivePhysicalStepMeasurability.encodeState_injective
            simpa only [incoming, hr, hr', Option.map_some, Option.some.injEq] using hin.symm
          obtain ⟨hrows, hselected, htime, hrewards⟩ :=
            actualRecord_input_fields rewards C_star C_h t z r hr
          obtain ⟨hrows', hselected', htime', hrewards'⟩ :=
            actualRecord_input_fields rewards C_star C_h t pref r' hr'
          have hselectedEq : r'.input.selected = r.input.selected := by
            rw [hselected, hselected', sourcePrefix_selected]
          have hcontrol (v : Fin p.T) (hv : v.val < t.val + 1) :
              (r'.input.rows r.input.selected).2 v =
                (r.input.rows r.input.selected).2 v := by
            rw [hrows, hrows', hselected]
            exact (sourcePrefix_control control0 (t.val + 1) z v).trans (ite_eq_left hv)
          have hcurrent : (r.input.rows r.input.selected).2 r.input.time =
              (r'.input.rows r.input.selected).2 r.input.time :=
            (hcontrol r.input.time (by rw [htime]; exact Nat.lt_succ_self t.val)).symm
          have hpast : ∀ v : Fin p.T, v.val < r.input.time.val →
              ((r.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop =
                ((r'.input.rows r.input.selected).2 v).1 ContinuousControlSlice.Label.prop := by
            intro v hv
            rw [hcontrol v (by rw [htime] at hv; omega)]
          obtain ⟨hdown, hup⟩ := record_positive_eq_of_temporal_reads r r' hstate
            hselectedEq (htime'.trans htime.symm) (hrewards'.trans hrewards.symm)
            hcurrent hpast
          have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (r'.input.row.2 t).1 =
                PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  (r.input.row.2 t).1 := by
            change PublicDiscreteDraws.selectedFollowerDraw _ _
                ((r'.input.rows r'.input.selected).2 t).1 = _
            rw [hselectedEq, hcontrol t (Nat.lt_succ_self t.val)]
            rfl
          change actualRecord rate rewards C_star C_h t
            (sourcePrefix control0 (t.val + 1) z) = some r' at hr'
          simp only [actualFirstCollectionDownReadout, actualFirstCollectionUpReadout,
            hr, hr', hdraw, hdown, hup, and_self]

private theorem mem_end_prefix_iff
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (A : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hA : MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t] A)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    z ∈ A ↔ sourcePrefix control0 (t.val + 1) z ∈ A := by
  rw [← ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t,
    sourcePrefixFiltration_succ] at hA
  obtain ⟨B, _, hB⟩ := MeasurableSpace.measurableSet_comap.mp hA
  rw [← hB]
  simp only [Set.mem_preimage,
    sourcePrefix_sourcePrefix control0 t.val (t.val + 1) (by omega)]

/-- The prechoice OLD and FORMED supports are also invariant under the
successor prefix. This uses their already proved exact-field measurability. -/
theorem supports_end_factor
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    (z ∈ OLD (rate := rate) rewards C_star C_h i t ↔
      sourcePrefix control0 (t.val + 1) z ∈ OLD (rate := rate) rewards C_star C_h i t) ∧
    (z ∈ FORMED (rate := rate) rewards C_star C_h i t ↔
      sourcePrefix control0 (t.val + 1) z ∈ FORMED (rate := rate) rewards C_star C_h i t) := by
  exact ⟨mem_end_prefix_iff control0 t _
      (measurableSet_OLD (rate := rate) rewards C_star C_h control0 i t) z,
    mem_end_prefix_iff control0 t _
      (measurableSet_FORMED (rate := rate) rewards C_star C_h control0 i t) z⟩

/-- Literal factorization of the original staged observation, at every
source point and with the whole reward table and unrestricted constants. -/
theorem X_end_factor
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    X (rate := rate) rewards C_star C_h i t z =
      X (rate := rate) rewards C_star C_h i t
        (sourcePrefix control0 (t.val + 1) z) := by
  obtain ⟨hdown, hup⟩ := actual_readouts_end_factor
    (rate := rate) rewards C_star C_h control0 i t z
  obtain ⟨hOld, hFormed⟩ := supports_end_factor
    (rate := rate) rewards C_star C_h control0 i t z
  simp only [X, Set.indicator_apply, ← hOld, ← hFormed, hdown, hup]

/-- The original staged observation is strongly measurable by round end.
No caller supplies a factorization or adaptation hypothesis. -/
theorem X_round_end_measurable
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[sourcePrefixFiltration control0 (t.val + 2)]
      (X (rate := rate) rewards C_star C_h i t) := by
  rw [show t.val + 2 = (t.val + 1) + 1 by omega, sourcePrefixFiltration_succ]
  have h := (measurable_X (rate := rate) rewards C_star C_h control0 i t).comp
    (comap_measurable (sourcePrefix control0 (t.val + 1)))
  have heq : X (rate := rate) rewards C_star C_h i t =
      (X (rate := rate) rewards C_star C_h i t) ∘ sourcePrefix control0 (t.val + 1) := by
    funext z
    exact X_end_factor (rate := rate) rewards C_star C_h control0 i t z
  rw [heq]
  exact h.stronglyMeasurable

/-- Analytical binary extension of the original staged observation. -/
def x (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : ℕ)
    (z : BootstrapPrivateRoundStreams.SourceInput p) : Bool :=
  if hn : n < p.T then
    decide (X (rate := rate) rewards C_star C_h i ⟨n, hn⟩ z = 1)
  else false

/-- Analytical extension of the deterministic positive-reward count. -/
def g (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (n : ℕ)
    (_z : BootstrapPrivateRoundStreams.SourceInput p) : ℝ :=
  if hn : n < p.T then (positiveRewardCount rewards ⟨n, hn⟩ : ℝ) else 0

/-- W's actual real observation agrees with the staged readout in range. -/
theorem observation_eq_X
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : ℕ) (hn : n < p.T) :
    PhaseServiceWaiting.observation (x (rate := rate) rewards C_star C_h) i n =
      X (rate := rate) rewards C_star C_h i ⟨n, hn⟩ := by
  funext z
  obtain hzero | hone := X_zero_or_one (rate := rate) rewards C_star C_h i ⟨n, hn⟩ z
  · simp only [PhaseServiceWaiting.observation, x, dite_eq_left hn, hzero,
      zero_ne_one, decide_false, Bool.false_eq_true, ite_false]
  · simp only [PhaseServiceWaiting.observation, x, dite_eq_left hn, hone,
      decide_true, ite_true]

/-- The binary extension has no observations beyond the physical horizon. -/
theorem x_eq_false_of_horizon_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : ℕ) (hn : p.T ≤ n)
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    x (rate := rate) rewards C_star C_h i n z = false := by
  exact dite_eq_right (Nat.not_lt.mpr hn)

/-- W's observation is zero beyond the horizon. -/
theorem observation_eq_zero_of_horizon_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (n : ℕ) (hn : p.T ≤ n) :
    PhaseServiceWaiting.observation (x (rate := rate) rewards C_star C_h) i n = 0 := by
  funext z
  rw [PhaseServiceWaiting.observation,
    x_eq_false_of_horizon_le (rate := rate) rewards C_star C_h i n hn z]
  rfl

/-- The weight extension is zero beyond the horizon. -/
theorem g_eq_zero_of_horizon_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (n : ℕ) (hn : p.T ≤ n) : g rewards n = 0 := by
  funext z
  exact dite_eq_right (Nat.not_lt.mpr hn)

/-- The exact `hX_meas` input for W, including the zero extension. -/
theorem observation_stronglyMeasurable
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (i : Fin (p.m - 1)) (n : ℕ) :
    StronglyMeasurable[sourcePrefixFiltration control0 (n + 2)]
      (PhaseServiceWaiting.observation (x (rate := rate) rewards C_star C_h) i n) := by
  by_cases hn : n < p.T
  · rw [observation_eq_X (rate := rate) rewards C_star C_h i n hn]
    exact X_round_end_measurable (rate := rate) rewards C_star C_h control0 i ⟨n, hn⟩
  · rw [observation_eq_zero_of_horizon_le
      (rate := rate) rewards C_star C_h i n (Nat.le_of_not_gt hn)]
    exact stronglyMeasurable_const

/-- The exact `hw_meas` input for W: this reward count is deterministic. -/
theorem g_stronglyMeasurable
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    StronglyMeasurable[sourcePrefixFiltration control0 (n + 1)] (g rewards n) := by
  unfold g
  exact stronglyMeasurable_const

/-- Finite cardinality bounds the literal count, without a reward premise. -/
theorem positiveRewardCount_le (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (t : Fin p.T) : positiveRewardCount rewards t ≤ p.K := by
  simpa only [positiveRewardCount, Fintype.card_fin] using
    (positiveRewardArms rewards t).card_le_univ

/-- The exact `hw_bound` input for W, at every source and calendar offset. -/
theorem g_mem_Icc (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (n : ℕ) (z : BootstrapPrivateRoundStreams.SourceInput p) :
    g rewards n z ∈ Set.Icc (0 : ℝ) (p.K : ℝ) := by
  by_cases hn : n < p.T
  · simp only [g, dite_eq_left hn, Set.mem_Icc]
    exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (positiveRewardCount_le rewards ⟨n, hn⟩)⟩
  · simp only [g, dite_eq_right hn, Set.mem_Icc, le_refl, true_and]
    exact Nat.cast_nonneg _

end Bandits.Support.ReferenceFirstCollectionRoundEndObservation

end
