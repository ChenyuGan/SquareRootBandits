/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedUpFalseTail

/-!
# Fixed-ID original-source wrong-UP tail

The ID cylinder is retained throughout the actual numerical UP calendar.
Sources: `sources/zip4/manuscript/08_main_theorem.tex:26-78`,
`07_public_setup.tex:123-164`, `appendix_a_local_protocol.tex:92-157`,
and `05_binary_transport.tex:20-55` in the same manuscript directory.
This is an internal UP diagnostic estimate, not manuscript closure. Its named
consumer is the same-ID saved-wrong row-mean assembly, after a separately
accepted DOWN fixed-ID estimate is also available.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceGeneratedUpPrefixPositiveHalf
open Bandits.Support.ReferenceGeneratedUpSourceCalendar

namespace Bandits.Support.ReferenceGeneratedUpFalseFixedIDTail

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The retained identification array on the original source carrier. -/
def idCylinder (ids : CompletePublicTable.IDArray p) :
    Set (BootstrapPrivateRoundStreams.SourceInput p) := {z | z.1.1 = ids}

theorem measurableSet_idCylinder (ids : CompletePublicTable.IDArray p) :
    MeasurableSet (idCylinder ids) := by
  exact (measurable_fst.comp measurable_fst) (measurableSet_singleton ids)

/-- Restriction of the original rows/private product, without resampling a run. -/
def idRestrictedLaw (ids : CompletePublicTable.IDArray p) :
    Measure (BootstrapPrivateRoundStreams.SourceInput p) :=
  (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (idCylinder ids)

instance idRestrictedLaw_finite (ids : CompletePublicTable.IDArray p) :
    IsFiniteMeasure (idRestrictedLaw ids) := by
  unfold idRestrictedLaw
  infer_instance

theorem idRestrictedLaw_apply (ids : CompletePublicTable.IDArray p)
    (s : Set (BootstrapPrivateRoundStreams.SourceInput p)) :
    idRestrictedLaw ids s = BootstrapPrivateRoundStreams.sourceInputLaw p
      (idCylinder ids ∩ s) := by
  rw [idRestrictedLaw, Measure.restrict_apply' (measurableSet_idCylinder ids), Set.inter_comm]

/-- The original source product with its actual ID coordinate fixed. -/
def fixedIDSourceLaw (ids : CompletePublicTable.IDArray p) :
    Measure (BootstrapPrivateRoundStreams.SourceInput p) :=
  ((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p)

instance fixedIDSourceLaw_probability (ids : CompletePublicTable.IDArray p) :
    IsProbabilityMeasure (fixedIDSourceLaw ids) := by
  unfold fixedIDSourceLaw
  infer_instance

/-- Localizing the current-pair half identity by a coordinate retained in
its remainder preserves the exact half factor. -/
theorem actualUpPrefixPositive_id_hash_half
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) (control0 : ContinuousLearningRows.TimeControl p) (alpha ell : ℕ)
    (candidate : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (i : Fin (p.m - 1)) (ids : CompletePublicTable.IDArray p) :
    idRestrictedLaw ids
        (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
          rewards C_star C_h q t s hs control0 alpha ell candidate i) =
      ((1 : ℝ≥0∞) / 2) * idRestrictedLaw ids
        (actualUpPrefixPositiveSourceEvent (rate := rate)
          rewards C_star C_h q t s hs control0 alpha ell candidate i) := by
  let C := ReferenceGeneratedUpBatchPrefixEvent.upBatchPrefixCylinder
    (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
  let D : Set (ReferenceGeneratedAffineHashHalf.PairRemainder p q t (1, i)) :=
    {v | v.1.1 = ids}
  have hD : MeasurableSet D := by
    exact (measurable_fst.comp measurable_fst) (measurableSet_singleton ids)
  have hC : MeasurableSet C :=
    ReferenceGeneratedUpBatchPrefixEvent.measurableSet_upBatchPrefixCylinder
      (rate := rate) rewards C_star C_h q t s hs control0 alpha ell candidate i
  have heq : ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent
      (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate (C ∩ D) =
      ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent
        (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate C ∩
        idCylinder ids := by
    ext z
    simp only [ReferenceGeneratedAffineHashHalf.generatedPositiveSourceEvent,
      Set.mem_ofPred_eq, Set.mem_inter_iff, D, idCylinder,
      ReferenceSelectedAffinePairLaw.fixedPairSplit_id]
    constructor
    · rintro ⟨hz, ⟨hc, hid⟩, hp, hn⟩
      exact ⟨⟨hz, hc, hp, hn⟩, hid⟩
    · rintro ⟨⟨hz, hc, hp, hn⟩, hid⟩
      exact ⟨hz, ⟨hc, hid⟩, hp, hn⟩
  have heqHash : ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent
      (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate (C ∩ D) =
      ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent
        (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate C ∩
        idCylinder ids := by
    unfold ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent
    rw [heq]
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    tauto
  unfold idRestrictedLaw
  rw [Measure.restrict_apply
      (measurableSet_actualUpPrefixPositiveHashOneSourceEvent
        rewards C_star C_h q t s hs control0 alpha ell candidate i),
    Measure.restrict_apply
      (measurableSet_actualUpPrefixPositiveSourceEvent
        rewards C_star C_h q t s hs control0 alpha ell candidate i),
    actualUpPrefixPositiveHashOneSourceEvent_eq_generatedPositiveHashOneSourceEvent,
    actualUpPrefixPositiveSourceEvent_eq_generatedPositiveSourceEvent]
  change BootstrapPrivateRoundStreams.sourceInputLaw p
      (ReferenceGeneratedAffineHashHalf.generatedPositiveHashOneSourceEvent
        (rate := rate) rewards C_star C_h q t 1 i s hs control0 candidate C ∩
        idCylinder ids) = _
  rw [← heqHash, ← heq]
  exact ReferenceGeneratedAffineHashHalf.upGeneratedPositive_hash_half
    (rate := rate) rewards C_star C_h q t i s hs control0 candidate (C ∩ D) (hC.inter hD)

/-- Exact half-measure equality on the actual UP calendar: the disjoint union
of the current-hash-one constituents has half the measure of the disjoint
union of the corresponding unchecked attempt constituents. -/
theorem upSourceSurvivalEvent_measure_eq_half_attempt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hell : 1 ≤ ell) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) =
      ((1 : ℝ≥0∞) / 2) * idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
          rewards C_star C_h q control0 alpha ell candidate i) := by
  classical
  cases ell with
  | zero => omega
  | succ n =>
      let μ := idRestrictedLaw ids
      have hhashDisjoint := ReferenceGeneratedUpSourceCalendar.upSourceHashOne_pairwiseDisjoint
        (rate := rate) rewards C_star C_h q control0 alpha (n + 1) candidate i
      have hpositiveDisjoint := ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent_pairwiseDisjoint
        (rate := rate) rewards C_star C_h q control0 alpha (n + 1) candidate i
      have hhashMeas : ∀ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
          MeasurableSet (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i) := by
        intro c
        exact measurableSet_actualUpPrefixPositiveHashOneSourceEvent
          rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
            control0 alpha (n + 1) candidate i
      have hpositiveMeas : ∀ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
          MeasurableSet (actualUpPrefixPositiveSourceEvent (rate := rate)
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i) := by
        intro c
        exact measurableSet_actualUpPrefixPositiveSourceEvent
          rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
            control0 alpha (n + 1) candidate i
      have hpositiveMeasure :
          μ (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
              rewards C_star C_h q control0 alpha (n + 1) candidate i) =
            ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
              μ (actualUpPrefixPositiveSourceEvent (rate := rate)
                rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                  control0 alpha (n + 1) candidate i) := by
        change μ (⋃ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
          actualUpPrefixPositiveSourceEvent (rate := rate)
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i) = _
        rw [measure_iUnion hpositiveDisjoint hpositiveMeas, tsum_fintype]
      calc
        μ (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha candidate i (n + 1)) =
            ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
              μ (actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
                rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                  control0 alpha (n + 1) candidate i) := by
          change μ (⋃ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
            actualUpPrefixPositiveHashOneSourceEvent (rate := rate)
              rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                control0 alpha (n + 1) candidate i) = _
          rw [measure_iUnion hhashDisjoint hhashMeas, tsum_fintype]
        _ = ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
              ((1 : ℝ≥0∞) / 2) *
                μ (actualUpPrefixPositiveSourceEvent (rate := rate)
                  rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                    control0 alpha (n + 1) candidate i) := by
          apply Finset.sum_congr rfl
          intro c _
          exact actualUpPrefixPositive_id_hash_half
            rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
              control0 alpha (n + 1) candidate i ids
        _ = ((1 : ℝ≥0∞) / 2) *
              ∑ c : ReferenceGeneratedUpSourceCalendar.CalendarIndex p,
                μ (actualUpPrefixPositiveSourceEvent (rate := rate)
                  rewards C_star C_h q c.1 c.2.val (Nat.le_of_lt_succ c.2.isLt)
                    control0 alpha (n + 1) candidate i) := by
          rw [← Finset.mul_sum]
        _ = ((1 : ℝ≥0∞) / 2) *
              μ (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
                rewards C_star C_h q control0 alpha (n + 1) candidate i) := by
          rw [hpositiveMeasure]

/-- The source-law calendar survival event satisfies the half recurrence. -/
theorem upSourceSurvivalEvent_measure_recurrence
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hell : 1 ≤ ell) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) * idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i (ell - 1)) := by
  have hhalf := upSourceSurvivalEvent_measure_eq_half_attempt
    (rate := rate) rewards C_star C_h q ids control0 alpha candidate i ell hell hellQ
  have hsubset :
      ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
        rewards C_star C_h q control0 alpha ell candidate i ⊆
      ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha candidate i (ell - 1) := by
    by_cases hfirst : ell = 1
    · subst ell
      exact ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent_one_subset_zero
        rewards C_star C_h q control0 alpha candidate i
    · exact ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent_subset_predecessor
        rewards C_star C_h q control0 alpha ell candidate i (by omega)
  calc
    _ = ((1 : ℝ≥0∞) / 2) *
        idRestrictedLaw ids
          (ReferenceGeneratedUpSourceCalendar.upSourceAttemptEvent (rate := rate)
            rewards C_star C_h q control0 alpha ell candidate i) := hhalf
    _ ≤ ((1 : ℝ≥0∞) / 2) *
        idRestrictedLaw ids
          (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
            rewards C_star C_h q control0 alpha candidate i (ell - 1)) :=
      mul_le_mul_of_nonneg_left (measure_mono hsubset) (by positivity)

/-- Iteration through the inclusive quota gives the geometric bound with the
actual original `J=q` stratum as the base event. -/
theorem upSourceSurvivalEvent_measure_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p) (i : Fin (p.m - 1)) (ell : ℕ)
    (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) ^ ell * idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i 0) := by
  induction ell with
  | zero => simp
  | succ n ih =>
      have hnQ : n ≤ AffineBatchDecoder.quota p := by omega
      have hrec := upSourceSurvivalEvent_measure_recurrence
        (rate := rate) rewards C_star C_h q ids control0 alpha candidate i (n + 1)
          (by omega) hellQ
      have hbound := ih hnQ
      calc
        _ ≤ ((1 : ℝ≥0∞) / 2) *
            idRestrictedLaw ids
              (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
                rewards C_star C_h q control0 alpha candidate i n) := hrec
        _ ≤ ((1 : ℝ≥0∞) / 2) *
            (((1 : ℝ≥0∞) / 2) ^ n * idRestrictedLaw ids
              (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
                rewards C_star C_h q control0 alpha candidate i 0)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
        _ = ((1 : ℝ≥0∞) / 2) ^ (n + 1) *
              idRestrictedLaw ids
                (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
                  rewards C_star C_h q control0 alpha candidate i 0) := by
          rw [pow_succ]
          ac_rfl

/-- Exact finite disjoint-union measure equality for the literal all-J event. -/
theorem upSourceAllJSurvivalEvent_measure_eq_sum
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p) (i : Fin (p.m - 1)) (ell : ℕ) :
    idRestrictedLaw ids
        (ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
          rewards C_star C_h control0 alpha candidate i ell) =
      ∑ q : Fin (M p), idRestrictedLaw ids
        (ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) := by
  classical
  change idRestrictedLaw ids
      (⋃ q : Fin (M p),
        ReferenceGeneratedUpSourceCalendar.upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i ell) = _
  rw [measure_iUnion
    (ReferenceGeneratedUpSourceTail.upSourceSurvivalEvent_pairwiseDisjoint (rate := rate)
      rewards C_star C_h control0 alpha candidate i ell)
    (fun q => ReferenceGeneratedUpSourceCalendar.measurableSet_upSourceSurvivalEvent
      (rate := rate) rewards C_star C_h q control0 alpha candidate i ell), tsum_fintype]

/-- The localized numerical calendar estimate, with its literal original
selected-row base mass and no factor for the number of rows. -/
theorem upSourceSurvivalEvent_id_inter_measure_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p)
    (i : Fin (p.m - 1)) (ell : ℕ) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p
      (idCylinder ids ∩ upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) ^ ell * BootstrapPrivateRoundStreams.sourceInputLaw p
        (idCylinder ids ∩ {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q}) := by
  have h := upSourceSurvivalEvent_measure_le_geometric
    (rate := rate) rewards C_star C_h q ids control0 alpha candidate i ell hellQ
  rw [idRestrictedLaw_apply, idRestrictedLaw_apply] at h
  exact h

/-- Real-measure form of the retained-ID calendar estimate. -/
theorem upSourceSurvivalEvent_id_inter_measureReal_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (q : Fin (M p)) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p)
    (i : Fin (p.m - 1)) (ell : ℕ) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
      (idCylinder ids ∩ upSourceSurvivalEvent (rate := rate)
        rewards C_star C_h q control0 alpha candidate i ell) ≤
      ((1 : ℝ) / 2) ^ ell * (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (idCylinder ids ∩ {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q}) := by
  have h := upSourceSurvivalEvent_id_inter_measure_le_geometric
    (rate := rate) rewards C_star C_h q ids control0 alpha candidate i ell hellQ
  have hfinite : ((1 : ℝ≥0∞) / 2) ^ ell * BootstrapPrivateRoundStreams.sourceInputLaw p
      (idCylinder ids ∩ {z | ActualInitializationPhysicalStep.selectedRowIndex p z = q}) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num)) (measure_ne_top _ _)
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] using
    ENNReal.toReal_mono hfinite h

/-- Summing the retained original J masses introduces no row-count factor. -/
theorem upSourceAllJSurvivalEvent_measure_le_geometric
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (alpha : ℕ)
    (candidate : ReferenceGeneratedUpSourceTail.Candidate p)
    (i : Fin (p.m - 1)) (ell : ℕ) (hellQ : ell ≤ AffineBatchDecoder.quota p) :
    idRestrictedLaw ids
      (ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
        rewards C_star C_h control0 alpha candidate i ell) ≤
      ((1 : ℝ≥0∞) / 2) ^ ell * idRestrictedLaw ids Set.univ := by
  rw [upSourceAllJSurvivalEvent_measure_eq_sum]
  calc
    _ ≤ ∑ q : Fin (M p), ((1 : ℝ≥0∞) / 2) ^ ell * idRestrictedLaw ids
        (upSourceSurvivalEvent (rate := rate)
          rewards C_star C_h q control0 alpha candidate i 0) := by
      apply Finset.sum_le_sum
      intro q _
      exact upSourceSurvivalEvent_measure_le_geometric
        rewards C_star C_h q ids control0 alpha candidate i ell hellQ
    _ = _ := by
      rw [← Finset.mul_sum, ← upSourceAllJSurvivalEvent_measure_eq_sum,
        ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent_zero_eq_univ]

/-- The original ambiguity envelope, localized before its union bound. -/
theorem upAwaitedAmbiguityEnvelope_id_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) :
    idRestrictedLaw ids
      (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
        (rate := rate) rewards C_star C_h control0) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p * idRestrictedLaw ids Set.univ := by
  let μ := idRestrictedLaw ids
  calc
    μ (⋃ i : Fin (p.m - 1), ⋃ alpha : Fin p.T,
        ⋃ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
          ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
            rewards C_star C_h control0 alpha.val candidate i (AffineBatchDecoder.quota p))
        ≤ ∑ i : Fin (p.m - 1),
            μ (⋃ alpha : Fin p.T, ⋃ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
              ReferenceGeneratedUpSourceTail.upSourceAllJSurvivalEvent (rate := rate)
                rewards C_star C_h control0 alpha.val candidate i (AffineBatchDecoder.quota p)) :=
          measure_iUnion_fintype_le μ _
    _ ≤ ∑ i : Fin (p.m - 1), ∑ alpha : Fin p.T,
          ∑ candidate : ReferenceGeneratedUpSourceTail.Candidate p,
            ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p * μ Set.univ := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro alpha _
      apply le_trans (measure_iUnion_fintype_le μ _)
      exact Finset.sum_le_sum fun candidate _ =>
        upSourceAllJSurvivalEvent_measure_le_geometric
          (rate := rate) rewards C_star C_h ids control0 alpha.val candidate i
            (AffineBatchDecoder.quota p) (le_refl _)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ReferenceGeneratedUpSourceTail.Candidate, AffineChannelLaw.Word,
        AffineChannelLaw.Bit, Fintype.card_fun, ZMod.card, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
      rfl

/-- Pointwise physical coverage is reused under the retained-ID measure. -/
theorem generatedUpWrongSuffixPrefixEvent_id_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : CompletePublicTable.IDArray p)
    (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) :
    idRestrictedLaw ids
      (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h k) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p * idRestrictedLaw ids Set.univ := by
  exact (measure_mono
    (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent_subset_upAwaitedAmbiguityEnvelope
      (rate := rate) rewards C_star C_h control0 k)).trans
    (upAwaitedAmbiguityEnvelope_id_measure_le rewards C_star C_h ids control0)

/-- Every finite fair-bit ID array has a positive original atom. -/
theorem idArrayMeasure_singleton_ne_zero (ids : CompletePublicTable.IDArray p) :
    CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
  have hbit (b : Bool) : CompletePublicTable.fairBitLaw {b} ≠ 0 := by
    have hr : CompletePublicTable.fairBitLaw.real {b} = (1 / 2 : ℝ) := by
      cases b <;> simp only [CompletePublicTable.fairBitLaw_false_mass,
        CompletePublicTable.fairBitLaw_true_mass]
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hr
    norm_num at hr
  simp only [CompletePublicTable.idArrayMeasure, Measure.pi_singleton]
  exact Finset.prod_ne_zero_iff.mpr fun u _ =>
    Finset.prod_ne_zero_iff.mpr fun t _ => hbit (ids u t)

/-- Original product restriction is exactly its positive ID mass times the
same continuous rows/private product with the ID inserted. -/
theorem idRestrictedLaw_eq_smul (ids : CompletePublicTable.IDArray p) :
    idRestrictedLaw ids = CompletePublicTable.idArrayMeasure p {ids} • fixedIDSourceLaw ids := by
  have hc : idCylinder ids =
      ({ids} ×ˢ (Set.univ : Set (CompletePublicTable.CompleteRows p))) ×ˢ
        (Set.univ : Set (BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)) := by
    ext z
    simp only [idCylinder, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_univ, and_true]
  unfold idRestrictedLaw BootstrapPrivateRoundStreams.sourceInputLaw
    CompletePublicTable.publishedOutputMeasure
  rw [hc, ← Measure.restrict_prod_eq_prod_univ,
    ← Measure.restrict_prod_eq_prod_univ, Measure.restrict_singleton,
    Measure.prod_smul_left, Measure.prod_smul_left]
  rfl

/-- The actual wrong-UP prefix bound under the fixed-ID original product.
Only a budget already proportional to the retained ID mass is normalized. -/
theorem generatedUpWrongSuffixPrefixEvent_fixedID_measure_le
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (ids : CompletePublicTable.IDArray p) :
    fixedIDSourceLaw ids
      (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h k) ≤
      ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
        ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
  have h := generatedUpWrongSuffixPrefixEvent_id_measure_le
    (rate := rate) rewards C_star C_h ids control0 k
  rw [idRestrictedLaw_eq_smul] at h
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at h
  apply (ENNReal.mul_le_mul_iff_left (idArrayMeasure_singleton_ne_zero ids)
    (measure_ne_top (CompletePublicTable.idArrayMeasure p) {ids})).mp
  simpa only [mul_comm] using h

/-- Uniform fixed-ID UP diagnostic probability on the original source
carrier, for every whole reward table and every prefix count. -/
theorem generatedUpWrongSuffixPrefixEvent_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (ids : CompletePublicTable.IDArray p) :
    (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
      (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h k) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  have h := generatedUpWrongSuffixPrefixEvent_fixedID_measure_le
    (rate := rate) rewards C_star C_h control0 k ids
  have hhalf (n : ℕ) : ((1 : ℝ≥0∞) / 2) ^ n = (2 ^ n : ℝ≥0∞)⁻¹ := by
    rw [one_div, ← ENNReal.inv_pow]
  rw [hhalf] at h
  have hfinite : ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
      (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
        (ENNReal.pow_ne_top (by norm_num)))
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))
  have hreal := ENNReal.toReal_mono hfinite h
  have hbound : (fixedIDSourceLaw ids).real
      (ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
        (r := rate) rewards C_star C_h k) ≤
      ((p.m - 1 : ℕ) : ℝ) * p.T * 2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using hreal
  exact hbound.trans (ReferenceSuppressedDownTail.quota_union_factor_le p)

end Bandits.Support.ReferenceGeneratedUpFalseFixedIDTail

end
