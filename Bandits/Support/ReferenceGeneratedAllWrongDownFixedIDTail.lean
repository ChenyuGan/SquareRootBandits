/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedAllWrongDownEvent
public import Bandits.Support.ReferenceGeneratedDownFreshIDLocalizedTail

import Mathlib.MeasureTheory.Measure.Real
import Lean.Elab.Tactic.Omega

/-!
# All-phase wrong DOWN tail with an arbitrary identification array fixed

Sources: `sources/zip4/manuscript/08_main_theorem.tex:26-78`,
`07_public_setup.tex:123-164`, `appendix_a_local_protocol.tex:92-157`, and
`05_binary_transport.tex:20-55`, all under `sources/zip4/manuscript/`.

The retained-ID mixed and fresh estimates charge their disjoint actual birth
and reset bases jointly. Only afterwards is the original ID atom normalized.
The original selected index and all private arrays are averaged throughout.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal
open Bandits.Support.ReferenceGeneratedDownFreshIDLocalizedTail (idCylinder measurableSet_idCylinder)
open Bandits.Support.ReferenceGeneratedDownCohortFiniteUnion
  (SourceInput SourceLaw Candidate downCohortUnionEvent)

namespace Bandits.Support.ReferenceGeneratedAllWrongDownFixedIDTail

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

/-- Localizing the mixed tail to the literal retained identification array
preserves its actual birth base. No history law is an input. -/
theorem mixedDownDetector_measure_le_geometric_id
    (i : Fin (p.m - 1)) (alpha k : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (q : ℕ) :
    SourceLaw p (idCylinder ids ∩
      ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
        rate rewards C_star C_h i alpha k hAlpha w control0 q) ≤
      ((1 : ENNReal) / 2) ^ q * SourceLaw p
        (idCylinder ids ∩ {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha hAlpha k}) := by
  let a : Fin p.T := ⟨0, ConstructorDimensions.T_pos p⟩
  let Cell : Set (CompletePublicTable.IDArray p × GeneratedBootstrapRoundLaw.Past p a) :=
    {ids} ×ˢ Set.univ
  have hCell : MeasurableSet Cell := (measurableSet_singleton ids).prod MeasurableSet.univ
  have h := ReferenceGeneratedMixedDownAtBirthTail.mixedDownDetector_local_geometric_bound
    rate rewards C_star C_h i alpha k hAlpha w control0 a (Nat.zero_le _) Cell hCell q
  simpa only [Cell, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, and_true,
    ReferenceGeneratedPrelaunchDownCurrentPair.sourcePastView, idCylinder,
    Set.ofPred_and, Set.ofPred_mem_eq, SourceLaw] using h

/-- The finite original birth census retains its relative bound on every ID
cylinder, including absent and zero-mass birth strata. -/
theorem mixedDownFiniteOrdinals_measure_le_geometric_id
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (w : Candidate p) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (q : ℕ) :
    SourceLaw p (idCylinder ids ∩ ⋃ k : Fin (alpha + 1),
      ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
        rate rewards C_star C_h i alpha k.val hAlpha w control0 q) ≤
      ((1 : ENNReal) / 2) ^ q * SourceLaw p
        (idCylinder ids ∩ ⋃ k : Fin (alpha + 1),
          {z | ReferenceGeneratedPrelaunchDownPrefix.birthAt
            rate rewards C_star C_h z i alpha hAlpha k.val}) := by
  classical
  let μ := SourceLaw p
  let I := idCylinder ids
  let B := fun k : Fin (alpha + 1) =>
    {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k.val}
  let D := fun k : Fin (alpha + 1) =>
    ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha k.val hAlpha w control0 q
  have hdisjB : Pairwise (Function.onFun Disjoint (fun k => I ∩ B k)) := by
    intro k l hkl
    exact (ReferenceGeneratedDownCohortFiniteUnion.birthAt_pairwiseDisjoint
      rate rewards C_star C_h i alpha hAlpha hkl).mono
        Set.inter_subset_right Set.inter_subset_right
  have hmeasB : ∀ k, MeasurableSet (I ∩ B k) := by
    intro k
    apply (measurableSet_idCylinder ids).inter
    change MeasurableSet {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha hAlpha k.val}
    rw [← ReferenceGeneratedMixedDownPredecessor.mixedDownDetector_zero
      rate rewards C_star C_h i alpha k.val hAlpha w control0]
    exact ReferenceGeneratedMixedDownPredecessor.measurableSet_mixedDownDetector
      rate rewards C_star C_h i alpha k.val hAlpha w control0 0
  calc
    μ (I ∩ ⋃ k, D k) = μ (⋃ k, I ∩ D k) := by rw [Set.inter_iUnion]
    _ ≤ ∑ k, μ (I ∩ D k) := measure_iUnion_fintype_le μ _
    _ ≤ ∑ k : Fin (alpha + 1), ((1 : ENNReal) / 2) ^ q * μ (I ∩ B k) := by
      apply Finset.sum_le_sum
      intro k _
      exact mixedDownDetector_measure_le_geometric_id rate rewards C_star C_h
        i alpha k.val hAlpha w control0 ids q
    _ = ((1 : ENNReal) / 2) ^ q * μ (I ∩ ⋃ k, B k) := by
      rw [Set.inter_iUnion, measure_iUnion hdisjB hmeasB, tsum_fintype, Finset.mul_sum]

private theorem no_birthAt_after_actual_launch
    (i : Fin (p.m - 1)) (s alpha k : ℕ) (hs : s < p.T)
    (hsa : s < alpha) (halpha : alpha < p.T)
    (z : SourceInput p)
    (launch : ReferenceGeneratedDownQthCalendar.LaunchSource
      rate rewards C_star C_h s hs)
    (hsource : launch.val = z) :
    ¬ ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha (Nat.le_of_lt halpha) k := by
  classical
  subst z
  let x := ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput
    rate rewards C_star C_h launch.val
  let r : Fin p.T := ⟨alpha, halpha⟩
  have hElapsed : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output x).completed = s := by
    simpa only [x, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using
      launch.property.2
  have hCross : (ReferenceInitializationRun.output x).crossing.isSome = true := by
    simpa only [x, ReferenceGeneratedPrelaunchDownPrefix.sourceReferenceInput] using
      launch.property.1
  have hCompletedMul : (ReferenceInitializationRun.output x).completed *
      BootstrapDimensions.B_boot p = s := by
    dsimp only [ReferenceInitializationRun.elapsed] at hElapsed
    omega
  have hCompletedLe : (ReferenceInitializationRun.output x).completed ≤
      (BootstrapDimensions.roundBlockIndex p r).val := by
    apply (Nat.le_div_iff_mul_le (BootstrapDimensions.B_boot_pos p)).2
    rw [hCompletedMul]
    exact Nat.le_of_lt hsa
  have hRunAtOutputCompleted := ReferenceInitializationPrefixInvariance.run_at_completed
    x (BootstrapDimensions.n_boot p) le_rfl
  change ReferenceInitializationRun.run x (ReferenceInitializationRun.output x).completed =
    ReferenceInitializationRun.output x at hRunAtOutputCompleted
  have hCrossAtOutputCompleted :
      (ReferenceInitializationRun.run x (ReferenceInitializationRun.output x).completed).crossing.isSome =
        true := by
    rw [hRunAtOutputCompleted]
    exact hCross
  have hStop := ReferenceInitializationRun.run_stops_at_crossing x
    (ReferenceInitializationRun.output x).completed
    ((BootstrapDimensions.roundBlockIndex p r).val -
      (ReferenceInitializationRun.output x).completed) hCrossAtOutputCompleted
  have hRunAtRound : ReferenceInitializationRun.run x
      (BootstrapDimensions.roundBlockIndex p r).val =
        ReferenceInitializationRun.output x := by
    rw [Nat.add_sub_of_le hCompletedLe] at hStop
    exact hStop.trans hRunAtOutputCompleted
  have hCrossAtRound :
      (ReferenceInitializationRun.run x
        (BootstrapDimensions.roundBlockIndex p r).val).crossing.isSome = true := by
    rw [hRunAtRound]
    exact hCross
  have hOutputAtRound := ReferenceInitializationRun.output_eq_of_crossing x
    (BootstrapDimensions.roundBlockIndex p r).val
    (BootstrapDimensions.roundBlockIndex p r).isLt.le hCrossAtRound
  cases hpref : ReferenceGeneratedPrelaunchDownPrefix.source_prelaunch_down_prefix
      rate rewards C_star C_h launch.val i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hnone := active.val.1.property.2.1
          have hfalse : (ReferenceInitializationRun.run x
              (BootstrapDimensions.roundBlockIndex p r).val).crossing.isSome = false := by
            rw [← active.val.1.property.2.2]
            simp [hnone]
          simp only [hfalse, Bool.false_eq_true] at hCrossAtRound
      | inr inactive =>
          have hnone := inactive.val.1.property.2.1
          have hfalse : (ReferenceInitializationRun.run x
              (BootstrapDimensions.roundBlockIndex p r).val).crossing.isSome = false := by
            rw [← inactive.val.1.property.2.2]
            simp [hnone]
          simp only [hfalse, Bool.false_eq_true] at hCrossAtRound
  | inr stopped =>
      have hboundary : stopped.val.1 = ReferenceInitializationRun.output x := by
        calc
          stopped.val.1 = ReferenceInitializationRun.run x
              (BootstrapDimensions.roundBlockIndex p r).val :=
                stopped.property.2.1
          _ = ReferenceInitializationRun.output x := hOutputAtRound.symm
      have hlate : ReferenceInitializationRun.elapsed p stopped.val.1.completed < alpha := by
        rw [hboundary, hElapsed]
        exact hsa
      exact ReferenceGeneratedPrelaunchDownBirthBounds.source_prelaunch_down_stopped_prefix_no_late_birthAt
        rate rewards C_star C_h launch.val i r stopped hpref hlate k

/-- The two literal level-zero bases are disjoint on the same ID cylinder.
The fresh witness is the actual launch, before the birth's calendar round. -/
private theorem birthUnion_disjoint_freshBase_id
    (i : Fin (p.m - 1)) (alpha : Fin p.T) (w : Candidate p)
    (ids : CompletePublicTable.IDArray p) :
    Disjoint
      (idCylinder ids ∩ ⋃ k : Fin (alpha.val + 1),
        {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
          rate rewards C_star C_h z i alpha.val alpha.isLt.le k.val})
      (idCylinder ids ∩
        ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
          (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w 0) := by
  apply Set.disjoint_left.mpr
  intro z hbirth hfresh
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hbirth.2
  obtain ⟨_, s, hs, hsa, launch, hsource, _⟩ :=
    (ReferenceGeneratedDownFreshIDLocalizedTail.generatedDownFreshAllLaunchSourceEvent_zero_id_iff
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w ids z).mp hfresh
  exact no_birthAt_after_actual_launch rate rewards C_star C_h i s alpha.val k.val
    hs hsa alpha.isLt z launch hsource hk

private theorem downCohortUnion_stratum_measure_le_id
    (i : Fin (p.m - 1)) (alpha : Fin p.T) (w : Candidate p)
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p) :
    SourceLaw p (idCylinder ids ∩
      ((⋃ k : Fin (alpha.val + 1),
        ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
          rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q) ∪
        ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
          (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q)) ≤
      ((1 : ENNReal) / 2) ^ q * SourceLaw p (idCylinder ids) := by
  let μ := SourceLaw p
  let I := idCylinder ids
  let B := I ∩ ⋃ k : Fin (alpha.val + 1),
    {z : SourceInput p | ReferenceGeneratedPrelaunchDownPrefix.birthAt
      rate rewards C_star C_h z i alpha.val alpha.isLt.le k.val}
  let D := I ∩ ⋃ k : Fin (alpha.val + 1),
    ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
      rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q
  let F0 := I ∩
    ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w 0
  let Fq := I ∩
    ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q
  have hF0meas : MeasurableSet F0 :=
    ReferenceGeneratedDownFreshIDLocalizedTail.measurableSet_generatedDownFreshAllLaunchSourceEvent_id
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w 0 (Nat.zero_le _) control0 ids
  have hdisj : Disjoint B F0 := birthUnion_disjoint_freshBase_id
    rate rewards C_star C_h i alpha w ids
  have hbase : μ B + μ F0 ≤ μ I := by
    rw [← measure_union hdisj hF0meas]
    exact measure_mono (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
  have hD : μ D ≤ ((1 : ENNReal) / 2) ^ q * μ B :=
    mixedDownFiniteOrdinals_measure_le_geometric_id rate rewards C_star C_h
      i alpha.val alpha.isLt.le w control0 ids q
  have hF : μ Fq ≤ ((1 : ENNReal) / 2) ^ q * μ F0 :=
    ReferenceGeneratedDownFreshIDLocalizedTail.generatedDownFreshAllLaunchSourceEvent_measure_le_geometric_id
      (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q hqQ control0 ids
  rw [Set.inter_union_distrib_left]
  calc
    μ (D ∪ Fq) ≤ μ D + μ Fq := measure_union_le D Fq
    _ ≤ ((1 : ENNReal) / 2) ^ q * μ B +
        ((1 : ENNReal) / 2) ^ q * μ F0 := add_le_add hD hF
    _ = ((1 : ENNReal) / 2) ^ q * (μ B + μ F0) := by rw [mul_add]
    _ ≤ ((1 : ENNReal) / 2) ^ q * μ I :=
      mul_le_mul_of_nonneg_left hbase zero_le

/-- Relative retained-ID joint cohort estimate with exactly the original
receiver, physical-start and candidate indices. -/
theorem downCohortUnionEvent_measure_le_geometric_id
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (q : ℕ)
    (hqQ : q ≤ AffineBatchDecoder.quota p) :
    SourceLaw p (idCylinder ids ∩ downCohortUnionEvent
      rate rewards C_star C_h control0 q) ≤
      ((((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) * ((1 : ENNReal) / 2) ^ q) *
        SourceLaw p (idCylinder ids) := by
  classical
  let μ := SourceLaw p
  let I := idCylinder ids
  unfold downCohortUnionEvent
  simp only [Set.ofPred_mem_eq, Set.inter_iUnion]
  calc
    _ ≤ ∑ i : Fin (p.m - 1), μ (⋃ alpha : Fin p.T, ⋃ w : Candidate p,
        I ∩ ((⋃ k : Fin (alpha.val + 1),
          ReferenceGeneratedMixedDownPredecessor.mixedDownDetector
            rate rewards C_star C_h i alpha.val k.val alpha.isLt.le w control0 q) ∪
          ReferenceGeneratedDownFreshAllLaunchTail.generatedDownFreshAllLaunchSourceEvent
            (rate := rate) rewards C_star C_h i alpha.val alpha.isLt w q)) :=
      measure_iUnion_fintype_le μ _
    _ ≤ ∑ i : Fin (p.m - 1), ∑ alpha : Fin p.T, ∑ w : Candidate p,
        ((1 : ENNReal) / 2) ^ q * μ I := by
      apply Finset.sum_le_sum
      intro i _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro alpha _
      apply le_trans (measure_iUnion_fintype_le μ _)
      apply Finset.sum_le_sum
      intro w _
      exact downCohortUnion_stratum_measure_le_id rate rewards C_star C_h
        i alpha w control0 ids q hqQ
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow,
        Nat.cast_ofNat, mul_assoc, μ, I]

/-- The all-phase literal wrong-DOWN event has a retained-ID relative bound;
this uses its pointwise cohort inclusion, rather than an unconditional tail. -/
theorem generatedAllWrongDownSourceEvent_measure_le_geometric_id
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    SourceLaw p (idCylinder ids ∩
      ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
        rate rewards C_star C_h) ≤
      ((((p.m - 1 : ℕ) : ENNReal) * (p.T : ENNReal) *
        (2 : ENNReal) ^ AffineBatchDecoder.width p) *
          ((1 : ENNReal) / 2) ^ AffineBatchDecoder.quota p) *
        SourceLaw p (idCylinder ids) := by
  apply le_trans (measure_mono (Set.inter_subset_inter_right _
    (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent_subset_downCohortUnion
      rate rewards C_star C_h control0)))
  exact downCohortUnionEvent_measure_le_geometric_id rate rewards C_star C_h
    control0 ids (AffineBatchDecoder.quota p) le_rfl

/-- Every original finite fair-bit ID atom has positive mass. This uses no
restriction to good identification arrays. -/
theorem idArrayMeasure_singleton_ne_zero (ids : CompletePublicTable.IDArray p) :
    CompletePublicTable.idArrayMeasure p {ids} ≠ 0 := by
  classical
  have hbit (b : Bool) : CompletePublicTable.fairBitLaw {b} ≠ 0 := by
    have hreal : CompletePublicTable.fairBitLaw.real {b} = (1 / 2 : ℝ) := by
      cases b <;> simp
    intro hz
    simp only [measureReal_def, hz, ENNReal.toReal_zero] at hreal
    norm_num at hreal
  rw [CompletePublicTable.idArrayMeasure, Measure.pi_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro u _
  rw [Measure.pi_singleton]
  apply Finset.prod_ne_zero_iff.mpr
  intro t _
  exact hbit (ids u t)

/-- Restriction of the original source to its retained ID cylinder is exactly
the fair-bit atom mass times the stated original Dirac insertion product. -/
theorem sourceInputLaw_restrict_idCylinder (ids : CompletePublicTable.IDArray p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict (idCylinder ids) =
      CompletePublicTable.idArrayMeasure p {ids} •
        (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p)) := by
  have hI : idCylinder ids =
      ({ids} ×ˢ (Set.univ : Set (CompletePublicTable.CompleteRows p))) ×ˢ Set.univ := by
    ext z
    simp only [idCylinder, Set.mem_ofPred_eq, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
  rw [hI, BootstrapPrivateRoundStreams.sourceInputLaw,
    CompletePublicTable.publishedOutputMeasure,
    ← Measure.restrict_prod_eq_prod_univ, ← Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_singleton, Measure.prod_smul_left, Measure.prod_smul_left]

/-- The original cylinder mass is its original fair-bit atom, since all
continuous rows and the full private tuple retain probability mass one. -/
theorem sourceInputLaw_idCylinder (ids : CompletePublicTable.IDArray p) :
    BootstrapPrivateRoundStreams.sourceInputLaw p (idCylinder ids) =
      CompletePublicTable.idArrayMeasure p {ids} := by
  have h := congrArg (fun μ : Measure (SourceInput p) => μ Set.univ)
    (sourceInputLaw_restrict_idCylinder ids)
  simpa only [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] using h

/-- Exact insertion identity for the literal all-phase wrong-DOWN event. -/
theorem generatedAllWrongDownSourceEvent_id_mass
    (ids : CompletePublicTable.IDArray p) :
    SourceLaw p (idCylinder ids ∩
      ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
        rate rewards C_star C_h) =
      CompletePublicTable.idArrayMeasure p {ids} *
        (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
          (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
          (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h) := by
  have h := congrArg (fun μ : Measure (SourceInput p) => μ
      (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
        rate rewards C_star C_h)) (sourceInputLaw_restrict_idCylinder ids)
  rw [Measure.restrict_apply
    (ReferenceGeneratedAllWrongDownEvent.measurableSet_generatedAllWrongDownSourceEvent
      rate rewards C_star C_h), Measure.smul_apply, smul_eq_mul] at h
  rw [Set.inter_comm] at h
  exact h

/-- For every fixed identification array, the literal all-phase original-source
wrong-DOWN envelope has probability at most `1/(4 N²)`. All complete rows, the
original uniform J and all private arrays are averaged under the displayed
original product; no history, independence or good-array premise is supplied. -/
theorem generatedAllWrongDownSourceEvent_fixedID_measureReal_quota_bound
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) :
    (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
        (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
          rate rewards C_star C_h) ≤
      1 / (4 * (ConstructorDimensions.N p : ℝ) ^ 2) := by
  let mass := CompletePublicTable.idArrayMeasure p {ids}
  have hmass : 0 < mass.toReal :=
    ENNReal.toReal_pos (idArrayMeasure_singleton_ne_zero ids) (measure_ne_top _ _)
  have h := generatedAllWrongDownSourceEvent_measure_le_geometric_id
    rate rewards C_star C_h control0 ids
  rw [generatedAllWrongDownSourceEvent_id_mass rate rewards C_star C_h ids,
    sourceInputLaw_idCylinder ids] at h
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast] at hreal
  have hnormalized :
      (((Measure.dirac ids).prod (CompletePublicTable.completeRowsMeasure p)).prod
        (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
          (ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
            rate rewards C_star C_h) ≤
        ((((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
          (2 : ℝ) ^ AffineBatchDecoder.width p) *
          ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p) := by
    apply (mul_le_mul_iff_right₀ hmass).mp
    simpa only [mass, measureReal_def, mul_comm] using hreal
  apply hnormalized.trans
  simpa only [one_div, inv_pow] using ReferenceSuppressedDownTail.quota_union_factor_le p

end Bandits.Support.ReferenceGeneratedAllWrongDownFixedIDTail

end
