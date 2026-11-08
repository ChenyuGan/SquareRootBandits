/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteInclusivePhysicalDecoderErrors
public import Bandits.Support.ReferenceCompleteOrdinaryFalseFixedIDBudget

/-!
# Fixed-ID budget for the inclusive complete decoder error

The stopped ordinary error is bounded by the complete ordinary prefix result.
The fixed-awaited ambiguity branch is covered by the retained-ID DOWN cohort
and UP ambiguity-envelope bounds on the same original source product.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput)

namespace Bandits.Support.ReferenceCompleteInclusiveDecoderFixedIDBudget

variable {p : Parameters}

private theorem stoppedOrdinaryWrongCompletionEvent_subset_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
        rate rewards C_star C_h ⊆
      ReferenceCompleteOrdinaryFalseFixedIDBudget.ordinaryWrongCompletionPrefixEvent
        rate rewards C_star C_h p.T := by
  intro z hz
  change ∃ t : Fin p.T,
      ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
        rate rewards C_star C_h z t ∧
      ReferenceCompleteOrdinaryWrongCompletionCharacterization.ordinaryWrongCompletionAt
        rate rewards C_star C_h t z at hz
  rcases hz with ⟨t, _, hwrong⟩
  change ReferenceCompleteOrdinaryFalseEventObservableLocality.ordinaryWrongCompletionPrefix
    rate rewards C_star C_h p.T z
  exact ⟨t, by omega, hwrong⟩

private theorem stoppedFixedAwaitedAmbiguityEvent_subset_downCohort_upEnvelope
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) :
    ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
        rate rewards C_star C_h ⊆
      ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) ∪
        ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
          (rate := rate) rewards C_star C_h control0 := by
  intro z hz
  change ∃ t : Fin p.T,
      ReferenceCompleteInclusivePhysicalDecoderErrors.actualInclusivePhysicalScanGate
        rate rewards C_star C_h z t ∧
      ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt
        rate rewards C_star C_h z t at hz
  obtain ⟨t, _, hsource⟩ := hz
  have hliteral :=
    (ReferenceCompleteAwaitedBatchSourceCoverage.sourceFixedAwaitedCompletionAt_iff_literal
      rate rewards C_star C_h z t).mp hsource
  rcases hliteral with hdown | hup
  · exact Or.inl
      (ReferenceAwaitedDownCohortCoverage.fixedAwaitedDownFailureAt_mem_downCohortUnionEvent
        rate rewards C_star C_h control0 z t
        ((ReferenceLiteralAwaitedAmbiguityRowObservation.literalDownAmbiguityAt_iff_fixedAwaitedDownFailureAt
          rate rewards C_star C_h z t).mp hdown))
  · exact Or.inr
      (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEvent_subset_envelope
        (rate := rate) rewards C_star C_h control0
        (ReferenceAwaitedUpDecoderErrorProbability.fixedAwaitedUpFailureAt_mem_upAwaitedAmbiguityEvent
          rate rewards C_star C_h control0 z t
          ((ReferenceLiteralAwaitedAmbiguityRowObservation.literalUpAmbiguityAt_iff_fixedAwaitedUpFailureAt
            rate rewards C_star C_h z t).mp hup)))

private theorem downCohortUnionEvent_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) :
    (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
        (ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
          rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
  let downEvent := ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
    rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)
  have hdownMeas :=
    ReferenceGeneratedDownCohortFiniteUnion.measurableSet_downCohortUnionEvent
      rate rewards C_star C_h control0 (AffineBatchDecoder.quota p) le_rfl
  have h := ReferenceGeneratedAllWrongDownFixedIDTail.downCohortUnionEvent_measure_le_geometric_id
    rate rewards C_star C_h control0 ids (AffineBatchDecoder.quota p) le_rfl
  have htransport := congrArg (fun μ : Measure (SourceInput p) => μ downEvent)
    (ReferenceGeneratedAllWrongDownFixedIDTail.sourceInputLaw_restrict_idCylinder ids)
  rw [Measure.restrict_apply hdownMeas, Set.inter_comm] at htransport
  let mass := CompletePublicTable.idArrayMeasure p {ids}
  change ReferenceGeneratedDownCohortFiniteUnion.SourceLaw p
      (ReferenceGeneratedDownFreshIDLocalizedTail.idCylinder ids ∩ downEvent) =
    mass • ν downEvent at htransport
  rw [htransport,
    ReferenceGeneratedAllWrongDownFixedIDTail.sourceInputLaw_idCylinder ids] at h
  have hmass : 0 < mass.toReal :=
    ENNReal.toReal_pos
      (ReferenceGeneratedAllWrongDownFixedIDTail.idArrayMeasure_singleton_ne_zero ids)
      (measure_ne_top _ _)
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_one,
    ENNReal.toReal_ofNat, ENNReal.toReal_natCast] at hreal
  have hnormalized : ν.real downEvent ≤
      ((((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
        (2 : ℝ) ^ AffineBatchDecoder.width p) *
        ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p) := by
    apply (mul_le_mul_iff_right₀ hmass).mp
    simpa only [mass, measureReal_def, mul_comm] using hreal
  have hfactor := ReferenceSuppressedDownTail.quota_union_factor_le p
  have hpow : ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p =
      (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
    rw [one_div, ← inv_pow]
  have hfactor' : ((((p.m - 1 : ℕ) : ℝ) * (p.T : ℝ) *
        (2 : ℝ) ^ AffineBatchDecoder.width p) *
        ((1 : ℝ) / 2) ^ AffineBatchDecoder.quota p) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
    rw [hpow]
    exact hfactor
  have hnormalized' := hnormalized.trans hfactor'
  simpa only [ν, downEvent] using hnormalized'

private theorem upAwaitedAmbiguityEnvelope_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) :
    (ReferenceGeneratedUpFalseFixedIDTail.fixedIDSourceLaw ids).real
        (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
          (rate := rate) rewards C_star C_h control0) ≤
      1 / (4 * (N p : ℝ) ^ 2) := by
  have h := ReferenceGeneratedUpFalseFixedIDTail.upAwaitedAmbiguityEnvelope_id_measure_le
    (rate := rate) rewards C_star C_h ids control0
  rw [ReferenceGeneratedUpFalseFixedIDTail.idRestrictedLaw_eq_smul] at h
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at h
  have hnormalized :
      ReferenceGeneratedUpFalseFixedIDTail.fixedIDSourceLaw ids
          (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
            (rate := rate) rewards C_star C_h control0) ≤
        ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T * 2 ^ AffineBatchDecoder.width p *
          ((1 : ℝ≥0∞) / 2) ^ AffineBatchDecoder.quota p := by
    apply (ENNReal.mul_le_mul_iff_left
      (ReferenceGeneratedUpFalseFixedIDTail.idArrayMeasure_singleton_ne_zero ids)
      (measure_ne_top (CompletePublicTable.idArrayMeasure p) {ids})).mp
    simpa only [mul_comm] using h
  have hhalf (n : ℕ) : ((1 : ℝ≥0∞) / 2) ^ n = (2 ^ n : ℝ≥0∞)⁻¹ := by
    rw [one_div, ← ENNReal.inv_pow]
  rw [hhalf] at hnormalized
  have hfinite : ((p.m - 1 : ℕ) : ℝ≥0∞) * p.T *
      2 ^ AffineBatchDecoder.width p *
        (2 ^ AffineBatchDecoder.quota p : ℝ≥0∞)⁻¹ ≠ ∞ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.natCast_ne_top _))
        (ENNReal.pow_ne_top (by norm_num)))
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))
  have hreal := ENNReal.toReal_mono hfinite hnormalized
  have hbound :
      (ReferenceGeneratedUpFalseFixedIDTail.fixedIDSourceLaw ids).real
          (ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
            (rate := rate) rewards C_star C_h control0) ≤
        ((p.m - 1 : ℕ) : ℝ) * p.T * 2 ^ AffineBatchDecoder.width p *
          (2 ^ AffineBatchDecoder.quota p : ℝ)⁻¹ := by
    simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using hreal
  exact hbound.trans (ReferenceSuppressedDownTail.quota_union_factor_le p)

/-- The actual stopped ordinary error keeps the full prelaunch and physical
records of the ordinary prefix event, so its bound is uniform in the ID array. -/
theorem stoppedOrdinaryWrongCompletionEvent_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) :
    (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
        (ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
          rate rewards C_star C_h) ≤
      1 / (2 * (N p : ℝ) ^ 2) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
  have hmono : ν.real
        (ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
          rate rewards C_star C_h) ≤
      ν.real (ReferenceCompleteOrdinaryFalseFixedIDBudget.ordinaryWrongCompletionPrefixEvent
        rate rewards C_star C_h p.T) :=
    measureReal_mono
      (stoppedOrdinaryWrongCompletionEvent_subset_prefix rate rewards C_star C_h)
      (by finiteness)
  have hprefix :=
    ReferenceCompleteOrdinaryFalseFixedIDBudget.ordinaryWrongCompletionPrefix_fixedID_measureReal_le
      rate rewards C_star C_h control0 ids p.T
  exact hmono.trans hprefix

/-- The actual stopped fixed-awaited ambiguity is charged to the literal
whole-horizon DOWN cohort and UP awaited-ambiguity envelope on this same ID. -/
theorem stoppedFixedAwaitedAmbiguityEvent_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) :
    (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
        (ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
          rate rewards C_star C_h) ≤
      1 / (2 * (N p : ℝ) ^ 2) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
  let downCohort := ReferenceGeneratedDownCohortFiniteUnion.downCohortUnionEvent
    rate rewards C_star C_h control0 (AffineBatchDecoder.quota p)
  let upEnvelope := ReferenceGeneratedUpAwaitedAmbiguityTail.upAwaitedAmbiguityEnvelope
    (rate := rate) rewards C_star C_h control0
  have hdown : ν.real downCohort ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
    have hcohort := downCohortUnionEvent_fixedID_measureReal_le
      rate rewards C_star C_h control0 ids
    simpa only [ν, downCohort] using hcohort
  have hup : ν.real upEnvelope ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
    have henv := upAwaitedAmbiguityEnvelope_fixedID_measureReal_le
      rate rewards C_star C_h control0 ids
    simpa only [ν, upEnvelope,
      ReferenceGeneratedUpFalseFixedIDTail.fixedIDSourceLaw] using henv
  have hmono : ν.real
        (ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
          rate rewards C_star C_h) ≤ ν.real (downCohort ∪ upEnvelope) :=
    measureReal_mono
      (stoppedFixedAwaitedAmbiguityEvent_subset_downCohort_upEnvelope
        rate rewards C_star C_h control0)
      (by finiteness)
  have hsum : 1 / (4 * (N p : ℝ) ^ 2) + 1 / (4 * (N p : ℝ) ^ 2) =
      1 / (2 * (N p : ℝ) ^ 2) := by
    have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
    field_simp [ne_of_gt hNpos]
    ring
  calc
    _ ≤ ν.real (downCohort ∪ upEnvelope) := hmono
    _ ≤ ν.real downCohort + ν.real upEnvelope := measureReal_union_le _ _
    _ ≤ 1 / (4 * (N p : ℝ) ^ 2) + 1 / (4 * (N p : ℝ) ^ 2) := add_le_add hdown hup
    _ = 1 / (2 * (N p : ℝ) ^ 2) := hsum

/-- The complete inclusive source decoder failure event has the sum of the
ordinary and fixed-awaited budgets at every fixed identification array. -/
theorem completeInclusiveDecoderFailureEvent_fixedID_measureReal_le
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (ids : IDArray p) :
    (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p)).real
        (ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent
          rate rewards C_star C_h) ≤
      1 / (N p : ℝ) ^ 2 := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (BootstrapPrivateRoundStreams.extendedPrivateLaw p))
  have hfalse := stoppedOrdinaryWrongCompletionEvent_fixedID_measureReal_le
    rate rewards C_star C_h control0 ids
  have hamb := stoppedFixedAwaitedAmbiguityEvent_fixedID_measureReal_le
    rate rewards C_star C_h control0 ids
  have hsum : 1 / (2 * (N p : ℝ) ^ 2) + 1 / (2 * (N p : ℝ) ^ 2) =
      1 / (N p : ℝ) ^ 2 := by
    have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
    field_simp [ne_of_gt hNpos]
    ring
  calc
    _ ≤ ν.real
        (ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
          rate rewards C_star C_h) +
        ν.real
          (ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedFixedAwaitedAmbiguityEvent
            rate rewards C_star C_h) := by
      simpa only [ν,
        ReferenceCompleteInclusivePhysicalDecoderErrors.completeInclusiveDecoderFailureEvent] using
        measureReal_union_le _ _
    _ ≤ 1 / (2 * (N p : ℝ) ^ 2) + 1 / (2 * (N p : ℝ) ^ 2) := by
      exact add_le_add hfalse hamb
    _ = 1 / (N p : ℝ) ^ 2 := hsum

end Bandits.Support.ReferenceCompleteInclusiveDecoderFixedIDBudget

end
