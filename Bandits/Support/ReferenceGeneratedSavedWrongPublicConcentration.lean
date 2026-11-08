/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability
public import Bandits.Support.ReferenceGeneratedJointDecoderFailureBound
public import Bandits.Support.CompleteRowConcentration

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Whole-row concentration for saved-wrong diagnostics

This component concentrates the existing saved-wrong suffix-prefix event on
the complete physical suffix. Its row means are the original-ID-conditioned
uniform whole-row averages. It does not identify this diagnostic with the
overflow-stopped event or with the combined exceptional event.

Sources: `sources/zip4/manuscript/08_main_theorem.tex:29-75`,
`sources/zip4/manuscript/07_public_setup.tex:123-164`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-157`, and
`sources/zip4/manuscript/06_interruptions.tex:355-362`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicGridConcentration
open Bandits.Support.WholeRowHoeffding
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open scoped ENNReal

namespace Bandits.Support.ReferenceGeneratedSavedWrongPublicConcentration

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters}

/-- The source multiplier on the saved-wrong row probability. -/
@[expose] def savedWrongErrorScale (p : Parameters) : ℝ :=
  2 * (p.m : ℝ) * (p.T : ℝ)

/-- The literal original-ID-conditioned uniform mean of the existing
whole-row saved-wrong private probability. -/
@[expose] noncomputable def savedWrongRowMean
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) : ℝ :=
  (1 / (M p : ℝ)) * ∑ j : Fin (M p),
    ∫ rho : CompleteRow p,
      _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
        rate rewards C_star C_h k ids j rho ∂completeRowMeasure p

/-- The accepted real-grid encoding equivalence supplies the generic row cost
used by complete-row concentration. -/
@[expose] def savedWrongScaledRowCost (p : Parameters)
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) :
    IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ :=
  fun ids rewards j rho => savedWrongErrorScale p *
    _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
      rate ((realRewardMatrixEncodingEquiv p).symm rewards) C_star C_h k ids j rho

/-- The explicit Borel event of complete public rows satisfying the accepted
all-grid concentration inequality, centered at the same-ID row mean. -/
@[expose] noncomputable def savedWrongRowGoodEvent
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) :
    Set (IDArray p × CompleteRows p) :=
  {z | ∀ r : RealRewardMatrix p,
    barG (fun j rows => savedWrongScaledRowCost p rate C_star C_h k
      z.1 r j (rows j)) z.2 ≤
      savedWrongErrorScale p * savedWrongRowMean rate
        ((realRewardMatrixEncodingEquiv p).symm r) C_star C_h k z.1 +
        2 * rowConcentrationScale p}

/-- The published-output event is the row event on the original public product. -/
@[expose] noncomputable def savedWrongPublishedGoodEvent
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) : Set (PublishedOutput p) :=
  {u | (u.1, u.2) ∈ savedWrongRowGoodEvent rate C_star C_h k}

/-- Every fixed-ID row section of the mean is integrable. -/
theorem integrable_fixedRowProbability_sections
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) :
    Integrable
      (fun rho : CompleteRow p =>
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate rewards C_star C_h k ids j rho)
      (completeRowMeasure p) :=
  _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.integrable_fixedRowPrivateProbability
    rate rewards C_star C_h k ids j

/-- The original full-row product integral of the row probability is exactly
its single-row integral. -/
theorem integral_fixedRowProbability_fullRows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) (j : Fin (M p)) :
    (∫ rows : CompleteRows p,
      _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
        rate rewards C_star C_h k ids j (rows j) ∂completeRowsMeasure p) =
      ∫ rho : CompleteRow p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate rewards C_star C_h k ids j rho ∂completeRowMeasure p :=
  _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.integral_fixedRowPrivateProbability_rows
    rate rewards C_star C_h k ids j

/-- The fixed-ID row mean is jointly Borel in the original IDs and all whole
rows used in its finite sum. -/
theorem measurable_savedWrongRowMean
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) :
    Measurable (savedWrongRowMean rate rewards C_star C_h k) := by
  classical
  have hrow (j : Fin (M p)) :
      Measurable (fun ids : IDArray p =>
        ∫ rho : CompleteRow p,
          _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
            rate rewards C_star C_h k ids j rho ∂completeRowMeasure p) := by
    have h := _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.measurable_fixedRowPrivateProbability
      rate rewards C_star C_h k j
    exact h.stronglyMeasurable.integral_prod_right'.measurable
  unfold savedWrongRowMean
  exact measurable_const.mul (Finset.measurable_sum Finset.univ fun j hj => hrow j)

/-- Pointwise [0,1] bounds for the original-ID-conditioned row mean. -/
theorem savedWrongRowMean_bounds
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) :
    savedWrongRowMean rate rewards C_star C_h k ids ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonneg (j : Fin (M p)) : 0 ≤
      ∫ rho : CompleteRow p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate rewards C_star C_h k ids j rho ∂completeRowMeasure p :=
    integral_nonneg fun rho =>
      (_root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability_bounds
        rate rewards C_star C_h k ids j rho).1
  have hle (j : Fin (M p)) :
      (∫ rho : CompleteRow p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate rewards C_star C_h k ids j rho ∂completeRowMeasure p) ≤ 1 := by
    have h := integral_mono
      (integrable_fixedRowProbability_sections rate rewards C_star C_h k ids j)
      (integrable_const (1 : ℝ))
      (fun rho =>
        (_root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability_bounds
          rate rewards C_star C_h k ids j rho).2)
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hsumlo : 0 ≤ ∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate rewards C_star C_h k ids j rho ∂completeRowMeasure p :=
    Finset.sum_nonneg fun j hj => hnonneg j
  have hsumhi : (∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate rewards C_star C_h k ids j rho ∂completeRowMeasure p) ≤ (M p : ℝ) := by
    calc
      _ ≤ ∑ _j : Fin (M p), (1 : ℝ) := Finset.sum_le_sum fun j hj => hle j
      _ = (M p : ℝ) := by simp
  have hM : 0 < (M p : ℝ) := Nat.cast_pos.mpr (M_pos p)
  constructor
  · unfold savedWrongRowMean
    exact mul_nonneg (by positivity) hsumlo
  · unfold savedWrongRowMean
    calc
      (1 / (M p : ℝ)) * _ ≤ (1 / (M p : ℝ)) * (M p : ℝ) :=
        mul_le_mul_of_nonneg_left hsumhi (by positivity)
      _ = 1 := by field_simp

/-- The literal mean is integrable under the original ID-array law. -/
theorem integrable_savedWrongRowMean
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) :
    Integrable (savedWrongRowMean rate rewards C_star C_h k) (idArrayMeasure p) := by
  apply Integrable.of_mem_Icc 0 1
    (measurable_savedWrongRowMean rate rewards C_star C_h k).aemeasurable
  exact ae_of_all _ fun ids => savedWrongRowMean_bounds rate rewards C_star C_h k ids

/-- The original private expectation at a fixed ID array equals the literal
uniform row mean, retaining the original private arrays and J partition. -/
theorem savedWrongRowMean_eq_originalPrivateRows
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) :
    savedWrongRowMean rate rewards C_star C_h k ids =
      ∫ rows : CompleteRows p, ∫ e : ExtendedPrivateCoordinates p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
          rate rewards C_star C_h k ((ids, rows), e)
          ∂extendedPrivateLaw p ∂completeRowsMeasure p := by
  simpa only [savedWrongRowMean] using
    (_root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.rowsPrivateIntegral_eq_uniform_rowMeans
      rate rewards C_star C_h k ids).symm

/-- The complete-row expectation used by the accepted concentration theorem is
exactly the source multiplier times the literal same-ID mean. -/
theorem savedWrongScaledRowCost_muG_eq_savedWrongRowMean
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p)
    (r : RealRewardMatrix p) :
    WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
        (CompleteRowConcentration.liftedCompleteRowCost p ids
          (savedWrongScaledRowCost p rate C_star C_h k) r) =
      savedWrongErrorScale p * savedWrongRowMean rate
        ((realRewardMatrixEncodingEquiv p).symm r) C_star C_h k ids := by
  unfold WholeRowHoeffding.muG
  change (∑ j : Fin (M p), ∫ rows : CompleteRows p,
      savedWrongErrorScale p *
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate ((realRewardMatrixEncodingEquiv p).symm r) C_star C_h k ids j (rows j)
          ∂completeRowsMeasure p) / (M p : ℝ) = _
  simp_rw [integral_const_mul]
  rw [← Finset.mul_sum]
  simp_rw [_root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.integral_fixedRowPrivateProbability_rows]
  rw [savedWrongRowMean]
  ring

/-- The saved-wrong row mean averaged over the original ID-array law is at
most the original-source event probability budget. -/
theorem savedWrongRowMean_idArray_integral_bound
    (rate : RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p) (k : ℕ) :
    (∫ ids : IDArray p, savedWrongRowMean rate rewards C_star C_h k ids
      ∂idArrayMeasure p) ≤ 1 / (2 * (N p : ℝ) ^ 2) := by
  let event := ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
    rate rewards C_star C_h k
  have hevent : MeasurableSet event :=
    ReferenceGeneratedJointDecoderFailureBound.measurableSet_savedWrongSuffixPrefixEvent
      rate rewards C_star C_h k
  have hsource :
      (∫ source : BootstrapPrivateRoundStreams.SourceInput p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
          rate rewards C_star C_h k source ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
        (BootstrapPrivateRoundStreams.sourceInputLaw p).real event := by
    simp only [_root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator,
      event]
    exact integral_indicator_one hevent
  have hidentity := _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.sourceIntegral_eq_idIntegrated_uniform_rowMeans
    rate rewards C_star C_h k
  have hid :
      (∫ source : BootstrapPrivateRoundStreams.SourceInput p,
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
          rate rewards C_star C_h k source ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
        ∫ ids : IDArray p, savedWrongRowMean rate rewards C_star C_h k ids
          ∂idArrayMeasure p := by
    simpa only [savedWrongRowMean] using hidentity
  calc
    _ = (BootstrapPrivateRoundStreams.sourceInputLaw p).real event := hid.symm.trans hsource
    _ ≤ 1 / (2 * (N p : ℝ) ^ 2) :=
      ReferenceGeneratedJointDecoderFailureBound.savedWrongSuffixPrefixEvent_measureReal_bound
        rate rewards C_star C_h control0 k

/-- The actual scaled cost obeys the required complete-row interval at every
whole row. -/
theorem savedWrongScaledRowCost_bounds
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ)
    (ids : IDArray p) (r : RealRewardMatrix p) (j : Fin (M p)) (rho : CompleteRow p) :
    savedWrongScaledRowCost p rate C_star C_h k ids r j rho ∈
      Set.Icc (-(p.m : ℝ) * (p.T : ℝ)) (3 * (p.m : ℝ) * (p.T : ℝ)) := by
  have hp := _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability_bounds
    rate ((realRewardMatrixEncodingEquiv p).symm r)
      C_star C_h k ids j rho
  have hs : 0 ≤ savedWrongErrorScale p := by
    dsimp [savedWrongErrorScale]
    positivity
  have hmT : 0 ≤ (p.m : ℝ) * (p.T : ℝ) := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  constructor
  · have : 0 ≤ savedWrongErrorScale p *
        _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
          rate ((realRewardMatrixEncodingEquiv p).symm r) C_star C_h k ids j rho :=
      mul_nonneg hs hp.1
    dsimp [savedWrongScaledRowCost]
    have hneg : -(p.m : ℝ) * (p.T : ℝ) = -((p.m : ℝ) * (p.T : ℝ)) := by ring
    rw [hneg]
    exact (neg_nonpos.mpr hmT).trans this
  · have hle := mul_le_mul_of_nonneg_left hp.2 hs
    dsimp [savedWrongScaledRowCost] at hle ⊢
    dsimp [savedWrongErrorScale] at hle ⊢
    nlinarith [hmT]

/-- The row event is exactly the accepted complete-row concentration event on
each fixed-ID section. -/
theorem savedWrongRowGoodEvent_section_iff
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ)
    (ids : IDArray p) (rows : CompleteRows p) :
    (ids, rows) ∈ savedWrongRowGoodEvent rate C_star C_h k ↔
      rows ∈ CompleteRowConcentration.completeRowConcentrationGoodEvent p ids
        (savedWrongScaledRowCost p rate C_star C_h k) := by
  simp only [savedWrongRowGoodEvent, Set.mem_ofPred_eq,
    CompleteRowConcentration.completeRowConcentrationGoodEvent,
    PublicGridConcentration.rowConcentrationGoodEvent]
  constructor
  · intro h r
    have hm := savedWrongScaledRowCost_muG_eq_savedWrongRowMean
      rate C_star C_h k ids r
    have hr := h r
    rw [hm]
    exact hr
  · intro h r
    have hm := savedWrongScaledRowCost_muG_eq_savedWrongRowMean
      rate C_star C_h k ids r
    have hr := h r
    rw [hm] at hr
    exact hr

/-- Every fixed-ID complete-row section has the concentration failure bound. -/
theorem savedWrongRowGoodEvent_section_failure_prob
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) :
    (completeRowsMeasure p).real
      {rows : CompleteRows p | (ids, rows) ∉ savedWrongRowGoodEvent rate C_star C_h k} ≤
        1 / (2 * (N p : ℝ)) := by
  have hmeas : ∀ r j, Measurable
      (savedWrongScaledRowCost p rate C_star C_h k ids r j) := by
    intro r j
    have h := _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.measurable_fixedRowPrivateProbability
      rate ((realRewardMatrixEncodingEquiv p).symm r)
      C_star C_h k j
    exact measurable_const.mul
      (h.comp (measurable_const.prodMk measurable_id))
  have hb : ∀ r j, ∀ᵐ rho ∂completeRowMeasure p,
      savedWrongScaledRowCost p rate C_star C_h k ids r j rho ∈
        Set.Icc (-(p.m : ℝ) * (p.T : ℝ)) (3 * (p.m : ℝ) * (p.T : ℝ)) := by
    intro r j
    exact ae_of_all _ fun rho => savedWrongScaledRowCost_bounds rate C_star C_h k ids r j rho
  have hfailure := CompleteRowConcentration.completeRowConcentrationGoodEvent_failure_prob_le_completeRowsMeasure
    p ids (savedWrongScaledRowCost p rate C_star C_h k) hmeas hb
  have heq : {rows : CompleteRows p | (ids, rows) ∉
      savedWrongRowGoodEvent rate C_star C_h k} =
      (CompleteRowConcentration.completeRowConcentrationGoodEvent p ids
        (savedWrongScaledRowCost p rate C_star C_h k))ᶜ := by
    ext rows
    exact not_congr (savedWrongRowGoodEvent_section_iff
      rate C_star C_h k ids rows)
  rw [heq]
  exact hfailure

/-- Borelness of the explicit joint ID/complete-row event. -/
theorem measurableSet_savedWrongRowGoodEvent
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) :
    MeasurableSet (savedWrongRowGoodEvent rate C_star C_h k) := by
  classical
  have hcost (r : RealRewardMatrix p) (j : Fin (M p)) :
      Measurable (fun z : IDArray p × CompleteRows p =>
        savedWrongScaledRowCost p rate C_star C_h k z.1 r j (z.2 j)) := by
    have h := _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.measurable_fixedRowPrivateProbability
      rate ((realRewardMatrixEncodingEquiv p).symm r)
        C_star C_h k j
    have hpair : Measurable (fun z : IDArray p × CompleteRows p => (z.1, z.2 j)) :=
      measurable_fst.prodMk ((measurable_completeRowProjection p j).comp measurable_snd)
    exact measurable_const.mul (h.comp hpair)
  have hbar (r : RealRewardMatrix p) :
      Measurable (fun z : IDArray p × CompleteRows p =>
        barG (fun j rows => savedWrongScaledRowCost p rate C_star C_h k
          z.1 r j (rows j)) z.2) := by
    unfold WholeRowHoeffding.barG
    fun_prop
  have hmean (r : RealRewardMatrix p) :
      Measurable (fun z : IDArray p × CompleteRows p =>
        savedWrongErrorScale p *
          savedWrongRowMean rate ((realRewardMatrixEncodingEquiv p).symm r)
            C_star C_h k z.1 + 2 * rowConcentrationScale p) := by
    exact (measurable_const.mul
      ((measurable_savedWrongRowMean rate ((realRewardMatrixEncodingEquiv p).symm r)
        C_star C_h k).comp measurable_fst)).add_const _
  rw [show savedWrongRowGoodEvent rate C_star C_h k =
    {z | ∀ r : RealRewardMatrix p,
      barG (fun j rows => savedWrongScaledRowCost p rate C_star C_h k
        z.1 r j (rows j)) z.2 ≤
        savedWrongErrorScale p * savedWrongRowMean rate
          ((realRewardMatrixEncodingEquiv p).symm r) C_star C_h k z.1 +
          2 * rowConcentrationScale p} by
      ext z
      rfl]
  rw [Set.ofPred_forall]
  exact MeasurableSet.iInter fun r => measurableSet_le (hbar r) (hmean r)

/-- The Borel row event transfers without changing the original ID/row product. -/
theorem measurableSet_savedWrongPublishedGoodEvent
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) :
    MeasurableSet (savedWrongPublishedGoodEvent rate C_star C_h k) := by
  change MeasurableSet
    ((fun u : PublishedOutput p => (u.1, u.2)) ⁻¹'
      savedWrongRowGoodEvent rate C_star C_h k)
  exact (measurableSet_savedWrongRowGoodEvent rate C_star C_h k).preimage
    (measurable_fst.prodMk measurable_snd)

/-- The unconditional bad probability under the original published-output
product law has the same bound as every fixed-ID row section. -/
theorem savedWrongPublishedGoodEvent_failure_prob
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) :
    (publishedOutputMeasure p).real
      (savedWrongPublishedGoodEvent rate C_star C_h k)ᶜ ≤
        1 / (2 * (N p : ℝ)) := by
  let bad := (savedWrongPublishedGoodEvent rate C_star C_h k)ᶜ
  let fiber (ids : IDArray p) : CompleteRows p → ℝ :=
    fun rows => (bad.indicator (fun _ : PublishedOutput p => (1 : ℝ))) (ids, rows)
  have hbad : MeasurableSet bad :=
    (measurableSet_savedWrongPublishedGoodEvent rate C_star C_h k).compl
  have hfiber (ids : IDArray p) : MeasurableSet {rows : CompleteRows p | (ids, rows) ∈ bad} :=
    hbad.preimage (measurable_const.prodMk measurable_id)
  have hind : Measurable (bad.indicator (fun _ : PublishedOutput p => (1 : ℝ))) :=
    measurable_const.indicator hbad
  have hfun : Integrable (bad.indicator (fun _ : PublishedOutput p => (1 : ℝ)))
      ((idArrayMeasure p).prod (completeRowsMeasure p)) := by
    apply Integrable.of_mem_Icc 0 1 hind.aemeasurable
    exact ae_of_all _ fun u => by
      by_cases hu : u ∈ bad <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hu]
  have hsec_meas : Measurable (fun ids : IDArray p => ∫ rows : CompleteRows p,
      fiber ids rows ∂completeRowsMeasure p) := by
    have hs := hind.stronglyMeasurable.integral_prod_right'
      (ν := completeRowsMeasure p)
    simpa only [fiber] using hs.measurable
  have hsec_nonneg (ids : IDArray p) : 0 ≤
      ∫ rows : CompleteRows p, fiber ids rows ∂completeRowsMeasure p := by
    apply integral_nonneg
    intro rows
    change 0 ≤ bad.indicator (fun _ : PublishedOutput p => (1 : ℝ)) (ids, rows)
    by_cases h : (ids, rows) ∈ bad
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have hsec_upper (ids : IDArray p) :
      (∫ rows : CompleteRows p, fiber ids rows ∂completeRowsMeasure p) ≤
        1 / (2 * (N p : ℝ)) := by
    have h := savedWrongRowGoodEvent_section_failure_prob rate C_star C_h k ids
    have hset : {rows : CompleteRows p | (ids, rows) ∈ bad} =
        {rows : CompleteRows p | (ids, rows) ∉ savedWrongRowGoodEvent rate C_star C_h k} := by
      ext rows
      simp [bad, savedWrongPublishedGoodEvent, savedWrongRowGoodEvent]
    calc
      _ = (completeRowsMeasure p).real {rows : CompleteRows p | (ids, rows) ∈ bad} := by
        change (∫ rows : CompleteRows p,
          ({rows | (ids, rows) ∈ bad}.indicator (fun _ => (1 : ℝ))) rows
            ∂completeRowsMeasure p) = _
        exact integral_indicator_one (hfiber ids)
      _ ≤ 1 / (2 * (N p : ℝ)) := by
        rw [hset]
        exact h
  have hsec_int : Integrable (fun ids : IDArray p =>
      ∫ rows : CompleteRows p, fiber ids rows ∂completeRowsMeasure p) (idArrayMeasure p) := by
    apply Integrable.of_mem_Icc 0 (1 / (2 * (N p : ℝ))) hsec_meas.aemeasurable
    exact ae_of_all _ fun ids => ⟨hsec_nonneg ids, hsec_upper ids⟩
  have hprod := integral_prod
    (bad.indicator (fun _ : PublishedOutput p => (1 : ℝ))) hfun
  have houter :
      (∫ u : PublishedOutput p,
        bad.indicator (fun _ => (1 : ℝ)) u ∂publishedOutputMeasure p) =
        ∫ ids : IDArray p, ∫ rows : CompleteRows p, fiber ids rows
          ∂completeRowsMeasure p ∂idArrayMeasure p := by
    simpa only [publishedOutputMeasure, bad, fiber] using hprod
  have hbound : (∫ ids : IDArray p,
      ∫ rows : CompleteRows p, fiber ids rows ∂completeRowsMeasure p ∂idArrayMeasure p) ≤
      1 / (2 * (N p : ℝ)) := by
    calc
      _ ≤ ∫ _ids : IDArray p, (1 / (2 * (N p : ℝ))) ∂idArrayMeasure p :=
        integral_mono hsec_int (integrable_const _) hsec_upper
      _ = 1 / (2 * (N p : ℝ)) := by simp [integral_const, probReal_univ]
  calc
    _ = (publishedOutputMeasure p).real bad := rfl
    _ = ∫ u : PublishedOutput p,
        bad.indicator (fun _ => (1 : ℝ)) u ∂publishedOutputMeasure p :=
      (integral_indicator_one hbad).symm
    _ = ∫ ids : IDArray p, ∫ rows : CompleteRows p, fiber ids rows
        ∂completeRowsMeasure p ∂idArrayMeasure p := houter
    _ ≤ 1 / (2 * (N p : ℝ)) := hbound

/-- The explicit Borel event admits the fixed-ID concentration theorem on
the original full continuous row product. -/
theorem savedWrongScaledRowCost_fixedID_concentration
    (rate : RateInput p) (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) :
    (completeRowsMeasure p).real
      {rows | (ids, rows) ∉ savedWrongRowGoodEvent rate C_star C_h k} ≤
        1 / (2 * (N p : ℝ)) :=
  savedWrongRowGoodEvent_section_failure_prob rate C_star C_h k ids

/-- On every fixed public output in the event, all grid rewards obey the
private-expectation inequality with the same original-ID row mean. -/
theorem savedWrongPublishedGoodEvent_privateIntegral_bound
    (rate : RateInput p)
    (C_star C_h : ℝ) (k : ℕ) (u : PublishedOutput p)
    (hu : u ∈ savedWrongPublishedGoodEvent rate C_star C_h k)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    savedWrongErrorScale p *
        (∫ e : ExtendedPrivateCoordinates p,
          _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
            rate rewards C_star C_h k ((u.1, u.2), e)
          ∂extendedPrivateLaw p) ≤
      savedWrongErrorScale p * savedWrongRowMean rate rewards C_star C_h k u.1 +
        2 * rowConcentrationScale p := by
  have hrow : u.2 ∈ CompleteRowConcentration.completeRowConcentrationGoodEvent p u.1
      (savedWrongScaledRowCost p rate C_star C_h k) :=
    (savedWrongRowGoodEvent_section_iff rate C_star C_h k u.1 u.2).mp hu
  let r := realRewardMatrixEncodingEquiv p rewards
  have hconc := CompleteRowConcentration.completeRowConcentrationGoodEvent_bound_at
    p u.1 (savedWrongScaledRowCost p rate C_star C_h k) u.2 hrow r
  rw [savedWrongScaledRowCost_muG_eq_savedWrongRowMean] at hconc
  have hbar :
      barG (fun j rows => savedWrongScaledRowCost p rate C_star C_h k
        u.1 r j (rows j)) u.2 =
        savedWrongErrorScale p * ((1 / (M p : ℝ)) * ∑ j : Fin (M p),
          _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.fixedRowPrivateProbability
            rate rewards C_star C_h k u.1 j (u.2 j)) := by
    unfold WholeRowHoeffding.barG savedWrongScaledRowCost
    simp only [r, Equiv.symm_apply_apply]
    rw [← Finset.mul_sum]
    ring_nf
  have hprivate :=
    _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.privateIntegral_eq_uniform_fixedRows
      rate rewards C_star C_h k u
  have hbarPrivate :
      barG (fun j rows => savedWrongScaledRowCost p rate C_star C_h k
        u.1 r j (rows j)) u.2 =
        savedWrongErrorScale p *
          (∫ e : ExtendedPrivateCoordinates p,
            _root_.Bandits.Support.ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
              rate rewards C_star C_h k ((u.1, u.2), e)
            ∂extendedPrivateLaw p) := by
    rw [hbar, ← hprivate]
  have hcenter : savedWrongRowMean rate
      ((realRewardMatrixEncodingEquiv p).symm r) C_star C_h k u.1 =
        savedWrongRowMean rate rewards C_star C_h k u.1 := by
    simp only [r, Equiv.symm_apply_apply]
  rw [hcenter] at hconc
  calc
    _ = barG (fun j rows => savedWrongScaledRowCost p rate C_star C_h k
          u.1 r j (rows j)) u.2 := hbarPrivate.symm
    _ ≤ savedWrongErrorScale p * savedWrongRowMean rate rewards C_star C_h k u.1 +
          2 * rowConcentrationScale p := hconc

end Bandits.Support.ReferenceGeneratedSavedWrongPublicConcentration

end
