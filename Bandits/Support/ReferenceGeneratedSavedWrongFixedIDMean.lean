/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedSavedWrongPublicConcentration
public import Bandits.Support.ReferenceGeneratedAllWrongDownFixedIDTail
public import Bandits.Support.ReferenceGeneratedUpFalseFixedIDTail

/-!
# Fixed-ID mean bound for the generated saved-wrong diagnostic

The original-ID-conditioned whole-row mean is bounded by the two accepted
fixed-ID decoder budgets under the same original product law. On the existing
published good event, its private integral therefore has the corresponding
scaled center. This component does not assert stopped-event coverage or main
regret closure.

Sources: `sources/zip4/manuscript/08_main_theorem.tex:29-75`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:139-157`, and
`sources/zip4/manuscript/07_public_setup.tex:123-164`.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PublicGridConcentration

namespace Bandits.Support.ReferenceGeneratedSavedWrongFixedIDMean

variable {p : ConstructorDimensions.Parameters}

/-- Dirac insertion into the original complete-row and private product turns
the literal saved-wrong indicator expectation into the existing same-ID
whole-row mean, without changing the private coordinate law. -/
theorem savedWrongRowMean_eq_fixedID_sourceEvent_measure
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (k : ℕ) (ids : IDArray p) :
    ReferenceGeneratedSavedWrongPublicConcentration.savedWrongRowMean
        rate rewards C_star C_h k ids =
      (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
        (extendedPrivateLaw p)).real
        (ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
          rate rewards C_star C_h k) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (extendedPrivateLaw p))
  let E := ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
    rate rewards C_star C_h k
  let f : SourceInput p → ℝ :=
    ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
      rate rewards C_star C_h k
  have hE : MeasurableSet E :=
    ReferenceGeneratedJointDecoderFailureBound.measurableSet_savedWrongSuffixPrefixEvent
      rate rewards C_star C_h k
  have hfmeas : Measurable f :=
    ReferenceGeneratedSavedWrongSelectedRowProbability.measurable_savedWrongIndicator
      rate rewards C_star C_h k
  have hfint : Integrable f ν := by
    apply Integrable.of_mem_Icc 0 1 hfmeas.aemeasurable
    exact ae_of_all _ fun source =>
      ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator_bounds
        rate rewards C_star C_h k source
  have hinner : Integrable
      (fun published : PublishedOutput p =>
        ∫ e : ExtendedPrivateCoordinates p, f (published, e) ∂extendedPrivateLaw p)
      ((Measure.dirac ids).prod (completeRowsMeasure p)) :=
    hfint.integral_prod_left
  have hiterated :
      (∫ source : SourceInput p, f source ∂ν) =
        ∫ rows : CompleteRows p,
          ∫ e : ExtendedPrivateCoordinates p, f ((ids, rows), e)
            ∂extendedPrivateLaw p ∂completeRowsMeasure p := by
    calc
      _ = ∫ published : PublishedOutput p,
            ∫ e : ExtendedPrivateCoordinates p, f (published, e)
              ∂extendedPrivateLaw p
            ∂((Measure.dirac ids).prod (completeRowsMeasure p)) :=
        integral_prod _ hfint
      _ = ∫ id' : IDArray p, ∫ rows : CompleteRows p,
            ∫ e : ExtendedPrivateCoordinates p, f ((id', rows), e)
              ∂extendedPrivateLaw p ∂completeRowsMeasure p
            ∂Measure.dirac ids := integral_prod _ hinner
      _ = ∫ rows : CompleteRows p,
            ∫ e : ExtendedPrivateCoordinates p, f ((ids, rows), e)
              ∂extendedPrivateLaw p ∂completeRowsMeasure p := by
        simp only [integral_dirac]
  have hmeanrows :=
    ReferenceGeneratedSavedWrongPublicConcentration.savedWrongRowMean_eq_originalPrivateRows
      rate rewards C_star C_h k ids
  have hmass : (∫ source : SourceInput p, f source ∂ν) = ν.real E := by
    have hindicator : f = fun source => E.indicator (fun _ => (1 : ℝ)) source := by
      funext source
      rfl
    rw [hindicator]
    exact integral_indicator_one hE
  calc
    _ = ∫ rows : CompleteRows p,
          ∫ e : ExtendedPrivateCoordinates p,
            ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
              rate rewards C_star C_h k ((ids, rows), e)
            ∂extendedPrivateLaw p ∂completeRowsMeasure p := hmeanrows
    _ = ∫ source : SourceInput p, f source ∂ν := hiterated.symm
    _ = ν.real E := hmass

/-- For every ID array, the literal saved-wrong event under the original
Dirac-inserted law is bounded by the sum of the accepted DOWN and UP
fixed-ID budgets. -/
theorem savedWrongRowMean_fixedID_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
    (k : ℕ) (ids : IDArray p) :
    ReferenceGeneratedSavedWrongPublicConcentration.savedWrongRowMean
        rate rewards C_star C_h k ids ≤ 1 / (2 * (N p : ℝ) ^ 2) := by
  let ν := (((Measure.dirac ids).prod (completeRowsMeasure p)).prod
    (extendedPrivateLaw p))
  let savedEvent := ReferenceGeneratedSavedWrongEvent.savedWrongSuffixPrefixEvent
    rate rewards C_star C_h k
  let downEvent :=
    ReferenceGeneratedAllWrongDownEvent.generatedAllWrongDownSourceEvent
      rate rewards C_star C_h
  let upEvent :=
    ReferenceGeneratedUpFalseTail.generatedUpWrongSuffixPrefixEvent
      (r := rate) rewards C_star C_h k
  have hsubset : savedEvent ⊆ downEvent ∪ upEvent := by
    simpa only [savedEvent, downEvent, upEvent] using
      ReferenceGeneratedJointDecoderFailureBound.savedWrongSuffixPrefixEvent_subset_jointDecoderEvents
        rate rewards C_star C_h k
  have hdown : ν.real downEvent ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
    simpa only [ν, downEvent] using
      ReferenceGeneratedAllWrongDownFixedIDTail.generatedAllWrongDownSourceEvent_fixedID_measureReal_quota_bound
        rate rewards C_star C_h control0 ids
  have hup : ν.real upEvent ≤ 1 / (4 * (N p : ℝ) ^ 2) := by
    simpa only [ν, upEvent] using
      ReferenceGeneratedUpFalseFixedIDTail.generatedUpWrongSuffixPrefixEvent_fixedID_measureReal_le
        rate rewards C_star C_h control0 k ids
  have hNpos : 0 < (N p : ℝ) := Nat.cast_pos.mpr (N_pos p)
  have hsum :
      1 / (4 * (N p : ℝ) ^ 2) + 1 / (4 * (N p : ℝ) ^ 2) =
        1 / (2 * (N p : ℝ) ^ 2) := by
    have hNne : (N p : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp [hNne]
    ring
  calc
    _ = ν.real savedEvent := by
      simpa only [ν, savedEvent] using
        savedWrongRowMean_eq_fixedID_sourceEvent_measure
          rate rewards C_star C_h k ids
    _ ≤ ν.real (downEvent ∪ upEvent) :=
      measureReal_mono hsubset (by finiteness)
    _ ≤ ν.real downEvent + ν.real upEvent := measureReal_union_le _ _
    _ ≤ 1 / (4 * (N p : ℝ) ^ 2) + 1 / (4 * (N p : ℝ) ^ 2) :=
      add_le_add hdown hup
    _ = 1 / (2 * (N p : ℝ) ^ 2) := hsum

/-- On the existing published good event, every whole reward table obeys
the original private-expectation bound with the same-ID mean replaced by its
fixed-ID budget. -/
theorem savedWrongPublishedGoodEvent_privateIntegral_fixedID_bound
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (C_star C_h : ℝ) (k : ℕ)
    (control0 : ContinuousLearningRows.TimeControl p)
    (u : PublishedOutput p)
    (hu : u ∈ ReferenceGeneratedSavedWrongPublicConcentration.savedWrongPublishedGoodEvent
      rate C_star C_h k)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale p *
        (∫ e : ExtendedPrivateCoordinates p,
          ReferenceGeneratedSavedWrongSelectedRowProbability.savedWrongIndicator
            rate rewards C_star C_h k ((u.1, u.2), e)
          ∂extendedPrivateLaw p) ≤
      ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale p /
          (2 * (N p : ℝ) ^ 2) +
        2 * rowConcentrationScale p := by
  have hpublic :=
    ReferenceGeneratedSavedWrongPublicConcentration.savedWrongPublishedGoodEvent_privateIntegral_bound
      rate C_star C_h k u hu rewards
  have hmean := savedWrongRowMean_fixedID_bound
    rate rewards C_star C_h control0 k u.1
  have hscale :
      0 ≤ ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale p := by
    unfold ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale
    positivity
  calc
    _ ≤ ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale p *
          ReferenceGeneratedSavedWrongPublicConcentration.savedWrongRowMean
            rate rewards C_star C_h k u.1 +
        2 * rowConcentrationScale p :=
      hpublic
    _ ≤ ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale p *
          (1 / (2 * (N p : ℝ) ^ 2)) +
        2 * rowConcentrationScale p :=
      add_le_add (mul_le_mul_of_nonneg_left hmean hscale) (le_refl _)
    _ = ReferenceGeneratedSavedWrongPublicConcentration.savedWrongErrorScale p /
          (2 * (N p : ℝ) ^ 2) +
        2 * rowConcentrationScale p := by
      ring

end Bandits.Support.ReferenceGeneratedSavedWrongFixedIDMean

end
