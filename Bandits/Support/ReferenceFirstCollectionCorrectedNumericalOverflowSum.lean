/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCorrectedOriginalSourceOverflow
public import Bandits.Support.ReferenceFirstCollectionCorrectedBirthEnergySum
public import Mathlib.MeasureTheory.Measure.Real

import Mathlib.Tactic

/-!
# Corrected first-collection overflow sums on the original source

This module sums the existing corrected-slice overflow events under the
unchanged original source law. It uses the inherited post-call birth energy
and the disjoint original first-call partition. These numerical bounds do not
construct the physical queue joins used by their later consumer.

Sources: ZIP4 `04_slow_fast_learner.tex:157-187,256-290`,
`06_interruptions.tex:355-361,391-408,425-426`, and
`appendix_a_local_protocol.tex:28-64` under `sources/zip4/manuscript/`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Bandits.Support ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceFirstCollectionCorrectedSliceNumericalPrefix (correctedCell overflowEvent)
open scoped BigOperators

namespace Bandits.Support.ReferenceFirstCollectionCorrectedNumericalOverflowSum

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

local notation "X" => SourceInput p
local notation "mu" => sourceInputLaw p

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The literal union of the existing corrected-slice overflow events over
all arms and all cutoff/date cells, on the original source input. -/
def allArmOverflowEvent : Set X :=
  ⋃ a : Fin p.K, ⋃ u : Fin p.T, ⋃ t : Fin p.T,
    overflowEvent rate rewards C_star C_h u t a

/-- Corrected cells are contained in the original first-call partition, so
their unnormalized masses sum to at most one under the original source law. -/
theorem correctedCell_measure_sum_le_one :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      (mu).real (correctedCell rate rewards C_star C_h u t)) ≤ 1 := by
  let first : Fin p.T × Fin p.T → Set X := fun z => firstCell
    rate rewards C_star C_h z.1 z.2
  have hfirst_measurable : ∀ z : Fin p.T × Fin p.T, MeasurableSet (first z) := by
    intro z
    simpa only [first, firstCell] using
      ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
        rate rewards C_star C_h z.1 z.2
  have hfirst_disjoint :
      Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin p.T × Fin p.T))) first := by
    intro z hz w hw hne
    apply ReferenceFirstCollectionSamplerOutputLaw.firstCell_disjoint_of_ne
    intro heq
    exact hne heq
  have hfirst_sum :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (mu).real (firstCell rate rewards C_star C_h u t)) ≤ (mu).real Set.univ := by
    have hsum := MeasureTheory.sum_measureReal_le_measureReal_univ
      (μ := mu) (s := Finset.univ) (t := first)
      (by
        intro z hz
        exact hfirst_measurable z)
      hfirst_disjoint
    simpa only [first, Fintype.sum_prod_type] using hsum
  have hcell_le_first (u t : Fin p.T) :
      (mu).real (correctedCell rate rewards C_star C_h u t) ≤
        (mu).real (firstCell rate rewards C_star C_h u t) := by
    exact MeasureTheory.measureReal_mono (μ := mu)
      (fun x hx => hx.1) (by finiteness)
  have huniv : (mu).real Set.univ = 1 := by
    simp [Measure.real]
  calc
    (∑ u : Fin p.T, ∑ t : Fin p.T,
        (mu).real (correctedCell rate rewards C_star C_h u t)) ≤
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        (mu).real (firstCell rate rewards C_star C_h u t) := by
          apply Finset.sum_le_sum
          intro u hu
          apply Finset.sum_le_sum
          intro t ht
          exact hcell_le_first u t
    _ ≤ (mu).real Set.univ := hfirst_sum
    _ = 1 := huniv

/-- For one arm, the original-source sum of corrected-slice overflow
probabilities is bounded by the inherited birth-energy budget and the unique
first-call cell mass. -/
theorem armOverflowEvent_measure_sum_le (control0 : TimeControl p)
    (a : Fin p.K) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      (mu (overflowEvent rate rewards C_star C_h u t a)).toReal) ≤
      2 * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  let decay : ℝ := Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
    (32 * rate.eta.val))
  have hbirth :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ x, ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy
          rate rewards C_star C_h u t a x ∂mu) ≤ (p.T : ℝ) + 2 := by
    simpa only [ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy] using
      ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy_integral_sum_le_T_add_two
        rate rewards C_star C_h control0 a
  have hcell := correctedCell_measure_sum_le_one rate rewards C_star C_h
  have hinside :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ x, ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy
          rate rewards C_star C_h u t a x ∂mu) +
        (p.T : ℝ) *
          (∑ u : Fin p.T, ∑ t : Fin p.T,
            (mu).real (correctedCell rate rewards C_star C_h u t)) ≤
        2 * ((p.T : ℝ) + 1) := by
    have hTmass :
        (p.T : ℝ) *
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              (mu).real (correctedCell rate rewards C_star C_h u t)) ≤ (p.T : ℝ) := by
      calc
        _ ≤ (p.T : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hcell (Nat.cast_nonneg p.T)
        _ = (p.T : ℝ) := by ring
    calc
      _ ≤ ((p.T : ℝ) + 2) + (p.T : ℝ) := add_le_add hbirth hTmass
      _ = 2 * ((p.T : ℝ) + 1) := by ring
  calc
    (∑ u : Fin p.T, ∑ t : Fin p.T,
        (mu (overflowEvent rate rewards C_star C_h u t a)).toReal) ≤
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        decay *
          ((∫ x, ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy
              rate rewards C_star C_h u t a x ∂mu) +
            (p.T : ℝ) *
              (mu).real (correctedCell rate rewards C_star C_h u t)) := by
          apply Finset.sum_le_sum
          intro u hu
          apply Finset.sum_le_sum
          intro t ht
          simpa only [decay,
            ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy,
            Measure.real] using
            ReferenceFirstCollectionCorrectedOriginalSourceOverflow.overflowEvent_measure_le
              rate rewards C_star C_h control0 u t a
    _ = decay *
        ((∑ u : Fin p.T, ∑ t : Fin p.T,
            ∫ x, ReferenceFirstCollectionCorrectedBirthEnergySum.birthEnergy
              rate rewards C_star C_h u t a x ∂mu) +
          (p.T : ℝ) *
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              (mu).real (correctedCell rate rewards C_star C_h u t))) := by
            simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ decay * (2 * ((p.T : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hinside (Real.exp_nonneg _)
    _ = 2 * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
            simp only [decay]
            ring

/-- Summing the per-arm bounds charges the same corrected-slice event family
and the same original-source law once for each arm. -/
theorem allArmOverflowEvent_measure_sum_le (control0 : TimeControl p) :
    (∑ a : Fin p.K, ∑ u : Fin p.T, ∑ t : Fin p.T,
      (mu (overflowEvent rate rewards C_star C_h u t a)).toReal) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  let decay : ℝ := Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
    (32 * rate.eta.val))
  calc
    (∑ a : Fin p.K, ∑ u : Fin p.T, ∑ t : Fin p.T,
        (mu (overflowEvent rate rewards C_star C_h u t a)).toReal) ≤
      ∑ a : Fin p.K, 2 * ((p.T : ℝ) + 1) * decay := by
          apply Finset.sum_le_sum
          intro a ha
          simpa only [decay] using
            armOverflowEvent_measure_sum_le rate rewards C_star C_h control0 a
    _ = 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
            simp only [decay, Finset.sum_const, Finset.card_univ,
              Fintype.card_fin, nsmul_eq_mul]
            ring

/-- The literal union of all existing corrected-slice arm overflow events
has the finite-union bound under the unchanged original source law. -/
theorem allArmOverflowEvent_measure_le (control0 : TimeControl p) :
    (mu).real (allArmOverflowEvent rate rewards C_star C_h) ≤
      2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
        Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
          (32 * rate.eta.val)) := by
  calc
    (mu).real (allArmOverflowEvent rate rewards C_star C_h) ≤
        ∑ a : Fin p.K, (mu).real (⋃ u : Fin p.T, ⋃ t : Fin p.T,
          overflowEvent rate rewards C_star C_h u t a) := by
            simpa only [allArmOverflowEvent] using
              (MeasureTheory.measureReal_iUnion_fintype_le (μ := mu)
                (f := fun a : Fin p.K =>
                  ⋃ u : Fin p.T, ⋃ t : Fin p.T,
                    overflowEvent rate rewards C_star C_h u t a))
    _ ≤ ∑ a : Fin p.K, ∑ u : Fin p.T, (mu).real (⋃ t : Fin p.T,
          overflowEvent rate rewards C_star C_h u t a) := by
            apply Finset.sum_le_sum
            intro a ha
            exact MeasureTheory.measureReal_iUnion_fintype_le (μ := mu)
              (f := fun u : Fin p.T =>
                ⋃ t : Fin p.T, overflowEvent rate rewards C_star C_h u t a)
    _ ≤ ∑ a : Fin p.K, ∑ u : Fin p.T, ∑ t : Fin p.T,
          (mu).real (overflowEvent rate rewards C_star C_h u t a) := by
            apply Finset.sum_le_sum
            intro a ha
            apply Finset.sum_le_sum
            intro u hu
            exact MeasureTheory.measureReal_iUnion_fintype_le (μ := mu)
              (f := fun t : Fin p.T =>
                overflowEvent rate rewards C_star C_h u t a)
    _ ≤ 2 * (p.K : ℝ) * ((p.T : ℝ) + 1) *
          Real.exp (-(CanonicalRecordingRates.beta p rate.eta.val) /
            (32 * rate.eta.val)) :=
      allArmOverflowEvent_measure_sum_le rate rewards C_star C_h control0

end Bandits.Support.ReferenceFirstCollectionCorrectedNumericalOverflowSum
end
