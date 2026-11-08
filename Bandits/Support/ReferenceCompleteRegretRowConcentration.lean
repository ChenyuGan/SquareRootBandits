/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteSelectedRowExpectation
public import Bandits.Support.CompleteRowConcentration

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith

/-!
# Actual complete-reference regret row concentration

For one admissible rate, rounded reward table, and pair of execution constants,
this module combines the original-index selected-row regret with the existing
real image-grid concentration theorem. The row costs are the literal complete
reference execution's private expected regrets. They are not the manuscript's
combined cost with initialization and decoder error events. Sources:
sources/zip4/manuscript/07_public_setup.tex:123-164 and
sources/zip4/manuscript/08_main_theorem.tex:26-75.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicGridConcentration
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open Bandits.Support.ReferenceCompleteRewardMeasurability
open Bandits.Support.CompleteRowConcentration
open Bandits.Support.WholeRowHoeffding

namespace Bandits.Support.ReferenceCompleteRegretRowConcentration

variable {p : ConstructorDimensions.Parameters}

/-- Mean actual reference regret after drawing a fresh complete row for each
original row index. The same fixed rate, rounded table, and two execution
constants are used in every summand. Source: 08_main_theorem.tex:29-48. -/
@[expose] def meanReferenceRegret
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (ids : IDArray p) : ℝ :=
  (1 / (M p : ℝ)) * ∑ j : Fin (M p),
    ∫ rho : CompleteRow p,
      fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
      ∂completeRowMeasure p

/-- Decode a real image-grid matrix by the inverse of the admitted encoding. -/
@[expose] def decodeRealRewardMatrix (matrix : RealRewardMatrix p) :
    ActualInitializationPhysicalStep.GridRewardTable p :=
  (realRewardMatrixEncodingEquiv p).symm matrix

theorem decodeRealRewardMatrix_encode
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    decodeRealRewardMatrix (realRewardMatrixEncodingEquiv p rewards) = rewards :=
  (realRewardMatrixEncodingEquiv p).symm_apply_apply rewards

/-- The actual family supplied to complete-row concentration. Each cost is the
selected-row expectation of the complete physical reference regret; the real
matrix is pulled back through the accepted image-grid encoding. -/
@[expose] def actualReferenceRegretRowFamily
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ :=
  fun ids matrix j =>
    (fun z : IDArray p × CompleteRow p =>
      fixedRowPrivateExpectedRegret rate (decodeRealRewardMatrix matrix)
        C_star C_h z.1 j z.2) ∘ fun rho => (ids, rho)

/-- Specialization of the actual family to the encoded original denominator-D
table. This records that the family is the E-construction itself, not a second
reward grid or a supplied row-cost map. -/
theorem actualReferenceRegretRowFamily_encode
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (j : Fin (M p)) (rho : CompleteRow p) :
    actualReferenceRegretRowFamily rate C_star C_h ids
        (realRewardMatrixEncodingEquiv p rewards) j rho =
      fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho := by
  change fixedRowPrivateExpectedRegret rate
      (decodeRealRewardMatrix (realRewardMatrixEncodingEquiv p rewards))
      C_star C_h ids j rho = _
  rw [decodeRealRewardMatrix_encode]

/-- The finite parameter integrals defining the row mean are Borel in the one
shared identification array. -/
theorem measurable_meanReferenceRegret
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    Measurable (fun ids : IDArray p => meanReferenceRegret rate C_star C_h rewards ids) := by
  have hterm (j : Fin (M p)) :
      Measurable (fun ids : IDArray p =>
        ∫ rho : CompleteRow p,
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) := by
    exact ((measurable_fixedRowPrivateExpectedRegret
      rate rewards C_star C_h j).stronglyMeasurable.integral_prod_right'
        (ν := completeRowMeasure p)).measurable
  have hsum : Measurable (fun ids : IDArray p =>
      ∑ j : Fin (M p),
        ∫ rho : CompleteRow p,
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) := by
    apply Finset.measurable_sum Finset.univ
    intro j hj
    exact hterm j
  change Measurable (fun ids : IDArray p =>
    (1 / (M p : ℝ)) * ∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p)
  exact measurable_const.mul hsum

/-- Every fixed-ID row section of the actual family is Borel, by the joint
ID/whole-row measurability proved for the complete physical execution. -/
theorem measurable_actualReferenceRegretRowFamily
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    ∀ matrix j, Measurable (actualReferenceRegretRowFamily rate C_star C_h ids matrix j) := by
  intro matrix j
  exact (measurable_fixedRowPrivateExpectedRegret rate
    (decodeRealRewardMatrix matrix) C_star C_h j).comp
      (measurable_const.prodMk measurable_id)

/-- The literal regret interval embeds in the wider honest envelope consumed by
the existing Hoeffding calculation. -/
theorem actualReferenceRegretRowFamily_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    ∀ matrix j rho,
      actualReferenceRegretRowFamily rate C_star C_h ids matrix j rho ∈
        Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
          (3 * (p.m : ℝ) * (p.T : ℝ)) := by
  intro matrix j rho
  have h := fixedRowPrivateExpectedRegret_bounds rate
    (decodeRealRewardMatrix matrix) C_star C_h ids j rho
  change fixedRowPrivateExpectedRegret rate (decodeRealRewardMatrix matrix)
      C_star C_h ids j rho ∈
    Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
      (3 * (p.m : ℝ) * (p.T : ℝ))
  have hmt : 0 ≤ (p.m : ℝ) * (p.T : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  constructor
  · rw [show -(p.m : ℝ) * (p.T : ℝ) = -((p.m : ℝ) * (p.T : ℝ)) by ring]
    exact h.1
  · calc
      fixedRowPrivateExpectedRegret rate (decodeRealRewardMatrix matrix)
          C_star C_h ids j rho ≤ (p.m : ℝ) * (p.T : ℝ) := h.2
      _ ≤ 3 * (p.m : ℝ) * (p.T : ℝ) := by nlinarith [hmt]

/-- For each actual real-grid matrix, row independence follows from the
literal complete-row product law. -/
theorem iIndepFun_actualReferenceRegretRowFamily
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    ∀ matrix : RealRewardMatrix p,
      ProbabilityTheory.iIndepFun
        (liftedCompleteRowCost p ids
          (actualReferenceRegretRowFamily rate C_star C_h) matrix)
        (fixedIDCompleteRowsMeasure p ids) := by
  intro matrix
  exact iIndepFun_liftedCompleteRowCost p ids
    (actualReferenceRegretRowFamily rate C_star C_h)
    (measurable_actualReferenceRegretRowFamily rate C_star C_h ids) matrix

private theorem reciprocal_mul_eq_div (n : ℕ) (x : ℝ) :
    (1 / (n : ℝ)) * x = x / (n : ℝ) := by
  simp only [div_eq_mul_inv]
  ring

/-- The expected encoded family specializes to exactly the manuscript-grid
mean, with all row integrals taken under the original complete-row law. -/
theorem meanReferenceRegret_eq_actualFamily_muG
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    meanReferenceRegret rate C_star C_h rewards ids =
      WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
        (liftedCompleteRowCost p ids (actualReferenceRegretRowFamily rate C_star C_h)
          (realRewardMatrixEncodingEquiv p rewards)) := by
  have hterm (j : Fin (M p)) :
      (∫ rows : CompleteRows p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j
          (rows j) ∂completeRowsMeasure p) =
      (∫ rho : CompleteRow p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) := by
    let mp := measurePreserving_completeRowProjection p j
    have hmap : (completeRowsMeasure p).map
        (fun rows : CompleteRows p => rows j) = completeRowMeasure p := mp.map_eq
    have hgmap : AEStronglyMeasurable
        (fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j)
        ((completeRowsMeasure p).map (fun rows : CompleteRows p => rows j)) := by
      rw [hmap]
      exact (measurable_fixedRowPrivateExpectedRegret
        rate rewards C_star C_h j).comp
          (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
    calc
      _ = ∫ rho : CompleteRow p,
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
          ∂(completeRowsMeasure p).map (fun rows : CompleteRows p => rows j) := by
        symm
        exact integral_map
          (measurable_completeRowProjection p j).aemeasurable hgmap
      _ = _ := by rw [hmap]
  unfold WholeRowHoeffding.muG
  simp only [fixedIDCompleteRowsMeasure]
  simp only [liftedCompleteRowCost]
  simp only [actualReferenceRegretRowFamily, Function.comp_apply,
    decodeRealRewardMatrix_encode]
  unfold meanReferenceRegret
  rw [show (∑ j : Fin (M p),
      ∫ rows : CompleteRows p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j
          (rows j) ∂completeRowsMeasure p) =
    ∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p from Finset.sum_congr rfl (fun j hj => hterm j)]
  exact reciprocal_mul_eq_div (M p) _

private theorem integrable_completePrivateExpectedReward_rows
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    Integrable
      (fun rows : CompleteRows p =>
        completePrivateExpectedReward rate rewards C_star C_h (ids, rows))
      (completeRowsMeasure p) := by
  have hpair : Measurable (fun rows : CompleteRows p => (ids, rows)) :=
    measurable_const.prodMk measurable_id
  have hmeas := (measurable_completePrivateExpectedReward rate rewards C_star C_h).comp
    hpair
  apply Integrable.of_mem_Icc 0 ((p.m : ℝ) * (p.T : ℝ)) hmeas.aemeasurable
  exact ae_of_all _ fun rows =>
    completePrivateExpectedReward_bounds rate rewards C_star C_h (ids, rows)

/-- The finite sum of row means equals the comparator minus the integral of the
same complete-private expected reward over fresh complete rows. -/
theorem meanReferenceRegret_eq_comparator_sub_integral_rows
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    meanReferenceRegret rate C_star C_h rewards ids =
      gridComparator p rewards -
        ∫ rows : CompleteRows p,
          completePrivateExpectedReward rate rewards C_star C_h (ids, rows)
          ∂completeRowsMeasure p := by
  have htermInt (j : Fin (M p)) :
      Integrable
        (fun rows : CompleteRows p =>
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j (rows j))
        (completeRowsMeasure p) := by
    exact (measurePreserving_completeRowProjection p j).integrable_comp_of_integrable
      (integrable_fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j)
  have htermInt' : ∀ j ∈ (Finset.univ : Finset (Fin (M p))),
      Integrable
        (fun rows : CompleteRows p =>
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j (rows j))
        (completeRowsMeasure p) := by
    intro j hj
    exact htermInt j
  have haverage :
      meanReferenceRegret rate C_star C_h rewards ids =
        ∫ rows : CompleteRows p,
          (1 / (M p : ℝ)) * ∑ j : Fin (M p),
            fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j (rows j)
          ∂completeRowsMeasure p := by
    unfold meanReferenceRegret
    rw [integral_const_mul, integral_finsetSum Finset.univ htermInt']
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    let mp := measurePreserving_completeRowProjection p j
    have hmap : (completeRowsMeasure p).map
        (fun rows : CompleteRows p => rows j) = completeRowMeasure p := mp.map_eq
    have hgmap : AEStronglyMeasurable
        (fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j)
        ((completeRowsMeasure p).map (fun rows : CompleteRows p => rows j)) := by
      rw [hmap]
      exact (measurable_fixedRowPrivateExpectedRegret
        rate rewards C_star C_h j).comp
          (measurable_const.prodMk measurable_id) |>.aestronglyMeasurable
    calc
      (∫ rho : CompleteRow p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p) =
          ∫ rho : CompleteRow p,
            fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
              ∂(completeRowsMeasure p).map (fun rows : CompleteRows p => rows j) := by
        rw [hmap]
      _ = ∫ rows : CompleteRows p,
            fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j (rows j)
              ∂completeRowsMeasure p := by
        exact integral_map (measurable_completeRowProjection p j).aemeasurable hgmap
  have hpoint (rows : CompleteRows p) :=
    referenceRegret_eq_uniform_fixedRows rate rewards C_star C_h (ids, rows)
  have hprivInt := integrable_completePrivateExpectedReward_rows
    rate C_star C_h rewards ids
  calc
    _ = ∫ rows : CompleteRows p,
        (1 / (M p : ℝ)) * ∑ j : Fin (M p),
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j (rows j)
        ∂completeRowsMeasure p := haverage
    _ = ∫ rows : CompleteRows p,
        gridComparator p rewards - completePrivateExpectedReward
          rate rewards C_star C_h (ids, rows) ∂completeRowsMeasure p := by
      apply integral_congr_ae
      exact ae_of_all _ fun rows => (hpoint rows).symm
    _ = _ := by
      rw [integral_sub (integrable_const _) hprivInt]
      simp

/-- The previous identity is literally the iterated expectation of the original
complete reward over whole rows and all original private coordinates. -/
theorem meanReferenceRegret_eq_comparator_sub_iterated_original_expectation
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    meanReferenceRegret rate C_star C_h rewards ids =
      gridComparator p rewards -
        ∫ rows : CompleteRows p,
          ∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
            ReferenceCompletePhysicalRewards.completeReward rate ((ids, rows), e)
              rewards C_star C_h
              ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p
          ∂completeRowsMeasure p := by
  rw [meanReferenceRegret_eq_comparator_sub_integral_rows]
  rfl

/-- The actual reference-regret good event for rows: after the public output is
fixed, every denominator-D reward table obeys the stated regret inequality. -/
@[expose] def referenceCompleteRegretRowGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) : Set (CompleteRows p) :=
  {rows | ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
    gridComparator p rewards - completePrivateExpectedReward
      rate rewards C_star C_h (ids, rows) ≤
      meanReferenceRegret rate C_star C_h rewards ids +
        2 * rowConcentrationScale p}

/-- The joint public good event, formed from the fixed-ID row event without any
good-ID premise or exceptional public fibre. -/
@[expose] def referenceCompleteRegretPublicGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    Set (PublishedOutput p) :=
  {published | ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
    gridComparator p rewards - completePrivateExpectedReward
      rate rewards C_star C_h published ≤
      meanReferenceRegret rate C_star C_h rewards published.1 +
        2 * rowConcentrationScale p}

/-- For every encoded real-grid matrix, its concentration mean is the actual
meanReferenceRegret, and its realized average is the actual row regret average.
These are the two substitutions that identify the source event with C's event.
-/
private theorem encoded_row_average_eq
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rows : CompleteRows p) :
    WholeRowHoeffding.barG
        (liftedCompleteRowCost p ids (actualReferenceRegretRowFamily rate C_star C_h)
          (realRewardMatrixEncodingEquiv p rewards)) rows =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j (rows j) := by
  unfold WholeRowHoeffding.barG liftedCompleteRowCost
  simp_rw [actualReferenceRegretRowFamily_encode]
  exact (reciprocal_mul_eq_div (M p) _).symm

/-- The actual every-reward event is exactly C's event for the encoded actual
family. The equality uses E's fixed-output uniform mixture, not a conditional
law or an almost-everywhere public version. -/
theorem referenceCompleteRegretRowGoodEvent_eq_concentration
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    referenceCompleteRegretRowGoodEvent rate C_star C_h ids =
      completeRowConcentrationGoodEvent p ids
        (actualReferenceRegretRowFamily rate C_star C_h) := by
  classical
  ext rows
  constructor
  · intro h
    change ∀ matrix : RealRewardMatrix p,
      WholeRowHoeffding.barG
          (liftedCompleteRowCost p ids
            (actualReferenceRegretRowFamily rate C_star C_h) matrix) rows ≤
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
          (liftedCompleteRowCost p ids
            (actualReferenceRegretRowFamily rate C_star C_h) matrix) +
          2 * rowConcentrationScale p
    intro matrix
    let rewards : ActualInitializationPhysicalStep.GridRewardTable p :=
      (realRewardMatrixEncodingEquiv p).symm matrix
    have hregret := referenceRegret_eq_uniform_fixedRows
      rate rewards C_star C_h (ids, rows)
    have hmean := meanReferenceRegret_eq_actualFamily_muG
      rate C_star C_h rewards ids
    have hencode : realRewardMatrixEncodingEquiv p rewards = matrix :=
      (realRewardMatrixEncodingEquiv p).apply_symm_apply matrix
    have hbar :
        WholeRowHoeffding.barG
            (liftedCompleteRowCost p ids
              (actualReferenceRegretRowFamily rate C_star C_h) matrix) rows =
          gridComparator p rewards - completePrivateExpectedReward
            rate rewards C_star C_h (ids, rows) := by
      rw [← hencode, encoded_row_average_eq rate C_star C_h ids rewards rows]
      exact hregret.symm
    have hmu :
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
            (liftedCompleteRowCost p ids
              (actualReferenceRegretRowFamily rate C_star C_h) matrix) =
          meanReferenceRegret rate C_star C_h rewards ids := by
      rw [← hencode]
      exact hmean.symm
    have hbound := h rewards
    rw [← hbar, ← hmu] at hbound
    exact hbound
  · intro h
    change ∀ matrix : RealRewardMatrix p,
      WholeRowHoeffding.barG
          (liftedCompleteRowCost p ids
            (actualReferenceRegretRowFamily rate C_star C_h) matrix) rows ≤
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
          (liftedCompleteRowCost p ids
            (actualReferenceRegretRowFamily rate C_star C_h) matrix) +
          2 * rowConcentrationScale p at h
    change ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
      gridComparator p rewards - completePrivateExpectedReward
        rate rewards C_star C_h (ids, rows) ≤
      meanReferenceRegret rate C_star C_h rewards ids +
        2 * rowConcentrationScale p
    intro rewards
    let matrix := realRewardMatrixEncodingEquiv p rewards
    have hregret := referenceRegret_eq_uniform_fixedRows
      rate rewards C_star C_h (ids, rows)
    have hmean := meanReferenceRegret_eq_actualFamily_muG
      rate C_star C_h rewards ids
    have hbar :
        WholeRowHoeffding.barG
            (liftedCompleteRowCost p ids
              (actualReferenceRegretRowFamily rate C_star C_h) matrix) rows =
          gridComparator p rewards - completePrivateExpectedReward
            rate rewards C_star C_h (ids, rows) := by
      rw [show matrix = realRewardMatrixEncodingEquiv p rewards from rfl,
        encoded_row_average_eq rate C_star C_h ids rewards rows]
      exact hregret.symm
    have hmu :
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
            (liftedCompleteRowCost p ids
              (actualReferenceRegretRowFamily rate C_star C_h) matrix) =
          meanReferenceRegret rate C_star C_h rewards ids := by
      rw [show matrix = realRewardMatrixEncodingEquiv p rewards from rfl]
      exact hmean.symm
    have hbound := h matrix
    rw [hbar, hmu] at hbound
    exact hbound

/-- The every-reward row event is measurable under the original complete-row
law, as follows from its exact equality with the existing measurable event. -/
theorem measurableSet_referenceCompleteRegretRowGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    MeasurableSet (referenceCompleteRegretRowGoodEvent rate C_star C_h ids) := by
  rw [referenceCompleteRegretRowGoodEvent_eq_concentration]
  exact measurableSet_completeRowConcentrationGoodEvent p ids
    (actualReferenceRegretRowFamily rate C_star C_h)
    (measurable_actualReferenceRegretRowFamily rate C_star C_h ids)

/-- Fixed-ID row failure probability for the actual complete-reference family.
-/
theorem referenceCompleteRegretRowGoodEvent_failure_prob_le
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    (fixedIDCompleteRowsMeasure p ids).real
      (referenceCompleteRegretRowGoodEvent rate C_star C_h ids)ᶜ ≤
        1 / (2 * (N p : ℝ)) := by
  rw [referenceCompleteRegretRowGoodEvent_eq_concentration]
  exact completeRowConcentrationGoodEvent_failure_prob_le p ids
    (actualReferenceRegretRowFamily rate C_star C_h)
    (measurable_actualReferenceRegretRowFamily rate C_star C_h ids)
    (fun matrix j => ae_of_all _ fun rho =>
      actualReferenceRegretRowFamily_bounds rate C_star C_h ids matrix j rho)

/-- The same fixed-ID bound is stated on the original complete-row measure. -/
theorem referenceCompleteRegretRowGoodEvent_failure_prob_le_completeRows
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    (completeRowsMeasure p).real
      (referenceCompleteRegretRowGoodEvent rate C_star C_h ids)ᶜ ≤
        1 / (2 * (N p : ℝ)) := by
  change (fixedIDCompleteRowsMeasure p ids).real
    (referenceCompleteRegretRowGoodEvent rate C_star C_h ids)ᶜ ≤
      1 / (2 * (N p : ℝ))
  exact referenceCompleteRegretRowGoodEvent_failure_prob_le rate C_star C_h ids

/-- The joint event is Borel on the full published-output carrier. It is a
finite intersection over original grid tables of inequalities between the
joint Borel private expectation and the parameter-integral row mean. -/
theorem measurableSet_referenceCompleteRegretPublicGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    MeasurableSet (referenceCompleteRegretPublicGoodEvent rate C_star C_h) := by
  classical
  rw [referenceCompleteRegretPublicGoodEvent, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro rewards
  have hleft : Measurable (fun published : PublishedOutput p =>
      gridComparator p rewards -
        completePrivateExpectedReward rate rewards C_star C_h published) :=
    measurable_const.sub
      (measurable_completePrivateExpectedReward rate rewards C_star C_h)
  have hid : Measurable (fun published : PublishedOutput p => published.1) :=
    measurable_fst
  have hmean :=
    (measurable_meanReferenceRegret rate C_star C_h rewards).comp hid
  have hright : Measurable (fun published : PublishedOutput p =>
      meanReferenceRegret rate C_star C_h rewards published.1 +
        2 * rowConcentrationScale p) :=
    hmean.add (measurable_const : Measurable
      (fun _ : PublishedOutput p => 2 * rowConcentrationScale p))
  exact measurableSet_le hleft hright

/-- Integrating the fixed-ID failure estimate over the original ID-array law
gives the joint failure bound under the original published-output measure. -/
theorem referenceCompleteRegretPublicGoodEvent_failure_prob_le
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    (publishedOutputMeasure p).real
    ((referenceCompleteRegretPublicGoodEvent rate C_star C_h)ᶜ) ≤
        1 / (2 * (N p : ℝ)) := by
  let c : ℝ := 1 / (2 * (N p : ℝ))
  let badEvent : Set (PublishedOutput p) :=
    (referenceCompleteRegretPublicGoodEvent rate C_star C_h)ᶜ
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hmeas := measurableSet_referenceCompleteRegretPublicGoodEvent
    rate C_star C_h
  have hcompl : MeasurableSet badEvent := by
    exact hmeas.compl
  have hsection (ids : IDArray p) :
      completeRowsMeasure p
        ((fun rows : CompleteRows p => (ids, rows)) ⁻¹' badEvent) ≤
          ENNReal.ofReal c := by
    have hset :
        (fun rows : CompleteRows p => (ids, rows)) ⁻¹' badEvent =
          (referenceCompleteRegretRowGoodEvent rate C_star C_h ids)ᶜ := by
      ext rows
      simp [badEvent, referenceCompleteRegretPublicGoodEvent,
        referenceCompleteRegretRowGoodEvent]
    rw [hset]
    have hrow := referenceCompleteRegretRowGoodEvent_failure_prob_le_completeRows
      rate C_star C_h ids
    rw [measureReal_def] at hrow
    have hreal := ENNReal.ofReal_le_ofReal hrow
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at hreal
    simpa [c] using hreal
  have hprod :
      publishedOutputMeasure p badEvent ≤
        ENNReal.ofReal c := by
    rw [publishedOutputMeasure, Measure.prod_apply hcompl]
    calc
      ∫⁻ ids : IDArray p,
          completeRowsMeasure p
            ((fun rows : CompleteRows p => (ids, rows)) ⁻¹' badEvent)
          ∂idArrayMeasure p ≤
      ∫⁻ _ : IDArray p, ENNReal.ofReal c ∂idArrayMeasure p :=
          lintegral_mono hsection
      _ = ENNReal.ofReal c := by simp
  rw [measureReal_def]
  calc
    (publishedOutputMeasure p badEvent).toReal ≤
        (ENNReal.ofReal c).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hprod
    _ = c := ENNReal.toReal_ofReal hc
    _ = 1 / (2 * (N p : ℝ)) := rfl

/-- On a fixed good public output, the source regret inequality holds for every
original reward table. The quantifier remains outside the private expectation.
-/
theorem referenceCompleteRegretRowGoodEvent_bound_at
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) (rows : CompleteRows p)
    (hgood : rows ∈ referenceCompleteRegretRowGoodEvent rate C_star C_h ids)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    gridComparator p rewards - completePrivateExpectedReward
      rate rewards C_star C_h (ids, rows) ≤
      meanReferenceRegret rate C_star C_h rewards ids +
        2 * rowConcentrationScale p :=
  hgood rewards

end Bandits.Support.ReferenceCompleteRegretRowConcentration

end
