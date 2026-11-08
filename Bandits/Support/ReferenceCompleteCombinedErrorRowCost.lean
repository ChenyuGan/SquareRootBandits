/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteErrorSelectedRowProbability
public import Bandits.Support.ReferenceCompleteRegretRowConcentration

import Bandits.Support.RewardMatrixCount
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Combined complete-reference regret and error row cost

This module constructs the manuscript's single row cost from the actual
complete-reference regret and the original-private probability of the literal
complete-error union. It proves one simultaneous all-grid concentration event
for that combined cost, retaining the original public-output and private-law
carriers.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicGridConcentration
open Bandits.Support.ReferenceCompleteSelectedRowExpectation
open Bandits.Support.ReferenceCompleteRegretRowConcentration
open Bandits.Support.ReferenceCompleteErrorSelectedRowProbability
open Bandits.Support.CompleteRowConcentration
open Bandits.Support.WholeRowHoeffding

namespace Bandits.Support.ReferenceCompleteCombinedErrorRowCost

variable {p : ConstructorDimensions.Parameters}

private theorem reciprocal_mul_eq_div (n : ℕ) (x : ℝ) :
    (1 / (n : ℝ)) * x = x / (n : ℝ) := by
  simp only [div_eq_mul_inv]
  ring

/-- The manuscript's literal combined complete-row cost on the actual
denominator-`D` reward table and selected complete continuous row. -/
@[expose] def actualCombinedErrorRowCost
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) : ℝ :=
  fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho +
    2 * (p.m : ℝ) * (p.T : ℝ) *
      completeErrorFixedRowProbability rate rewards C_star C_h ids j rho

/-- Pull the actual combined row cost back from the accepted real image-grid
encoding used by complete-row concentration. -/
@[expose] def actualCombinedErrorRowFamily
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ :=
  fun ids matrix j rho =>
    ((fun z : IDArray p × CompleteRow p =>
      actualCombinedErrorRowCost rate (decodeRealRewardMatrix matrix)
        C_star C_h z.1 j z.2) ∘ fun rho => (ids, rho)) rho

/-- The original continuous-row mean of the combined cost, at one fixed ID
array and one actual denominator-`D` reward table. -/
@[expose] def meanActualCombinedErrorRowCost
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) : ℝ :=
  (1 / (M p : ℝ)) * ∑ j : Fin (M p),
    ∫ rho : CompleteRow p,
      actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
      ∂completeRowMeasure p

/-- The realized combined row average at a fixed published output. -/
@[expose] def actualCombinedErrorRowAverage
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) : ℝ :=
  (1 / (M p : ℝ)) * ∑ j : Fin (M p),
    actualCombinedErrorRowCost rate rewards C_star C_h
      published.1 j (published.2 j)

/-- The single all-reward combined-row event for fixed public IDs. -/
@[expose] def actualCombinedErrorRowGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) : Set (CompleteRows p) :=
  {rows | ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
    (1 / (M p : ℝ)) * ∑ j : Fin (M p),
      actualCombinedErrorRowCost rate rewards C_star C_h ids j (rows j) ≤
        meanActualCombinedErrorRowCost rate rewards C_star C_h ids +
          2 * rowConcentrationScale p}

/-- The combined-row event on the original published-output carrier. The one
public output is fixed before the all-reward quantifier and private expectation.
-/
@[expose] def actualCombinedErrorPublicGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    Set (PublishedOutput p) :=
  {published | ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
    actualCombinedErrorRowAverage rate rewards C_star C_h published ≤
      meanActualCombinedErrorRowCost rate rewards C_star C_h published.1 +
        2 * rowConcentrationScale p}

/-- The actual fixed-ID/index row cost is jointly Borel in the ID array and
the whole continuous row. -/
theorem measurable_actualCombinedErrorRowCost
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (j : Fin (M p)) :
    Measurable (fun z : IDArray p × CompleteRow p =>
      actualCombinedErrorRowCost rate rewards C_star C_h z.1 j z.2) := by
  have hF := measurable_fixedRowPrivateExpectedRegret rate rewards C_star C_h j
  have hE := measurable_completeErrorFixedRowProbability rate rewards C_star C_h j
  change Measurable (fun z : IDArray p × CompleteRow p =>
    fixedRowPrivateExpectedRegret rate rewards C_star C_h z.1 j z.2 +
      2 * (p.m : ℝ) * (p.T : ℝ) *
        completeErrorFixedRowProbability rate rewards C_star C_h z.1 j z.2)
  exact hF.add (measurable_const.mul hE)

/-- The pointwise interval for the literal combined cost follows from the
original fixed-row regret interval and the genuine zero-one union probability.
-/
theorem actualCombinedErrorRowCost_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) (rho : CompleteRow p) :
    actualCombinedErrorRowCost rate rewards C_star C_h ids j rho ∈
      Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ)) := by
  change fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho +
      2 * (p.m : ℝ) * (p.T : ℝ) *
        completeErrorFixedRowProbability rate rewards C_star C_h ids j rho ∈ _
  have hF := fixedRowPrivateExpectedRegret_bounds rate rewards C_star C_h ids j rho
  have hE := completeErrorFixedRowProbability_bounds rate rewards C_star C_h ids j rho
  have h := Bandits.Support.RewardMatrixCount.combinedCost_mem_Icc
    (m := (p.m : ℝ)) (T := (p.T : ℝ))
    (F := fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho)
    (E := completeErrorFixedRowProbability rate rewards C_star C_h ids j rho)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    ⟨by simpa only [neg_mul] using hF.1, hF.2⟩
    ⟨hE.1, hE.2⟩
  simpa only [neg_mul] using h

/-- Each fixed-ID actual combined row is integrable under the original
continuous complete-row law. -/
theorem integrable_actualCombinedErrorRowCost
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (ids : IDArray p) (j : Fin (M p)) :
    Integrable (actualCombinedErrorRowCost rate rewards C_star C_h ids j)
      (completeRowMeasure p) := by
  have hpair : Measurable (fun rho : CompleteRow p => (ids, rho)) :=
    measurable_const.prodMk measurable_id
  have hmeas := (measurable_actualCombinedErrorRowCost rate rewards C_star C_h j).comp hpair
  apply Integrable.of_mem_Icc (-(p.m : ℝ) * (p.T : ℝ))
    (3 * (p.m : ℝ) * (p.T : ℝ)) hmeas.aemeasurable
  exact ae_of_all _ fun rho =>
    actualCombinedErrorRowCost_bounds rate rewards C_star C_h ids j rho

/-- The real-grid family specializes to the same actual source table through
the admitted encoding equivalence. -/
theorem actualCombinedErrorRowFamily_encode
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (j : Fin (M p)) (rho : CompleteRow p) :
    actualCombinedErrorRowFamily rate C_star C_h ids
        (realRewardMatrixEncodingEquiv p rewards) j rho =
      actualCombinedErrorRowCost rate rewards C_star C_h ids j rho := by
  change actualCombinedErrorRowCost rate
    (decodeRealRewardMatrix (realRewardMatrixEncodingEquiv p rewards))
    C_star C_h ids j rho = _
  exact congrArg (fun r => actualCombinedErrorRowCost rate r C_star C_h ids j rho)
    (decodeRealRewardMatrix_encode rewards)

/-- Every fixed-ID/index section of the encoded actual combined family is
Borel. -/
theorem measurable_actualCombinedErrorRowFamily
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    ∀ matrix j, Measurable (actualCombinedErrorRowFamily rate C_star C_h ids matrix j) := by
  intro matrix j
  change Measurable
    ((fun z : IDArray p × CompleteRow p =>
      actualCombinedErrorRowCost rate (decodeRealRewardMatrix matrix)
        C_star C_h z.1 j z.2) ∘ fun rho => (ids, rho))
  exact (measurable_actualCombinedErrorRowCost rate (decodeRealRewardMatrix matrix)
    C_star C_h j).comp (measurable_const.prodMk measurable_id)

/-- The encoded actual combined family retains the complete source interval.
-/
theorem actualCombinedErrorRowFamily_bounds
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    ∀ matrix j rho,
      actualCombinedErrorRowFamily rate C_star C_h ids matrix j rho ∈
        Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
          (3 * (p.m : ℝ) * (p.T : ℝ)) := by
  intro matrix j rho
  exact actualCombinedErrorRowCost_bounds rate (decodeRealRewardMatrix matrix)
    C_star C_h ids j rho

/-- The same-ID mean is exactly the manuscript mean-regret term plus the
literal complete-error probability mean, with the source's shared constants.
-/
theorem meanActualCombinedErrorRowCost_eq_components
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    meanActualCombinedErrorRowCost rate rewards C_star C_h ids =
      meanReferenceRegret rate C_star C_h rewards ids +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          completeErrorMean rate rewards C_star C_h ids := by
  have hterm (j : Fin (M p)) :
      (∫ rho : CompleteRow p,
        actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p) =
      (∫ rho : CompleteRow p,
        fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p) +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          (∫ rho : CompleteRow p,
            completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
            ∂completeRowMeasure p) := by
    unfold actualCombinedErrorRowCost
    have hF := integrable_fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j
    have hE := integrable_completeErrorFixedRowProbability rate rewards C_star C_h ids j
    have hscaled : Integrable
        (fun rho : CompleteRow p =>
          2 * (p.m : ℝ) * (p.T : ℝ) *
            completeErrorFixedRowProbability rate rewards C_star C_h ids j rho)
        (completeRowMeasure p) := hE.const_mul (2 * (p.m : ℝ) * (p.T : ℝ))
    rw [integral_add hF hscaled, integral_const_mul]
  unfold meanActualCombinedErrorRowCost meanReferenceRegret completeErrorMean
  rw [show (∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p) =
      ∑ j : Fin (M p),
        ((∫ rho : CompleteRow p,
          fixedRowPrivateExpectedRegret rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          (∫ rho : CompleteRow p,
            completeErrorFixedRowProbability rate rewards C_star C_h ids j rho
            ∂completeRowMeasure p)) from
      Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring_nf

/-- The combined mean is Borel in the original shared ID array. -/
theorem measurable_meanActualCombinedErrorRowCost
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ) :
    Measurable (fun ids : IDArray p =>
      meanActualCombinedErrorRowCost rate rewards C_star C_h ids) := by
  have hterm (j : Fin (M p)) :
      Measurable (fun ids : IDArray p =>
        ∫ rho : CompleteRow p,
          actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p) := by
    exact (measurable_actualCombinedErrorRowCost rate rewards C_star C_h j).stronglyMeasurable
      |>.integral_prod_right' (ν := completeRowMeasure p) |>.measurable
  change Measurable (fun ids : IDArray p => (1 / (M p : ℝ)) *
    ∑ j : Fin (M p),
      ∫ rho : CompleteRow p,
        actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p)
  exact measurable_const.mul
    (Finset.univ.measurable_fun_sum fun j hj => hterm j)

/-- The source mean equals the generic whole-row Hoeffding mean for the one
encoded actual combined family. This uses the measure-preserving projection of
each whole continuous row, not a new row law. -/
theorem meanActualCombinedErrorRowCost_eq_actualFamily_muG
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (ids : IDArray p) :
    meanActualCombinedErrorRowCost rate rewards C_star C_h ids =
      WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
        (liftedCompleteRowCost p ids (actualCombinedErrorRowFamily rate C_star C_h)
          (realRewardMatrixEncodingEquiv p rewards)) := by
  have hterm (j : Fin (M p)) :
      (∫ rows : CompleteRows p,
        actualCombinedErrorRowCost rate rewards C_star C_h ids j (rows j)
        ∂completeRowsMeasure p) =
      (∫ rho : CompleteRow p,
        actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
        ∂completeRowMeasure p) := by
    let mp := measurePreserving_completeRowProjection p j
    have hmap : (completeRowsMeasure p).map
        (fun rows : CompleteRows p => rows j) = completeRowMeasure p := mp.map_eq
    have hgmap : AEStronglyMeasurable
        (actualCombinedErrorRowCost rate rewards C_star C_h ids j)
        ((completeRowsMeasure p).map (fun rows : CompleteRows p => rows j)) := by
      rw [hmap]
      have hpair : Measurable (fun rho : CompleteRow p => (ids, rho)) :=
        measurable_const.prodMk measurable_id
      exact (measurable_actualCombinedErrorRowCost rate rewards C_star C_h j).comp
        hpair |>.aestronglyMeasurable
    calc
      _ = ∫ rho : CompleteRow p,
          actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
          ∂(completeRowsMeasure p).map (fun rows : CompleteRows p => rows j) := by
        symm
        exact integral_map (measurable_completeRowProjection p j).aemeasurable hgmap
      _ = _ := by rw [hmap]
  unfold WholeRowHoeffding.muG
  simp only [fixedIDCompleteRowsMeasure]
  simp only [liftedCompleteRowCost]
  simp only [actualCombinedErrorRowFamily, Function.comp_apply,
    decodeRealRewardMatrix_encode]
  unfold meanActualCombinedErrorRowCost
  rw [show (∑ j : Fin (M p),
      ∫ rows : CompleteRows p,
        actualCombinedErrorRowCost rate rewards C_star C_h ids j (rows j)
        ∂completeRowsMeasure p) =
      ∑ j : Fin (M p),
        ∫ rho : CompleteRow p,
          actualCombinedErrorRowCost rate rewards C_star C_h ids j rho
          ∂completeRowMeasure p from
      Finset.sum_congr rfl (fun j _ => hterm j)]
  exact reciprocal_mul_eq_div (M p) _

/-- The realized encoded-family average is exactly the average of the source
combined costs on the selected rows. -/
theorem actualCombinedErrorRowAverage_eq_actualFamily_barG
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rows : CompleteRows p) :
    WholeRowHoeffding.barG
        (liftedCompleteRowCost p ids (actualCombinedErrorRowFamily rate C_star C_h)
          (realRewardMatrixEncodingEquiv p rewards)) rows =
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        actualCombinedErrorRowCost rate rewards C_star C_h ids j (rows j) := by
  unfold WholeRowHoeffding.barG liftedCompleteRowCost
  simp_rw [actualCombinedErrorRowFamily_encode]
  exact (reciprocal_mul_eq_div (M p) _).symm

/-- The actual all-grid row event is exactly the generic concentration event
for this single encoded combined family. -/
theorem actualCombinedErrorRowGoodEvent_eq_concentration
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    actualCombinedErrorRowGoodEvent rate C_star C_h ids =
      completeRowConcentrationGoodEvent p ids
        (actualCombinedErrorRowFamily rate C_star C_h) := by
  classical
  ext rows
  constructor
  · intro h
    change ∀ matrix : RealRewardMatrix p,
      WholeRowHoeffding.barG
          (liftedCompleteRowCost p ids
            (actualCombinedErrorRowFamily rate C_star C_h) matrix) rows ≤
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
          (liftedCompleteRowCost p ids
            (actualCombinedErrorRowFamily rate C_star C_h) matrix) +
          2 * rowConcentrationScale p
    intro matrix
    let rewards : ActualInitializationPhysicalStep.GridRewardTable p :=
      (realRewardMatrixEncodingEquiv p).symm matrix
    have hbar := actualCombinedErrorRowAverage_eq_actualFamily_barG
      rate C_star C_h ids rewards rows
    have hmu := meanActualCombinedErrorRowCost_eq_actualFamily_muG
      rate C_star C_h rewards ids
    have hencode : realRewardMatrixEncodingEquiv p rewards = matrix :=
      (realRewardMatrixEncodingEquiv p).apply_symm_apply matrix
    have hbar' :
        WholeRowHoeffding.barG
            (liftedCompleteRowCost p ids
              (actualCombinedErrorRowFamily rate C_star C_h) matrix) rows =
          (1 / (M p : ℝ)) * ∑ j : Fin (M p),
            actualCombinedErrorRowCost rate rewards C_star C_h ids j (rows j) := by
      rw [← hencode]
      exact hbar
    have hmu' :
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
            (liftedCompleteRowCost p ids
              (actualCombinedErrorRowFamily rate C_star C_h) matrix) =
          meanActualCombinedErrorRowCost rate rewards C_star C_h ids := by
      rw [← hencode]
      exact hmu.symm
    have hbound := h rewards
    rw [← hbar', ← hmu'] at hbound
    exact hbound
  · intro h
    change ∀ matrix : RealRewardMatrix p,
      WholeRowHoeffding.barG
          (liftedCompleteRowCost p ids
            (actualCombinedErrorRowFamily rate C_star C_h) matrix) rows ≤
        WholeRowHoeffding.muG (fixedIDCompleteRowsMeasure p ids)
          (liftedCompleteRowCost p ids
            (actualCombinedErrorRowFamily rate C_star C_h) matrix) +
          2 * rowConcentrationScale p at h
    change ∀ rewards : ActualInitializationPhysicalStep.GridRewardTable p,
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        actualCombinedErrorRowCost rate rewards C_star C_h ids j (rows j) ≤
      meanActualCombinedErrorRowCost rate rewards C_star C_h ids +
        2 * rowConcentrationScale p
    intro rewards
    let matrix := realRewardMatrixEncodingEquiv p rewards
    have hbar := actualCombinedErrorRowAverage_eq_actualFamily_barG
      rate C_star C_h ids rewards rows
    have hmu := meanActualCombinedErrorRowCost_eq_actualFamily_muG
      rate C_star C_h rewards ids
    have hbound := h matrix
    rw [hbar, hmu.symm] at hbound
    exact hbound

/-- The fixed-ID combined all-grid event is Borel under the original row law.
-/
theorem measurableSet_actualCombinedErrorRowGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    MeasurableSet (actualCombinedErrorRowGoodEvent rate C_star C_h ids) := by
  rw [actualCombinedErrorRowGoodEvent_eq_concentration]
  exact measurableSet_completeRowConcentrationGoodEvent p ids
    (actualCombinedErrorRowFamily rate C_star C_h)
    (measurable_actualCombinedErrorRowFamily rate C_star C_h ids)

/-- At every fixed ID array the one combined all-grid event fails with
probability at most `1/(2N)`, by the accepted complete-row concentration
theorem applied to the actual encoded family. -/
theorem actualCombinedErrorRowGoodEvent_failure_prob_le
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    (fixedIDCompleteRowsMeasure p ids).real
      (actualCombinedErrorRowGoodEvent rate C_star C_h ids)ᶜ ≤
        1 / (2 * (N p : ℝ)) := by
  rw [actualCombinedErrorRowGoodEvent_eq_concentration]
  exact completeRowConcentrationGoodEvent_failure_prob_le p ids
    (actualCombinedErrorRowFamily rate C_star C_h)
    (measurable_actualCombinedErrorRowFamily rate C_star C_h ids)
    (fun matrix j => ae_of_all _ fun rho =>
      actualCombinedErrorRowFamily_bounds rate C_star C_h ids matrix j rho)

/-- The fixed-ID failure estimate on the original complete-row product law.
-/
theorem actualCombinedErrorRowGoodEvent_failure_prob_le_completeRows
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (ids : IDArray p) :
    (completeRowsMeasure p).real
      (actualCombinedErrorRowGoodEvent rate C_star C_h ids)ᶜ ≤
        1 / (2 * (N p : ℝ)) := by
  change (fixedIDCompleteRowsMeasure p ids).real
      (actualCombinedErrorRowGoodEvent rate C_star C_h ids)ᶜ ≤
    1 / (2 * (N p : ℝ))
  exact actualCombinedErrorRowGoodEvent_failure_prob_le rate C_star C_h ids

/-- The joint public-output combined event is Borel on the full product law.
-/
theorem measurableSet_actualCombinedErrorPublicGoodEvent
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    MeasurableSet (actualCombinedErrorPublicGoodEvent rate C_star C_h) := by
  classical
  rw [actualCombinedErrorPublicGoodEvent, Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro rewards
  have hterm (j : Fin (M p)) :
      Measurable (fun published : PublishedOutput p =>
        actualCombinedErrorRowCost rate rewards C_star C_h
          published.1 j (published.2 j)) := by
    have hrows : Measurable (fun published : PublishedOutput p => published.2 j) :=
      (measurable_pi_apply j).comp measurable_snd
    have hpair : Measurable
        (fun published : PublishedOutput p => (published.1, published.2 j)) :=
      measurable_fst.prodMk hrows
    change Measurable
      ((fun z : IDArray p × CompleteRow p =>
        actualCombinedErrorRowCost rate rewards C_star C_h z.1 j z.2) ∘
          fun published : PublishedOutput p => (published.1, published.2 j))
    exact (measurable_actualCombinedErrorRowCost rate rewards C_star C_h j).comp
      hpair
  have hleft : Measurable (fun published : PublishedOutput p =>
      actualCombinedErrorRowAverage rate rewards C_star C_h published) := by
    change Measurable (fun published : PublishedOutput p =>
      (1 / (M p : ℝ)) * ∑ j : Fin (M p),
        actualCombinedErrorRowCost rate rewards C_star C_h
          published.1 j (published.2 j))
    exact measurable_const.mul (Finset.univ.measurable_fun_sum
      fun j hj => hterm j)
  have hid : Measurable (fun published : PublishedOutput p => published.1) :=
    measurable_fst
  have hmean := (measurable_meanActualCombinedErrorRowCost rate rewards C_star C_h).comp
    hid
  have hright : Measurable (fun published : PublishedOutput p =>
      meanActualCombinedErrorRowCost rate rewards C_star C_h published.1 +
        2 * rowConcentrationScale p) :=
    hmean.add (measurable_const : Measurable
      (fun _ : PublishedOutput p => 2 * rowConcentrationScale p))
  exact measurableSet_le hleft hright

/-- Integrating the fixed-ID failure estimate over the original shared-ID law
gives the same `1/(2N)` failure bound for one published output. -/
theorem actualCombinedErrorPublicGoodEvent_failure_prob_le
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ) :
    (publishedOutputMeasure p).real
      ((actualCombinedErrorPublicGoodEvent rate C_star C_h)ᶜ) ≤
        1 / (2 * (N p : ℝ)) := by
  let c : ℝ := 1 / (2 * (N p : ℝ))
  let badEvent : Set (PublishedOutput p) :=
    (actualCombinedErrorPublicGoodEvent rate C_star C_h)ᶜ
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hmeas := measurableSet_actualCombinedErrorPublicGoodEvent rate C_star C_h
  have hcompl : MeasurableSet badEvent := hmeas.compl
  have hsection (ids : IDArray p) :
      completeRowsMeasure p
        ((fun rows : CompleteRows p => (ids, rows)) ⁻¹' badEvent) ≤
          ENNReal.ofReal c := by
    have hset :
        (fun rows : CompleteRows p => (ids, rows)) ⁻¹' badEvent =
          (actualCombinedErrorRowGoodEvent rate C_star C_h ids)ᶜ := by
      ext rows
      simp [badEvent, actualCombinedErrorPublicGoodEvent,
        actualCombinedErrorRowGoodEvent, actualCombinedErrorRowAverage]
    rw [hset]
    have hrow := actualCombinedErrorRowGoodEvent_failure_prob_le_completeRows
      rate C_star C_h ids
    rw [measureReal_def] at hrow
    have hreal := ENNReal.ofReal_le_ofReal hrow
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)] at hreal
    simpa [c] using hreal
  have hprod :
      publishedOutputMeasure p badEvent ≤ ENNReal.ofReal c := by
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

/-- At every fixed published output the combined row average equals the
comparator minus the original private expected reward plus the error-union
probability under the unchanged original private tuple and index law. -/
theorem actualCombinedErrorRowAverage_eq_original_private_expression
    (rate : ReferenceCompletePhysicalRewards.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)
    (published : PublishedOutput p) :
    actualCombinedErrorRowAverage rate rewards C_star C_h published =
      gridComparator p rewards -
        ReferenceCompleteRewardMeasurability.completePrivateExpectedReward
          rate rewards C_star C_h published +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          (∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
            completeErrorIndicator rate rewards C_star C_h ((published.1, published.2), e)
            ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have hF := referenceRegret_eq_uniform_fixedRows rate rewards C_star C_h published
  have hE := completeError_privateExpectation_eq_fixedRowAverage
    rate rewards C_star C_h published.1 published.2
  unfold actualCombinedErrorRowAverage actualCombinedErrorRowCost
  calc
    _ = (1 / (M p : ℝ)) *
          ∑ j : Fin (M p),
            fixedRowPrivateExpectedRegret rate rewards C_star C_h
              published.1 j (published.2 j) +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          ((1 / (M p : ℝ)) *
            ∑ j : Fin (M p),
              completeErrorFixedRowProbability rate rewards C_star C_h
                published.1 j (published.2 j)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ = gridComparator p rewards -
          ReferenceCompleteRewardMeasurability.completePrivateExpectedReward
            rate rewards C_star C_h published +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          (∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
            completeErrorIndicator rate rewards C_star C_h
              ((published.1, published.2), e)
            ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
      rw [← hF, ← hE]

/-- On one actual combined-good published output, the original-private
expression is bounded simultaneously for every denominator-`D` reward table.
-/
theorem actualCombinedErrorPublicGoodEvent_bound_at
    (rate : ReferenceCompletePhysicalRewards.RateInput p) (C_star C_h : ℝ)
    (published : PublishedOutput p)
    (hgood : published ∈ actualCombinedErrorPublicGoodEvent rate C_star C_h)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    gridComparator p rewards -
        ReferenceCompleteRewardMeasurability.completePrivateExpectedReward
          rate rewards C_star C_h published +
        2 * (p.m : ℝ) * (p.T : ℝ) *
          (∫ e : BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p,
            completeErrorIndicator rate rewards C_star C_h ((published.1, published.2), e)
            ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) ≤
      meanActualCombinedErrorRowCost rate rewards C_star C_h published.1 +
        2 * rowConcentrationScale p := by
  rw [← actualCombinedErrorRowAverage_eq_original_private_expression
    rate rewards C_star C_h published]
  exact hgood rewards

end Bandits.Support.ReferenceCompleteCombinedErrorRowCost

end
