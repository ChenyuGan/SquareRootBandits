/-
Copyright (c) 2026 Bandits contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CompletePublicTable
public import Bandits.Support.PublicGridConcentration

/-!
# Concentration for complete public rows

For a fixed identification array, this module lifts an explicit measurable,
almost-surely bounded row cost to the literal complete-row product. It derives
measurability, bounds, and row independence from the accepted complete-row
projection law, then applies the finite real reward-grid concentration result.
The cost map remains an explicit input: this module does not construct the
true-only reference execution, its row-only reads, or its protocol
measurability. Source: `sources/zip4/manuscript/08_main_theorem.tex:26-65`.
-/

public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.PublicGridConcentration
open Bandits.Support.WholeRowHoeffding

namespace Bandits.Support.CompleteRowConcentration

/-- Lift a row cost to the complete table by evaluating it on the matching
complete row. The identification array is fixed throughout every cost and
integral. -/
@[expose] def liftedCompleteRowCost (p : Parameters) (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ) :
    RealRewardMatrix p → Fin (M p) → CompleteRows p → ℝ :=
  fun r j rows => f id r j (rows j)

/-- The lifted cost is measurable when each fixed-ID row map is measurable. -/
theorem measurable_liftedCompleteRowCost (p : Parameters) (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (h_meas : ∀ r j, Measurable (f id r j)) :
    ∀ r j, Measurable (liftedCompleteRowCost p id f r j) := by
  intro r j
  exact (h_meas r j).comp (measurable_completeRowProjection p j)

/-- A rowwise almost-sure interval bound lifts through the actual complete-row
projection map. -/
theorem ae_mem_Icc_liftedCompleteRowCost (p : Parameters) (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (h_bounds : ∀ r j, ∀ᵐ row ∂completeRowMeasure p,
      f id r j row ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    ∀ r j, ∀ᵐ rows ∂fixedIDCompleteRowsMeasure p id,
      liftedCompleteRowCost p id f r j rows ∈
        Set.Icc (-(p.m : ℝ) * (p.T : ℝ)) (3 * (p.m : ℝ) * (p.T : ℝ)) := by
  intro r j
  change ∀ᵐ rows ∂completeRowsMeasure p,
    f id r j (rows j) ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
      (3 * (p.m : ℝ) * (p.T : ℝ))
  exact (measurePreserving_completeRowProjection p j).quasiMeasurePreserving.ae
    (h_bounds r j)

/-- For each fixed reward matrix, the lifted costs are independent because
the complete-row carrier has its literal finite product law. -/
theorem iIndepFun_liftedCompleteRowCost (p : Parameters) (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (h_meas : ∀ r j, Measurable (f id r j)) :
    ∀ r, ProbabilityTheory.iIndepFun (liftedCompleteRowCost p id f r)
      (fixedIDCompleteRowsMeasure p id) := by
  intro r
  have h := iIndepFun_fixedID_completeRows p id
  have hcomp := h.comp (fun j row => f id r j row) (fun j => h_meas r j)
  change ProbabilityTheory.iIndepFun
    (fun j rows => f id r j (rows j)) (fixedIDCompleteRowsMeasure p id)
  exact hcomp

/-- The simultaneous good event for the lifted complete-row costs, using the
same fixed identification array in the row averages. -/
@[expose] noncomputable def completeRowConcentrationGoodEvent (p : Parameters)
    (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ) :
    Set (CompleteRows p) :=
  rowConcentrationGoodEvent p (fixedIDCompleteRowsMeasure p id)
    (liftedCompleteRowCost p id f)

/-- The complete-row good event is measurable under the fixed-ID row law. -/
theorem measurableSet_completeRowConcentrationGoodEvent (p : Parameters)
    (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (h_meas : ∀ r j, Measurable (f id r j)) :
    MeasurableSet (completeRowConcentrationGoodEvent p id f) := by
  exact measurableSet_rowConcentrationGoodEvent p
    (fixedIDCompleteRowsMeasure p id) (liftedCompleteRowCost p id f)
    (measurable_liftedCompleteRowCost p id f h_meas)

/-- On a fixed complete-row output in the simultaneous event, every real
denominator-grid matrix obeys the source row-average inequality. -/
theorem completeRowConcentrationGoodEvent_bound_at (p : Parameters)
    (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (rows : CompleteRows p)
    (h_good : rows ∈ completeRowConcentrationGoodEvent p id f)
    (r : RealRewardMatrix p) :
    barG (liftedCompleteRowCost p id f r) rows ≤
      muG (fixedIDCompleteRowsMeasure p id) (liftedCompleteRowCost p id f r) +
        2 * rowConcentrationScale p := by
  exact h_good r

/-- The all-grid failure probability is at most `1/(2N)` under the fixed-ID
complete-row measure. The only cost-specific inputs are row measurability and
the rowwise a.e. interval bounds. -/
theorem completeRowConcentrationGoodEvent_failure_prob_le (p : Parameters)
    (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (h_meas : ∀ r j, Measurable (f id r j))
    (h_bounds : ∀ r j, ∀ᵐ row ∂completeRowMeasure p,
      f id r j row ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    (fixedIDCompleteRowsMeasure p id).real
      (completeRowConcentrationGoodEvent p id f)ᶜ ≤ 1 / (2 * (N p : ℝ)) := by
  exact rowConcentrationGoodEvent_failure_prob_le p
    (fixedIDCompleteRowsMeasure p id) (liftedCompleteRowCost p id f)
    (iIndepFun_liftedCompleteRowCost p id f h_meas)
    (measurable_liftedCompleteRowCost p id f h_meas)
    (ae_mem_Icc_liftedCompleteRowCost p id f h_bounds)

/-- The fixed-ID result is also the complete-row product-law result, since the
accepted fixed-ID measure is defined to be exactly `completeRowsMeasure`. -/
theorem completeRowConcentrationGoodEvent_failure_prob_le_completeRowsMeasure
    (p : Parameters) (id : IDArray p)
    (f : IDArray p → RealRewardMatrix p → Fin (M p) → CompleteRow p → ℝ)
    (h_meas : ∀ r j, Measurable (f id r j))
    (h_bounds : ∀ r j, ∀ᵐ row ∂completeRowMeasure p,
      f id r j row ∈ Set.Icc (-(p.m : ℝ) * (p.T : ℝ))
        (3 * (p.m : ℝ) * (p.T : ℝ))) :
    (completeRowsMeasure p).real
      (completeRowConcentrationGoodEvent p id f)ᶜ ≤ 1 / (2 * (N p : ℝ)) := by
  change (fixedIDCompleteRowsMeasure p id).real
    (completeRowConcentrationGoodEvent p id f)ᶜ ≤ 1 / (2 * (N p : ℝ))
  exact completeRowConcentrationGoodEvent_failure_prob_le p id f h_meas h_bounds

end Bandits.Support.CompleteRowConcentration

end
