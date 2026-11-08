/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.InitializationRowObservables
public import Bandits.Support.GeneratedInitializationFailureTail
public import Bandits.Support.GeneratedComparatorChargeTail

import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual selected-family initialization-cost mean

This module combines the accepted complete-row mean bounds for the literal
prelaunch comparator charge and operational initialization-failure flag. It
then identifies their combined row mean with the expectation over the original
selected-index private coordinates and a newly sampled complete-row family.

Sources: sources/zip4/manuscript/07_public_setup.tex:144-164,
sources/zip4/manuscript/appendix_b_communication.tex:753-798, and
sources/zip4/manuscript/08_main_theorem.tex:26-64,78-83.
-/

public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.GeneratedInitializationCostMean

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.ProductSetLaw
open Bandits.Support.BootstrapLaunchMonitor
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapDimensions

abbrev Parameters := ConstructorDimensions.Parameters

section FixedInputs

variable (p : Parameters)
variable (ids : CompletePublicTable.IDArray p)
variable (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
variable (C_star C_h : ℝ)
variable (eta : ReferencePrelaunchFollower.LearningRate)
variable (S : Finset (Fin p.K))

local notation "H" =>
  128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
    (p.K : ℝ) * (B_boot p : ℝ) +
    (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))

private theorem support_card (hS : S ∈ ProductSetLaw.support p.K p.m) :
    S.card = p.m :=
  BootstrapLaunchMonitor.supportedSet_card p hS

/-- The concrete combined initialization row cost is integrable for every
supported comparator. -/
theorem integrable_g_init (hS : S ∈ ProductSetLaw.support p.K p.m) :
    Integrable (InitializationRowObservables.g_init p ids rewards C_star C_h eta S)
      (CompletePublicTable.completeRowMeasure p) :=
  InitializationRowObservables.integrable_g_init p ids rewards C_star C_h eta S
    (support_card p S hS)

/-- The complete-row expectation of the combined initialization cost is
nonnegative. -/
theorem g_init_integral_nonneg
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    0 ≤ ∫ row, InitializationRowObservables.g_init p ids rewards C_star C_h eta S row
      ∂CompletePublicTable.completeRowMeasure p := by
  apply integral_nonneg_of_ae
  filter_upwards with row
  exact (InitializationRowObservables.g_init_bounds p ids rewards C_star C_h eta S
    (support_card p S hS) row).1

/-- The actual selected-family cost is measurable on the original extended
private-coordinate space for each fixed family of complete rows. -/
theorem measurable_actual_g_init_private
    (rows : CompletePublicTable.CompleteRows p) :
    Measurable
      (InitializationRowObservables.actualGInit p ids rewards C_star C_h eta S rows) :=
  InitializationRowObservables.measurable_actualGInit p ids rewards C_star C_h eta S rows

/-- The actual selected-family private integrand is integrable for every fixed
family of complete rows, by its accepted pointwise bound. -/
theorem integrable_actual_g_init_private
    (hS : S ∈ ProductSetLaw.support p.K p.m)
    (rows : CompletePublicTable.CompleteRows p) :
    Integrable
      (InitializationRowObservables.actualGInit p ids rewards C_star C_h eta S rows)
      (BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have hm := measurable_actual_g_init_private p ids rewards C_star C_h eta S rows
  have hbound : 0 ≤ 3 * ((p.m : ℝ) * (p.T : ℝ)) := by positivity
  apply Integrable.of_bound hm.aestronglyMeasurable
    (3 * ((p.m : ℝ) * (p.T : ℝ)))
    (ae_of_all _ fun rho => ?_)
  have hrange := InitializationRowObservables.actualGInit_bounds
    p ids rewards C_star C_h eta S (support_card p S hS) rows rho
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [hrange.1, hbound], hrange.2⟩

private theorem actual_private_integral_eq_average
    (hS : S ∈ ProductSetLaw.support p.K p.m)
    (rows : CompletePublicTable.CompleteRows p) :
    (∫ rho, InitializationRowObservables.actualGInit
      p ids rewards C_star C_h eta S rows rho
      ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j) :=
  InitializationRowObservables.actual_g_init_integral_eq_average p ids rewards C_star C_h eta S
    (support_card p S hS) rows

/-- The actual private expectation is measurable as a function of the newly
sampled complete-row family. The finite average comes from the original
scalar-selected index identity. -/
theorem measurable_actual_g_init_private_expectation
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    Measurable (fun rows : CompletePublicTable.CompleteRows p =>
      ∫ rho, InitializationRowObservables.actualGInit
        p ids rewards C_star C_h eta S rows rho
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) := by
  have hterm (j : Fin (ConstructorDimensions.M p)) :
      Measurable (fun rows : CompletePublicTable.CompleteRows p =>
        InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j)) :=
    (InitializationRowObservables.measurable_g_init p ids rewards C_star C_h eta S).comp
      (CompletePublicTable.measurable_completeRowProjection p j)
  have hsum : Measurable (fun rows : CompletePublicTable.CompleteRows p =>
      ∑ j : Fin (ConstructorDimensions.M p),
        InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j)) := by
    apply Finset.measurable_sum Finset.univ
    intro j hj
    exact hterm j
  have havg : Measurable (fun rows : CompletePublicTable.CompleteRows p =>
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j)) :=
    measurable_const.mul hsum
  have heq :
      (fun rows : CompletePublicTable.CompleteRows p =>
        ∫ rho, InitializationRowObservables.actualGInit
          p ids rewards C_star C_h eta S rows rho
          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      (fun rows : CompletePublicTable.CompleteRows p =>
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j)) := by
    funext rows
    exact actual_private_integral_eq_average p ids rewards C_star C_h eta S hS rows
  rw [heq]
  exact havg

/-- The actual private expectation is integrable over newly sampled complete
rows. Each term of its original-index finite average is integrable by the
complete-row projection law. -/
theorem integrable_actual_g_init_private_expectation
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    Integrable
      (fun rows : CompletePublicTable.CompleteRows p =>
        ∫ rho, InitializationRowObservables.actualGInit
          p ids rewards C_star C_h eta S rows rho
          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      (CompletePublicTable.completeRowsMeasure p) := by
  have hcard : S.card = p.m := support_card p S hS
  have hterm (j : Fin (ConstructorDimensions.M p)) :
      Integrable (fun rows : CompletePublicTable.CompleteRows p =>
        InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j))
      (CompletePublicTable.completeRowsMeasure p) := by
    exact (CompletePublicTable.measurePreserving_completeRowProjection p j).integrable_comp_of_integrable
        (InitializationRowObservables.integrable_g_init p ids rewards C_star C_h eta S hcard)
  have hsum : Integrable (fun rows : CompletePublicTable.CompleteRows p =>
      ∑ j : Fin (ConstructorDimensions.M p),
        InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j))
      (CompletePublicTable.completeRowsMeasure p) := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hterm j
  have havg := hsum.const_mul (1 / (ConstructorDimensions.M p : ℝ))
  have heq :
      (fun rows : CompletePublicTable.CompleteRows p =>
        ∫ rho, InitializationRowObservables.actualGInit
          p ids rewards C_star C_h eta S rows rho
          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
      (fun rows : CompletePublicTable.CompleteRows p =>
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            InitializationRowObservables.g_init p ids rewards C_star C_h eta S (rows j)) := by
    funext rows
    exact actual_private_integral_eq_average p ids rewards C_star C_h eta S hS rows
  rw [heq]
  exact havg

/-- The selected-family actual expectation equals the complete-row integral of
the existing literal row cost. This uses the accepted original-J private
average, then integrates each finite-average summand through its own complete
row projection law. -/
theorem selected_family_actual_mean_eq_row_mean
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    (∫ rows, (∫ rho, InitializationRowObservables.actualGInit
      p ids rewards C_star C_h eta S rows rho
      ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      ∂CompletePublicTable.completeRowsMeasure p) =
      ∫ row, InitializationRowObservables.g_init p ids rewards C_star C_h eta S row
        ∂CompletePublicTable.completeRowMeasure p := by
  let μrows := CompletePublicTable.completeRowsMeasure p
  let μrow := CompletePublicTable.completeRowMeasure p
  let g := InitializationRowObservables.g_init p ids rewards C_star C_h eta S
  have hcard : S.card = p.m := support_card p S hS
  have htermInt (j : Fin (ConstructorDimensions.M p)) :
      Integrable (fun rows : CompletePublicTable.CompleteRows p => g (rows j)) μrows := by
    exact (CompletePublicTable.measurePreserving_completeRowProjection p j).integrable_comp_of_integrable
        (InitializationRowObservables.integrable_g_init p ids rewards C_star C_h eta S hcard)
  have htermMeas : Measurable g :=
    InitializationRowObservables.measurable_g_init p ids rewards C_star C_h eta S
  have hproj (j : Fin (ConstructorDimensions.M p)) :
      (∫ rows, g (rows j) ∂μrows) = (∫ row, g row ∂μrow) := by
    let mp := CompletePublicTable.measurePreserving_completeRowProjection p j
    have hmap : μrows.map (fun rows : CompletePublicTable.CompleteRows p => rows j) = μrow :=
      mp.map_eq
    have hgmap : AEStronglyMeasurable g
        (μrows.map (fun rows : CompletePublicTable.CompleteRows p => rows j)) := by
      rw [hmap]
      exact htermMeas.aestronglyMeasurable
    calc
      (∫ rows, g (rows j) ∂μrows) =
          ∫ row, g row ∂μrows.map (fun rows : CompletePublicTable.CompleteRows p => rows j) := by
        symm
        exact integral_map
          (CompletePublicTable.measurable_completeRowProjection p j).aemeasurable hgmap
      _ = ∫ row, g row ∂μrow := by rw [hmap]
  have htermInt' : ∀ j ∈ (Finset.univ : Finset (Fin (ConstructorDimensions.M p))),
      Integrable (fun rows : CompletePublicTable.CompleteRows p => g (rows j)) μrows := by
    intro j hj
    exact htermInt j
  have haverage_integral :
      (∫ rows, (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p), g (rows j) ∂μrows) =
      ∫ row, g row ∂μrow := by
    calc
      _ = (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p), ∫ rows, g (rows j) ∂μrows := by
        rw [integral_const_mul, integral_finsetSum Finset.univ htermInt']
      _ = (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p), ∫ row, g row ∂μrow := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        exact hproj j
      _ = ∫ row, g row ∂μrow := by
        have hMpos : 0 < (ConstructorDimensions.M p : ℝ) :=
          Nat.cast_pos.mpr (ConstructorDimensions.M_pos p)
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp [ne_of_gt hMpos]
  have hpoint : ∀ rows : CompletePublicTable.CompleteRows p,
      (∫ rho, InitializationRowObservables.actualGInit
        p ids rewards C_star C_h eta S rows rho
        ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p) =
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p), g (rows j) := by
    intro rows
    exact actual_private_integral_eq_average p ids rewards C_star C_h eta S hS rows
  calc
    _ = ∫ rows, (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p), g (rows j) ∂μrows := by
      apply integral_congr_ae
      exact ae_of_all _ hpoint
    _ = ∫ row, g row ∂μrow := haverage_integral

/-- The complete-row expectation of the actual combined startup cost is
bounded by the accepted comparator threshold plus the exact residual
7*m*T/(2*N^2). The only numerical premises are the accepted identification
event and the explicit shared lower bounds on C_h and C_star. -/
theorem g_init_integral_le
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hCstar : (2 : ℝ) ^ 20 ≤ C_star)
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    (∫ row, InitializationRowObservables.g_init p ids rewards C_star C_h eta S row
      ∂CompletePublicTable.completeRowMeasure p) ≤
      H + 7 * ((p.m : ℝ) * (p.T : ℝ)) / (2 * (N p : ℝ) ^ 2) := by
  have hcard : S.card = p.m := support_card p S hS
  have hcInt := InitializationRowObservables.integrable_c_S
    p ids rewards C_star C_h eta S hcard
  have heInt := InitializationRowObservables.integrable_e_initFlag
    p ids rewards C_star C_h eta
  have hc := GeneratedComparatorChargeTail.c_S_integral_le
    p ids rewards C_star C_h eta S hS
  have he := GeneratedInitializationFailureTail.e_initFlag_integral_bounds
    p ids rewards C_star C_h eta hgood hC_h hCstar
  let k : ℝ := 2 * ((p.m : ℝ) * (p.T : ℝ))
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hsplit :
      (∫ row, InitializationRowObservables.g_init p ids rewards C_star C_h eta S row
        ∂CompletePublicTable.completeRowMeasure p) =
      (∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
        ∂CompletePublicTable.completeRowMeasure p) +
      k * (∫ row, InitializationRowObservables.e_initFlag
        p ids rewards C_star C_h eta row ∂CompletePublicTable.completeRowMeasure p) := by
    calc
      _ = ∫ row,
          (InitializationRowObservables.c_S p ids rewards C_star C_h eta S row +
            k * InitializationRowObservables.e_initFlag p ids rewards C_star C_h eta row)
          ∂CompletePublicTable.completeRowMeasure p := by
        apply integral_congr_ae
        exact ae_of_all _ fun row => by
          rw [InitializationRowObservables.g_init_eq_components p ids rewards
            C_star C_h eta S row]
      _ = (∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
            ∂CompletePublicTable.completeRowMeasure p) +
          ∫ row, k * InitializationRowObservables.e_initFlag
            p ids rewards C_star C_h eta row ∂CompletePublicTable.completeRowMeasure p :=
          integral_add hcInt (heInt.const_mul k)
      _ = (∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
            ∂CompletePublicTable.completeRowMeasure p) +
          k * (∫ row, InitializationRowObservables.e_initFlag
            p ids rewards C_star C_h eta row ∂CompletePublicTable.completeRowMeasure p) := by
          rw [integral_const_mul]
  have hweighted :
      k * (∫ row, InitializationRowObservables.e_initFlag
        p ids rewards C_star C_h eta row ∂CompletePublicTable.completeRowMeasure p) ≤
      k * (5 / (4 * (N p : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left he.1 hk
  calc
    _ = (∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
          ∂CompletePublicTable.completeRowMeasure p) +
        k * (∫ row, InitializationRowObservables.e_initFlag
          p ids rewards C_star C_h eta row ∂CompletePublicTable.completeRowMeasure p) := hsplit
    _ ≤ (H + ((p.m : ℝ) * (p.T : ℝ)) / (N p : ℝ) ^ 2) +
        k * (5 / (4 * (N p : ℝ) ^ 2)) := add_le_add hc hweighted
    _ = H + 7 * ((p.m : ℝ) * (p.T : ℝ)) / (2 * (N p : ℝ) ^ 2) := by
      dsimp [k]
      field_simp [ne_of_gt (Nat.cast_pos.mpr (ConstructorDimensions.N_pos p))]
      ; ring

/-- The fixed-ID, fixed-reward actual expectation over newly sampled complete
rows and the original private coordinates has the same startup-cost bound. -/
theorem selected_family_actual_mean_le
    (hgood : ids ∈ IdentificationGoodEvent.identificationGoodEvent p)
    (hC_h : (4096 : ℝ) ≤ C_h)
    (hCstar : (2 : ℝ) ^ 20 ≤ C_star)
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    (∫ rows, (∫ rho, InitializationRowObservables.actualGInit
      p ids rewards C_star C_h eta S rows rho
      ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      ∂CompletePublicTable.completeRowsMeasure p) ≤
      H + 7 * ((p.m : ℝ) * (p.T : ℝ)) / (2 * (N p : ℝ) ^ 2) := by
  rw [selected_family_actual_mean_eq_row_mean p ids rewards C_star C_h eta S hS]
  exact g_init_integral_le p ids rewards C_star C_h eta S hgood hC_h hCstar hS

/-- The selected-family actual expectation is integrable over its complete-row
family, with the original private law inside the expectation. -/
theorem integrable_selected_family_actual_mean_function
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    Integrable
      (fun rows : CompletePublicTable.CompleteRows p =>
        ∫ rho, InitializationRowObservables.actualGInit
          p ids rewards C_star C_h eta S rows rho
          ∂BootstrapPrivateRoundStreams.extendedPrivateLaw p)
      (CompletePublicTable.completeRowsMeasure p) :=
  integrable_actual_g_init_private_expectation p ids rewards C_star C_h eta S hS

end FixedInputs

end Bandits.Support.GeneratedInitializationCostMean

end
