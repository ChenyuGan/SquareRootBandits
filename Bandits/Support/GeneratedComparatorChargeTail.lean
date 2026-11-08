/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.GeneratedMonitorObstructionTail
public import Bandits.Support.GeneratedComparatorChargeAssembly
public import Bandits.Support.InitializationRowObservables

import Mathlib.MeasureTheory.Measure.Real

/-!
# Strict prelaunch comparator-charge tails

The literal event that some supported comparator exceeds the launch-scale
charge threshold is measurable on the original reference coordinates. The
accepted deterministic assembly places it inside the accepted comparator
monitor deficit, whose single simultaneous tail controls the product-stream
expected charge. Sources: `appendix_b_communication.tex:642-682,753-765`,
`07_public_setup.tex:106-140`, and `08_main_theorem.tex:78-83`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Bandits.Support.GeneratedComparatorChargeTail

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.GeneratedBootstrapBlockFiltrationRepair
open Bandits.Support.GeneratedBootstrapRoundLaw
open Bandits.Support.InitializationRowObservables
open Bandits.Support.ReferenceInitializationRun

abbrev Parameters := ConstructorDimensions.Parameters
abbrev Coordinates (p : Parameters) := GeneratedBootstrapRoundLaw.Coordinates p

section FixedInputs

variable (p : Parameters)
variable (ids : CompletePublicTable.IDArray p)
variable (rewards : Fin p.T → Fin p.K → Fin (D p + 1))
variable (C_star C_h : ℝ)
variable (eta : ReferencePrelaunchFollower.LearningRate)

local notation "x(" e ")" =>
  GeneratedBootstrapBlockFiltrationRepair.referenceInput p ids rewards C_star C_h eta e
local notation "H" =>
  128 * (4 * (BootstrapStartupCostScale.Q C_star C_h p : ℝ) +
    (p.K : ℝ) * (B_boot p : ℝ) +
    (p.m : ℝ) * (p.K : ℝ) * (B_boot p : ℝ) * (4 * (b_N p : ℝ)))

/-- The exact event that one supported comparator has strict-prelaunch charge
above the launch threshold, evaluated at the same reference input. -/
def strictPrelaunchComparatorChargeEvent : Set (Coordinates p) :=
  {e | ∃ S : Finset (Fin p.K),
    S ∈ ProductSetLaw.support p.K p.m ∧
      InitializationRowObservables.comparatorChargeAtBoundary p rewards S
        (ReferenceInitializationRun.output (x(e))) > H}

/-- The reference adapter and fixed-row adapter construct the same actual run
input on the original row/private coordinates. -/
theorem referenceInput_eq_fixedRowInput (row : CompleteRow p)
    (e : InitializationRowObservables.PrivateCoordinates p) :
    x((row, e)) =
      ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e := by
  rfl

/-- Consequently the two adapters expose the same actual terminal boundary. -/
theorem referenceOutput_eq_fixedRowOutput (row : CompleteRow p)
    (e : InitializationRowObservables.PrivateCoordinates p) :
    ReferenceInitializationRun.output (x((row, e))) =
      ReferenceInitializationRun.output
        (ReferenceInitializationIndexMixture.fixedRowInput p ids rewards C_star C_h eta row e) := by
  exact congrArg ReferenceInitializationRun.output
    (referenceInput_eq_fixedRowInput p ids rewards C_star C_h eta row e)

/-- Ambient measurability of the exact finite union over the actual
supported-comparator family. -/
theorem measurableSet_strictPrelaunchComparatorChargeEvent :
    MeasurableSet (strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta) := by
  have houtput : Measurable (fun e : Coordinates p =>
      ReferenceInitializationRun.output (x(e))) := by
    exact (ReferenceInitializationMeasurability.measurable_output
      p C_star C_h eta rewards).comp (measurable_const.prodMk measurable_id)
  have hcharge (S : Finset (Fin p.K)) :
      Measurable (fun e : Coordinates p =>
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e)))) :=
    (InitializationRowObservables.measurable_comparatorChargeAtBoundary p rewards S).comp
      houtput
  have hevent : strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta =
      ⋃ S ∈ ProductSetLaw.support p.K p.m,
        {e : Coordinates p |
          InitializationRowObservables.comparatorChargeAtBoundary p rewards S
            (ReferenceInitializationRun.output (x(e))) > H} := by
    ext e
    simp [strictPrelaunchComparatorChargeEvent]
  rw [hevent]
  exact (ProductSetLaw.support p.K p.m).measurableSet_biUnion fun S hS =>
    measurableSet_lt measurable_const (hcharge S)

/-- Every point of the exact supported-comparator charge event witnesses the
existing comparator monitor deficit on that same reference input. -/
theorem strictPrelaunchComparatorChargeEvent_subset_comparatorMonitorDeficitPullback :
    strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta ⊆
      GeneratedMonitorObstructionTail.comparatorMonitorDeficitPullback
        p ids rewards C_star C_h eta := by
  intro e he
  rcases he with ⟨S, hS, hcharge⟩
  change GeneratedComparatorChargeObstruction.comparatorMonitorDeficit (x(e))
  exact GeneratedComparatorChargeAssembly.comparatorCharge_obstruction_subset (x(e))
    ⟨S, hS, hcharge⟩

/-- The exact simultaneous event inherits both accepted deficit-tail bounds.
No separate union over comparators is taken. -/
theorem strictPrelaunchComparatorChargeEvent_measure_le :
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta) ≤
      2 * (p.K : ℝ) * Real.exp (-(4 * (b_N p : ℝ))) ∧
    (GeneratedBootstrapRoundLaw.originalLaw p).real
        (strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta) ≤
      1 / (N p : ℝ) ^ 2 := by
  have hsub := strictPrelaunchComparatorChargeEvent_subset_comparatorMonitorDeficitPullback
    p ids rewards C_star C_h eta
  have hmono :
      (GeneratedBootstrapRoundLaw.originalLaw p).real
          (strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta) ≤
        (GeneratedBootstrapRoundLaw.originalLaw p).real
          (GeneratedMonitorObstructionTail.comparatorMonitorDeficitPullback
            p ids rewards C_star C_h eta) := by
    exact ENNReal.toReal_mono
      (measure_ne_top (GeneratedBootstrapRoundLaw.originalLaw p)
        (GeneratedMonitorObstructionTail.comparatorMonitorDeficitPullback
          p ids rewards C_star C_h eta))
      (measure_mono hsub)
  have htail := GeneratedMonitorObstructionTail.comparatorMonitorDeficitPullback_measure_le
    p ids rewards C_star C_h eta
  exact ⟨hmono.trans htail.1, hmono.trans htail.2⟩

/-- Expected strict-prelaunch charge for one supported comparator under the
original complete-row/private product law. -/
theorem referenceComparatorCharge_integral_le (S : Finset (Fin p.K))
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    ∫ e : Coordinates p,
      InitializationRowObservables.comparatorChargeAtBoundary p rewards S
        (ReferenceInitializationRun.output (x(e)))
      ∂GeneratedBootstrapRoundLaw.originalLaw p ≤
        H + ((p.m : ℝ) * (p.T : ℝ)) / (N p : ℝ) ^ 2 := by
  classical
  let E := strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta
  let μ := GeneratedBootstrapRoundLaw.originalLaw p
  have hE : MeasurableSet E := by
    exact measurableSet_strictPrelaunchComparatorChargeEvent p ids rewards C_star C_h eta
  have htail := strictPrelaunchComparatorChargeEvent_measure_le p ids rewards C_star C_h eta
  have hcard : S.card = p.m := BootstrapLaunchMonitor.supportedSet_card p hS
  have hchargeMeas : Measurable
      (fun e : Coordinates p =>
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e)))) := by
    exact (InitializationRowObservables.measurable_comparatorChargeAtBoundary
      p rewards S).comp
        ((ReferenceInitializationMeasurability.measurable_output
          p C_star C_h eta rewards).comp (measurable_const.prodMk measurable_id))
  have hchargeInt : Integrable
      (fun e : Coordinates p =>
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e)))) μ := by
    refine Integrable.of_bound hchargeMeas.aestronglyMeasurable
      ((p.m : ℝ) * (p.T : ℝ)) (ae_of_all _ fun e => ?_)
    have hb := InitializationRowObservables.comparatorChargeAtBoundary_bounds
      p rewards S hcard (ReferenceInitializationRun.output (x(e)))
    have hM : 0 ≤ (p.m : ℝ) * (p.T : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hb.1, hM], hb.2⟩
  have hindicatorInt : Integrable
      (fun e : Coordinates p => E.indicator (fun _ => (1 : ℝ)) e) μ := by
    refine Integrable.of_bound (measurable_const.indicator hE).aestronglyMeasurable 1
      (ae_of_all _ fun e => ?_)
    by_cases he : e ∈ E <;> simp [he]
  have hH : 0 ≤ H := by positivity
  have hmajorantInt : Integrable
      (fun e : Coordinates p =>
        H + ((p.m : ℝ) * (p.T : ℝ)) * E.indicator (fun _ => (1 : ℝ)) e) μ :=
    (integrable_const H).add (hindicatorInt.const_mul ((p.m : ℝ) * (p.T : ℝ)))
  have hpoint : ∀ e : Coordinates p,
      InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e))) ≤
        H + ((p.m : ℝ) * (p.T : ℝ)) * E.indicator (fun _ => (1 : ℝ)) e := by
    intro e
    have hbounds := InitializationRowObservables.comparatorChargeAtBoundary_bounds
      p rewards S hcard (ReferenceInitializationRun.output (x(e)))
    by_cases he : e ∈ E
    · simp only [Set.indicator_of_mem he, mul_one]
      linarith [hbounds.2]
    · have hleH :
          InitializationRowObservables.comparatorChargeAtBoundary p rewards S
              (ReferenceInitializationRun.output (x(e))) ≤ H := by
        apply le_of_not_gt
        intro hlarge
        apply he
        exact ⟨S, hS, hlarge⟩
      simpa only [Set.indicator_of_notMem he, mul_zero, add_zero] using hleH
  have hindicatorIntegral :
      ∫ e : Coordinates p, E.indicator (fun _ => (1 : ℝ)) e ∂μ = μ.real E :=
    integral_indicator_one hE
  have hmajorantIntegral :
      ∫ e : Coordinates p,
        H + ((p.m : ℝ) * (p.T : ℝ)) * E.indicator (fun _ => (1 : ℝ)) e ∂μ =
          H + ((p.m : ℝ) * (p.T : ℝ)) * μ.real E := by
    calc
      _ = (∫ _ : Coordinates p, H ∂μ) +
          ∫ e : Coordinates p,
            ((p.m : ℝ) * (p.T : ℝ)) * E.indicator (fun _ => (1 : ℝ)) e ∂μ :=
              integral_add (integrable_const H)
                (hindicatorInt.const_mul ((p.m : ℝ) * (p.T : ℝ)))
      _ = H + ((p.m : ℝ) * (p.T : ℝ)) * μ.real E := by
              have hconst : (∫ _ : Coordinates p, H ∂μ) = H := by simp
              rw [hconst, integral_const_mul, hindicatorIntegral]
  have hscale : 0 ≤ (p.m : ℝ) * (p.T : ℝ) :=
    mul_nonneg (Nat.cast_nonneg p.m) (Nat.cast_nonneg p.T)
  have hweighted :
      ((p.m : ℝ) * (p.T : ℝ)) * μ.real E ≤
        ((p.m : ℝ) * (p.T : ℝ)) * (1 / (N p : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left htail.2 hscale
  calc
    ∫ e : Coordinates p,
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e))) ∂μ
        ≤ ∫ e : Coordinates p,
            H + ((p.m : ℝ) * (p.T : ℝ)) * E.indicator (fun _ => (1 : ℝ)) e ∂μ :=
              integral_mono hchargeInt hmajorantInt hpoint
    _ = H + ((p.m : ℝ) * (p.T : ℝ)) * μ.real E := hmajorantIntegral
    _ ≤ H + ((p.m : ℝ) * (p.T : ℝ)) * (1 / (N p : ℝ) ^ 2) :=
          calc
            _ = ((p.m : ℝ) * (p.T : ℝ)) * μ.real E + H := by ring
            _ ≤ ((p.m : ℝ) * (p.T : ℝ)) * (1 / (N p : ℝ) ^ 2) + H :=
              add_le_add_left hweighted H
            _ = _ := by ring
    _ = H + ((p.m : ℝ) * (p.T : ℝ)) / (N p : ℝ) ^ 2 := by
          simp [div_eq_mul_inv]

/-- The complete-row integral of the fixed-row comparator charge obeys the
same bound. The product integrand is identified pointwise with the actual
initialization observable before applying its accepted row-private Fubini
identity. -/
theorem c_S_integral_le (S : Finset (Fin p.K))
    (hS : S ∈ ProductSetLaw.support p.K p.m) :
    ∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
      ∂CompletePublicTable.completeRowMeasure p ≤
        H + ((p.m : ℝ) * (p.T : ℝ)) / (N p : ℝ) ^ 2 := by
  have hcard : S.card = p.m := BootstrapLaunchMonitor.supportedSet_card p hS
  have hcharge (e : Coordinates p) :
      InitializationRowObservables.initializationComparatorCharge
          p ids rewards C_star C_h eta S e.1 e.2 =
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e))) := by
    rw [referenceOutput_eq_fixedRowOutput p ids rewards C_star C_h eta e.1 e.2]
    exact InitializationRowObservables.initializationComparatorCharge_eq_comparatorChargeAtBoundary
      p ids rewards C_star C_h eta S e.1 e.2
  have hproduct :
      (∫ e : Coordinates p,
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e)))
        ∂GeneratedBootstrapRoundLaw.originalLaw p) =
      ∫ e : Coordinates p,
        InitializationRowObservables.initializationComparatorCharge
          p ids rewards C_star C_h eta S e.1 e.2
        ∂GeneratedBootstrapRoundLaw.originalLaw p := by
    apply integral_congr_ae
    filter_upwards with e
    exact (hcharge e).symm
  have hrow :
      (∫ e : Coordinates p,
        InitializationRowObservables.initializationComparatorCharge
          p ids rewards C_star C_h eta S e.1 e.2
        ∂GeneratedBootstrapRoundLaw.originalLaw p) =
      ∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
        ∂CompletePublicTable.completeRowMeasure p :=
    InitializationRowObservables.integral_rowPrivate_comparatorCharge
      p ids rewards C_star C_h eta S hcard
  calc
    ∫ row, InitializationRowObservables.c_S p ids rewards C_star C_h eta S row
        ∂CompletePublicTable.completeRowMeasure p =
      ∫ e : Coordinates p,
        InitializationRowObservables.initializationComparatorCharge
          p ids rewards C_star C_h eta S e.1 e.2
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hrow.symm
    _ = ∫ e : Coordinates p,
        InitializationRowObservables.comparatorChargeAtBoundary p rewards S
          (ReferenceInitializationRun.output (x(e)))
        ∂GeneratedBootstrapRoundLaw.originalLaw p := hproduct.symm
    _ ≤ H + ((p.m : ℝ) * (p.T : ℝ)) / (N p : ℝ) ^ 2 :=
      referenceComparatorCharge_integral_le p ids rewards C_star C_h eta S hS

end FixedInputs

end Bandits.Support.GeneratedComparatorChargeTail

end
