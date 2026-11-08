/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope
public import Bandits.Support.ReferenceFirstLiveEmptyPendingExponentialIncrement

import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Actual empty-pending conditional exponential queue step

Sources: sources/zip4/manuscript/04_slow_fast_learner.tex:245-288,
sources/zip4/manuscript/06_interruptions.tex:425-426, and
sources/zip4/manuscript/07_public_setup.tex:127-164.

This module proves one conditional queue step on the actual empty-pending
carrier, using its unchanged unnormalized measure and its actual prefix field.
The inclusive current update is retained, including zero-arrival service and
the update that first overflows. The result is a cell for a later
original-source/calendar iteration; it does not identify the field with a
manuscript history or close a manuscript queue or regret assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingConditionalExponentialQueue

abbrev Parameters := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.Parameters
abbrev RateInput := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.RateInput
abbrev RewardTable := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.RewardTable
abbrev TimeControl := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Ze" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "muE" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
  rate rewards C_star C_h q t s hs control0
local notation "Fempty" => ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
  rate rewards C_star C_h q t s hs control0
local notation "G" => ReferenceFirstLiveEmptyPendingAcceptedMoments.G
  rate rewards C_star C_h q t s hs control0
local notation "acceptedA" => ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
  rate rewards C_star C_h q t s hs control0
local notation "bBefore" => ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore
  rate rewards C_star C_h q t s hs control0
local notation "bAfter" => ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogAfter
  rate rewards C_star C_h q t s hs control0
local notation "retainedIncrement" =>
  ReferenceFirstLiveEmptyPendingExponentialIncrement.retainedIncrement
    rate rewards C_star C_h q t s hs control0
local notation "expRetainedIncrement" =>
  ReferenceFirstLiveEmptyPendingExponentialIncrement.expRetainedIncrement
    rate rewards C_star C_h q t s hs control0
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Bcap" => 1 / (32 * rate.eta.val)

/-- Exponential of the actual strict-past normalized backlog. -/
def expBacklogBefore (j : Fin p.K) (z : Ze) : ℝ :=
  Real.exp (beta * bBefore j z)

/-- Exponential of the actual inclusive successor backlog. -/
def expBacklogAfter (j : Fin p.K) (z : Ze) : ℝ :=
  Real.exp (beta * bAfter j z)

private theorem beta_pos : 0 < beta :=
  CanonicalRecordingRates.beta_pos p rate.eta.property

private theorem beta_mul_acceptedA_le_one (j : Fin p.K) (z : Ze) :
    beta * acceptedA j z ≤ 1 := by
  have hbeta := beta_pos rate
  have hA := ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_pointwise_bounds
    rate rewards C_star C_h q t s hs control0 j z
  have hmul : acceptedA j z * beta ≤ 1 := (le_div_iff₀ hbeta).mp hA.2
  simpa [mul_comm] using hmul

/-- The actual empty-pending queue update is the reflected update by X's
literal retained increment, including the inclusive first-overflow cell. -/
theorem backlogAfter_eq_max_add_retainedIncrement (j : Fin p.K) (z : Ze) :
    bAfter j z = max (bBefore j z + retainedIncrement j z) 0 := by
  by_cases hz : z ∈ G
  · calc
      bAfter j z = max (bBefore j z + acceptedA j z - 4) 0 :=
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogAfter_eq_max_on_G
          rate rewards C_star C_h q t s hs control0 j z hz
      _ = max (bBefore j z + retainedIncrement j z) 0 := by
        rw [ReferenceFirstLiveEmptyPendingExponentialIncrement.retainedIncrement_eq_acceptedA_sub_four_of_mem_G
          rate rewards C_star C_h q t s hs control0 j z hz]
        congr 1
        ring
  · calc
      bAfter j z = bBefore j z :=
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.stopped_queue_noop_off_G
          rate rewards C_star C_h q t s hs control0 j z hz
      _ = max (bBefore j z + retainedIncrement j z) 0 := by
        rw [ReferenceFirstLiveEmptyPendingExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
          rate rewards C_star C_h q t s hs control0 j z hz]
        rw [add_zero]
        exact (max_eq_left
          (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_nonneg
            rate rewards C_star C_h q t s hs control0 j z)).symm

/-- Reflected queue exponentials are bounded by one plus the product of the
strict-past exponential and X's retained-increment exponential. -/
theorem expBacklogAfter_le_one_add_product (j : Fin p.K) (z : Ze) :
    expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ≤
      1 + expBacklogBefore rate rewards C_star C_h q t s hs control0 j z *
        expRetainedIncrement j z := by
  rw [expBacklogAfter, backlogAfter_eq_max_add_retainedIncrement
    rate rewards C_star C_h q t s hs control0 j z]
  simpa [expBacklogBefore,
    ReferenceFirstLiveEmptyPendingExponentialIncrement.expRetainedIncrement] using
      (CanonicalQueueProcess.exp_mul_max_le (bBefore j z) (retainedIncrement j z) beta)

/-- The adapted strict-past exponential is measurable on the actual
empty-pending prefix field. -/
theorem measurable_expBacklogBefore_prefix (j : Fin p.K) :
    Measurable[Fempty]
      (fun z : Ze => expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) := by
  have hbefore := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_backlogBefore
    rate rewards C_star C_h q t s hs control0 j
  have hscaled : Measurable[Fempty] (fun z : Ze => beta * bBefore j z) :=
    (measurable_const : Measurable[Fempty] (fun _ : Ze => beta)).mul hbefore
  simpa [expBacklogBefore] using hscaled.exp

/-- Ambient Borel measurability of the strict-past exponential. -/
theorem measurable_expBacklogBefore (j : Fin p.K) :
    Measurable (fun z : Ze =>
      expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) := by
  exact (measurable_expBacklogBefore_prefix rate rewards C_star C_h q t s hs control0 j).mono
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) le_rfl

/-- Ambient Borel measurability of the inclusive successor exponential. -/
theorem measurable_expBacklogAfter (j : Fin p.K) :
    Measurable (fun z : Ze =>
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) := by
  have hafter := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_backlogAfter
    rate rewards C_star C_h q t s hs control0 j
  have hscaled : Measurable (fun z : Ze => beta * bAfter j z) :=
    (measurable_const : Measurable (fun _ : Ze => beta)).mul hafter
  simpa [expBacklogAfter] using hscaled.exp

/-- The strict-past exponential is nonnegative and has a uniform finite cap
from the actual queue-energy envelope. -/
theorem expBacklogBefore_bounds (j : Fin p.K) (z : Ze) :
    0 ≤ expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∧
      expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ≤
        Real.exp (beta * (2 * Bcap)) := by
  constructor
  · exact Real.exp_nonneg _
  · exact Real.exp_le_exp_of_le
      (mul_le_mul_of_nonneg_left
        (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogBefore_le_two_Bcap
          rate rewards C_star C_h q t s hs control0 j z)
        (le_of_lt (beta_pos rate)))

/-- The inclusive successor exponential has the same uniform finite cap,
including the update which first overflows. -/
theorem expBacklogAfter_bounds (j : Fin p.K) (z : Ze) :
    0 ≤ expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ∧
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ≤
        Real.exp (beta * (2 * Bcap)) := by
  constructor
  · exact Real.exp_nonneg _
  · exact Real.exp_le_exp_of_le
      (mul_le_mul_of_nonneg_left
        (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.backlogAfter_le_two_Bcap
          rate rewards C_star C_h q t s hs control0 j z)
        (le_of_lt (beta_pos rate)))

/-- X's retained-increment exponential is pointwise bounded by exp 1; the
bound uses its actual accepted-arrival cap and zero off the strict-past set. -/
theorem expRetainedIncrement_le_exp_one (j : Fin p.K) (z : Ze) :
    expRetainedIncrement j z ≤ Real.exp 1 := by
  change Real.exp (beta * retainedIncrement j z) ≤ Real.exp 1
  have hbeta := beta_pos rate
  have hmul := beta_mul_acceptedA_le_one rate rewards C_star C_h q t s hs control0 j z
  by_cases hz : z ∈ G
  · rw [ReferenceFirstLiveEmptyPendingExponentialIncrement.retainedIncrement_eq_acceptedA_sub_four_of_mem_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    apply Real.exp_le_exp_of_le
    calc
      beta * (acceptedA j z - 4) = beta * acceptedA j z - 4 * beta := by ring
      _ ≤ beta * acceptedA j z := by nlinarith [hbeta]
      _ ≤ 1 := hmul
  · rw [ReferenceFirstLiveEmptyPendingExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    exact Real.exp_le_exp_of_le (by norm_num)

private theorem integrable_of_norm_le_uniform {f : Ze → ℝ} {C : ℝ}
    (hf : Measurable f) (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f muE := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  have habs : |C| = C := abs_of_nonneg hC
  simpa only [Real.norm_eq_abs, habs] using hbound z

/-- Integrability of the strict-past exponential on the same finite,
unnormalized empty-pending source measure. -/
theorem integrable_expBacklogBefore (j : Fin p.K) :
    Integrable (fun z : Ze =>
      expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) muE := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp (beta * (2 * Bcap)))
    (measurable_expBacklogBefore rate rewards C_star C_h q t s hs control0 j)
    (by positivity [rate.eta.property])
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (expBacklogBefore_bounds rate rewards C_star C_h q t s hs control0 j z).1]
  exact (expBacklogBefore_bounds rate rewards C_star C_h q t s hs control0 j z).2

/-- Integrability of the inclusive successor exponential on the same finite,
unnormalized empty-pending source measure. -/
theorem integrable_expBacklogAfter (j : Fin p.K) :
    Integrable (fun z : Ze =>
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) muE := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp (beta * (2 * Bcap)))
    (measurable_expBacklogAfter rate rewards C_star C_h q t s hs control0 j)
    (by positivity [rate.eta.property])
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (expBacklogAfter_bounds rate rewards C_star C_h q t s hs control0 j z).1]
  exact (expBacklogAfter_bounds rate rewards C_star C_h q t s hs control0 j z).2

/-- The before-exponential times X's retained-increment exponential is
integrable, discharging conditional pull-out from the actual uniform bounds. -/
theorem integrable_expBacklogBefore_mul_expRetainedIncrement (j : Fin p.K) :
    Integrable (fun z : Ze =>
      expBacklogBefore rate rewards C_star C_h q t s hs control0 j z *
        expRetainedIncrement j z) muE := by
  have hbeforeMeas := measurable_expBacklogBefore rate rewards C_star C_h q t s hs control0 j
  have hincrementMeas :=
    ReferenceFirstLiveEmptyPendingExponentialIncrement.measurable_expRetainedIncrement
      rate rewards C_star C_h q t s hs control0 j
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp (beta * (2 * Bcap)) * Real.exp 1)
    (hbeforeMeas.mul hincrementMeas) (by positivity [rate.eta.property])
  intro z
  have hbefore :=
    (expBacklogBefore_bounds rate rewards C_star C_h q t s hs control0 j z).2
  have hincrement := expRetainedIncrement_le_exp_one
    rate rewards C_star C_h q t s hs control0 j z
  change ‖Real.exp (beta * bBefore j z) *
      Real.exp (beta * retainedIncrement j z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
  exact mul_le_mul hbefore hincrement (Real.exp_nonneg _) (Real.exp_nonneg _)

/-- Conditional exponential queue recurrence on the original empty-pending
carrier, with the exact Fempty and muE used by X. -/
theorem expBacklogAfter_condExp_step (j : Fin p.K) :
    muE[(fun z : Ze =>
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) | Fempty] ≤ᵐ[muE]
      (fun z : Ze => 1 +
        expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) := by
  let before : Ze → ℝ := expBacklogBefore rate rewards C_star C_h q t s hs control0 j
  let increment : Ze → ℝ := expRetainedIncrement j
  let after : Ze → ℝ := expBacklogAfter rate rewards C_star C_h q t s hs control0 j
  let product : Ze → ℝ := fun z => before z * increment z
  let split : Ze → ℝ := fun z => 1 + product z
  have hfieldle := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
    rate rewards C_star C_h q t s hs control0
  have hbeforeMeas := measurable_expBacklogBefore_prefix
    rate rewards C_star C_h q t s hs control0 j
  have hbeforeStrong : StronglyMeasurable[Fempty] before := by
    simpa [before] using hbeforeMeas.stronglyMeasurable
  have hbeforeInt := integrable_expBacklogBefore
    rate rewards C_star C_h q t s hs control0 j
  have hincrementInt :=
    ReferenceFirstLiveEmptyPendingExponentialIncrement.integrable_expRetainedIncrement
      rate rewards C_star C_h q t s hs control0 j
  have hproductInt := integrable_expBacklogBefore_mul_expRetainedIncrement
    rate rewards C_star C_h q t s hs control0 j
  have hsplitInt : Integrable split muE := by
    have hproduct : Integrable product muE := by
      simpa [product, before, increment] using hproductInt
    simpa [split] using (integrable_const (1 : ℝ)).add hproduct
  have hafterInt : Integrable after muE := by
    simpa [after] using integrable_expBacklogAfter
      rate rewards C_star C_h q t s hs control0 j
  have hpointwise : ∀ z : Ze, after z ≤ split z := by
    intro z
    simpa [after, split, product, before, increment] using
      expBacklogAfter_le_one_add_product rate rewards C_star C_h q t s hs control0 j z
  have hmono := condExp_mono (m := Fempty) hafterInt hsplitInt
    (Filter.Eventually.of_forall hpointwise)
  have hadd := condExp_add (integrable_const (1 : ℝ)) hproductInt Fempty
  have hsplitEq : split =
      (fun _ : Ze => (1 : ℝ)) + (fun z : Ze => before z * increment z) := by
    funext z
    rfl
  have hadd' := (condExp_congr_ae
    (Filter.Eventually.of_forall fun z => congrFun hsplitEq z)).trans hadd
  have hconst := condExp_const (μ := muE) hfieldle (1 : ℝ)
  have hpull := condExp_mul_of_stronglyMeasurable_left
    hbeforeStrong hproductInt hincrementInt
  have hsplitCE : muE[split | Fempty] =ᵐ[muE]
      (fun z : Ze => 1 + before z * muE[increment | Fempty] z) := by
    filter_upwards [hadd', hpull] with z haddZ hpullZ
    have hconstZ := congrFun hconst z
    calc
      muE[split | Fempty] z =
          (muE[(fun _ : Ze => (1 : ℝ)) | Fempty] +
            muE[(fun y : Ze => before y * increment y) | Fempty]) z := haddZ
      _ = 1 + before z * muE[increment | Fempty] z := by
        change muE[(fun _ : Ze => (1 : ℝ)) | Fempty] z +
          muE[before * increment | Fempty] z =
            1 + before z * muE[increment | Fempty] z
        rw [hconstZ]
        have hpullZ' :
            muE[before * increment | Fempty] z =
              before z * muE[increment | Fempty] z := by
          simpa only [Pi.mul_apply] using hpullZ
        rw [hpullZ']
  have hCEincrement :=
    ReferenceFirstLiveEmptyPendingExponentialIncrement.expRetainedIncrement_condExp_le_one
      rate rewards C_star C_h q t s hs control0 j
  have hresult : muE[after | Fempty] ≤ᵐ[muE]
      (fun z : Ze => 1 + before z) := by
    filter_upwards [hmono, hsplitCE, hCEincrement] with z hmonoZ hsplitZ hincrementZ
    rw [hsplitZ] at hmonoZ
    have hbeforeNonneg : 0 ≤ before z := by
      exact Real.exp_nonneg _
    have hproductBound : before z * muE[increment | Fempty] z ≤ before z := by
      calc
        before z * muE[increment | Fempty] z ≤ before z * 1 :=
          mul_le_mul_of_nonneg_left hincrementZ hbeforeNonneg
        _ = before z := mul_one _
    have hupper : 1 + before z * muE[increment | Fempty] z ≤ 1 + before z :=
      add_le_add_right hproductBound 1
    exact hmonoZ.trans hupper
  simpa [after, before] using hresult

/-- Integrating the conditional recurrence adds the mass of the same source
carrier, not one; this holds for the finite unnormalized measure, including
the zero measure case. -/
theorem integral_expBacklogAfter_step (j : Fin p.K) :
    (∫ z : Ze,
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ∂muE) ≤
      (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0).real Set.univ +
        (∫ z : Ze,
          expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∂muE) := by
  have hfieldle := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
    rate rewards C_star C_h q t s hs control0
  have hbeforeInt := integrable_expBacklogBefore
    rate rewards C_star C_h q t s hs control0 j
  have hafterInt := integrable_expBacklogAfter
    rate rewards C_star C_h q t s hs control0 j
  have hrhsInt : Integrable (fun z : Ze =>
      1 + expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) muE :=
    (integrable_const (1 : ℝ)).add hbeforeInt
  calc
    (∫ z : Ze,
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ∂muE) =
        ∫ z : Ze, muE[(fun x : Ze =>
          expBacklogAfter rate rewards C_star C_h q t s hs control0 j x) | Fempty] z ∂muE :=
      (integral_condExp hfieldle).symm
    _ ≤ ∫ z : Ze,
        1 + expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∂muE :=
      integral_mono_ae integrable_condExp hrhsInt
        (expBacklogAfter_condExp_step rate rewards C_star C_h q t s hs control0 j)
    _ = (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
          rate rewards C_star C_h q t s hs control0).real Set.univ +
        (∫ z : Ze,
          expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∂muE) := by
      rw [integral_add (integrable_const (1 : ℝ)) hbeforeInt]
      simp only [integral_const, smul_eq_mul, mul_one]

end Bandits.Support.ReferenceFirstLiveEmptyPendingConditionalExponentialQueue

end
