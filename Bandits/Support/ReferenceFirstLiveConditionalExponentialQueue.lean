/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveQueueEnergyEnvelope

import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Actual first-live conditional exponential queue step

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-188,245-290`
and `sources/zip4/manuscript/06_interruptions.tex:391-397,425-426`.

This module proves a one-cell conditional exponential estimate on the existing
first-live source cylinder. It uses the actual accepted-record conditional
first-moment bound, the strict-past overflow event, and the same unnormalized
branch measure and prefix field as the accepted-moment and energy modules.
The current inclusive overflow update is retained, and a zero accepted arrival
on an enabled retained cell still has increment `-4`. The results are one
branch step for a later original-source exponential iteration; they do not
identify the prefix field with manuscript `F_t` or close the manuscript queue
bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue

abbrev Parameters := ReferenceFirstLiveQueueEnergyEnvelope.Parameters
abbrev RateInput := ReferenceFirstLiveQueueEnergyEnvelope.RateInput
abbrev RewardTable := ReferenceFirstLiveQueueEnergyEnvelope.RewardTable
abbrev TimeControl := ReferenceFirstLiveQueueEnergyEnvelope.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "Fplus" => ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField rate rewards C_star C_h q t s hs control0
local notation "G" => ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0
local notation "beta" => ReferenceFirstLiveSourceSavedMoments.beta rate
local notation "acceptedA" => ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA rate rewards C_star C_h q t s hs control0
local notation "backlogBefore" => ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogBefore rate rewards C_star C_h q t s hs control0
local notation "backlogAfter" => ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter rate rewards C_star C_h q t s hs control0
local notation "Bcap" => 1 / (32 * rate.eta.val)

/-- The current accepted arrival minus the four units of service, masked by
the literal strict-past no-overflow event. This uses the accepted projection
from the actual `take n` / `take (n + 1)` cells on `Zplus`. -/
def retainedIncrement (j : Fin p.K) (z : Zplus) : ℝ :=
  Set.indicator G (fun x => acceptedA j x - 4) z

/-- The exponential of the actual retained increment, with the canonical
`32 * eta * L_stab` coefficient. -/
def expRetainedIncrement (j : Fin p.K) (z : Zplus) : ℝ :=
  Real.exp (beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z)

/-- Exponential of the actual strict-past normalized backlog. -/
def expBacklogBefore (j : Fin p.K) (z : Zplus) : ℝ :=
  Real.exp (beta * backlogBefore j z)

/-- Exponential of the actual normalized backlog after this inclusive cell. -/
def expBacklogAfter (j : Fin p.K) (z : Zplus) : ℝ :=
  Real.exp (beta * backlogAfter j z)

/-- Exponential of the actual accepted arrival before the service deduction. -/
def expAcceptedArrival (j : Fin p.K) (z : Zplus) : ℝ :=
  Real.exp (beta * acceptedA j z)

private theorem beta_pos : 0 < beta := by
  simpa [ReferenceFirstLiveSourceSavedMoments.beta] using
    CanonicalRecordingRates.beta_pos p rate.eta.property

private theorem beta_mul_acceptedA_le_one (j : Fin p.K) (z : Zplus) :
    beta * acceptedA j z ≤ 1 := by
  have hbeta := beta_pos rate
  have hA := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_pointwise_bounds rate rewards C_star C_h q t s hs control0 j z
  have hmul : acceptedA j z * beta ≤ 1 :=
    (le_div_iff₀ hbeta).mp hA.2
  simpa [mul_comm] using hmul

/-- On the retained event, the increment uses the actual accepted arrival,
including when that arrival is zero. -/
theorem retainedIncrement_eq_acceptedA_sub_four_of_mem_G (j : Fin p.K)
    (z : Zplus) (hz : z ∈ G) :
    retainedIncrement rate rewards C_star C_h q t s hs control0 j z = acceptedA j z - 4 := by
  simp [retainedIncrement, hz]

/-- After an earlier strict-past overflow the logical increment is zero. -/
theorem retainedIncrement_eq_zero_of_not_mem_G (j : Fin p.K)
    (z : Zplus) (hz : z ∉ G) :
    retainedIncrement rate rewards C_star C_h q t s hs control0 j z = 0 := by
  simp [retainedIncrement, hz]

/-- An enabled retained cell with zero accepted arrival still records the
four-unit service decrement in the queue increment. -/
theorem retainedIncrement_eq_neg_four_of_zero_acceptedA (j : Fin p.K)
    (z : Zplus) (hz : z ∈ G)
    (hzero : acceptedA j z = 0) :
    retainedIncrement rate rewards C_star C_h q t s hs control0 j z = -4 := by
  rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
    rate rewards C_star C_h q t s hs control0 j z hz, hzero]
  ring

private theorem beta_mul_retainedIncrement_le_one (j : Fin p.K) (z : Zplus) :
    beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z ≤ 1 := by
  by_cases hz : z ∈ G
  · rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    calc
      beta * (acceptedA j z - 4) = beta * acceptedA j z - 4 * beta := by ring
      _ ≤ beta * acceptedA j z := by nlinarith [beta_pos rate]
      _ ≤ 1 := beta_mul_acceptedA_le_one rate rewards C_star C_h q t s hs control0 j z
  · rw [retainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h q t s hs control0 j z hz]
    norm_num

/-- Ambient measurability of the literal retained source increment. -/
theorem measurable_retainedIncrement (j : Fin p.K) :
    Measurable (fun z : Zplus =>
      retainedIncrement rate rewards C_star C_h q t s hs control0 j z) := by
  have hA := ReferenceFirstLiveAllArmAcceptedConditionalMoments.measurable_acceptedA rate rewards C_star C_h q t s hs control0 j
  have hG := ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
    rate rewards C_star C_h q t s hs control0
  exact (hA.sub_const 4).indicator hG

/-- Prefix measurability of the exponential coefficient multiplying a
current-cell conditional expectation. -/
theorem measurable_expBacklogBefore_prefix (j : Fin p.K) :
    Measurable[Fplus] (fun z : Zplus => expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) := by
  have hbefore := ReferenceFirstLiveQueueEnergyEnvelope.measurable_backlogBefore
    rate rewards C_star C_h q t s hs control0 j
  have hscaled : Measurable[Fplus] (fun z : Zplus => beta * backlogBefore j z) :=
    (measurable_const : Measurable[Fplus] (fun _ : Zplus => beta)).mul hbefore
  simpa [expBacklogBefore] using hscaled.exp

/-- Ambient measurability of the strict-past exponential. -/
theorem measurable_expBacklogBefore (j : Fin p.K) :
    Measurable (fun z : Zplus => expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) := by
  exact (measurable_expBacklogBefore_prefix rate rewards C_star C_h q t s hs control0 j).mono
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0) le_rfl

/-- Ambient measurability of the inclusive successor exponential, using E's
actual Borel result for the successor queue. -/
theorem measurable_expBacklogAfter (j : Fin p.K) :
    Measurable (fun z : Zplus => expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) := by
  have hafter := ReferenceFirstLiveQueueEnergyEnvelope.measurable_backlogAfter
    rate rewards C_star C_h q t s hs control0 j
  have hscaled : Measurable (fun z : Zplus => beta * backlogAfter j z) :=
    (measurable_const : Measurable (fun _ : Zplus => beta)).mul hafter
  simpa [expBacklogAfter] using hscaled.exp

/-- Ambient measurability of the accepted-arrival exponential. -/
theorem measurable_expAcceptedArrival (j : Fin p.K) :
    Measurable (fun z : Zplus => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z) := by
  have haccepted := ReferenceFirstLiveAllArmAcceptedConditionalMoments.measurable_acceptedA rate rewards C_star C_h q t s hs control0 j
  have hscaled : Measurable (fun z : Zplus => beta * acceptedA j z) :=
    (measurable_const : Measurable (fun _ : Zplus => beta)).mul haccepted
  simpa [expAcceptedArrival] using hscaled.exp

/-- Ambient measurability of the retained-increment exponential. -/
theorem measurable_expRetainedIncrement (j : Fin p.K) :
    Measurable (fun z : Zplus => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) := by
  have hscaled : Measurable (fun z : Zplus =>
      beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z) :=
    (measurable_const : Measurable (fun _ : Zplus => beta)).mul
      (measurable_retainedIncrement rate rewards C_star C_h q t s hs control0 j)
  simpa [expRetainedIncrement] using hscaled.exp

private theorem integrable_of_norm_le_uniform {f : Zplus → ℝ} {C : ℝ}
    (hf : Measurable f) (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f muPlus := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  have habs : |C| = C := abs_of_nonneg hC
  simpa only [Real.norm_eq_abs, habs] using hbound z

/-- Finite `muPlus` integrability of the accepted-arrival exponential. -/
theorem integrable_expAcceptedArrival (j : Fin p.K) :
    Integrable (fun z : Zplus => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp 1) (measurable_expAcceptedArrival rate rewards C_star C_h q t s hs control0 j)
    (by positivity)
  intro z
  change ‖Real.exp (beta * acceptedA j z)‖ ≤ Real.exp 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp_of_le (beta_mul_acceptedA_le_one rate rewards C_star C_h q t s hs control0 j z)

/-- Finite `muPlus` integrability of the retained-increment exponential. -/
theorem integrable_expRetainedIncrement (j : Fin p.K) :
    Integrable (fun z : Zplus => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp 1) (measurable_expRetainedIncrement rate rewards C_star C_h q t s hs control0 j)
    (by positivity)
  intro z
  change ‖Real.exp (beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z)‖ ≤ Real.exp 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp_of_le
    (beta_mul_retainedIncrement_le_one rate rewards C_star C_h q t s hs control0 j z)

/-- Finite `muPlus` integrability of the strict-past backlog exponential. -/
theorem integrable_expBacklogBefore (j : Fin p.K) :
    Integrable (fun z : Zplus => expBacklogBefore rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  have hbeta := beta_pos rate
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp (beta * (2 * Bcap)))
    (measurable_expBacklogBefore rate rewards C_star C_h q t s hs control0 j)
    (by positivity [rate.eta.property])
  intro z
  have hback := ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_le_two_Bcap
    rate rewards C_star C_h q t s hs control0 j z
  change ‖Real.exp (beta * backlogBefore j z)‖ ≤ Real.exp (beta * (2 * Bcap))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp_of_le
    (mul_le_mul_of_nonneg_left hback (le_of_lt hbeta))

/-- Finite `muPlus` integrability of the actual inclusive successor
exponential, including a first overflow update. -/
theorem integrable_expBacklogAfter (j : Fin p.K) :
    Integrable (fun z : Zplus => expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  have hbeta := beta_pos rate
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp (beta * (2 * Bcap)))
    (measurable_expBacklogAfter rate rewards C_star C_h q t s hs control0 j)
    (by positivity [rate.eta.property])
  intro z
  have hback := ReferenceFirstLiveQueueEnergyEnvelope.backlogAfter_le_two_Bcap
    rate rewards C_star C_h q t s hs control0 j z
  change ‖Real.exp (beta * backlogAfter j z)‖ ≤ Real.exp (beta * (2 * Bcap))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp_of_le
    (mul_le_mul_of_nonneg_left hback (le_of_lt hbeta))

/-- The coefficient-times-increment product needed for conditional
pull-out is integrable on the same finite, unnormalized source measure. -/
theorem integrable_expBacklogBefore_mul_expRetainedIncrement (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      expBacklogBefore rate rewards C_star C_h q t s hs control0 j z *
        expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) muPlus := by
  have hbeta := beta_pos rate
  have hbeforeMeas := measurable_expBacklogBefore rate rewards C_star C_h q t s hs control0 j
  have hincrementMeas := measurable_expRetainedIncrement rate rewards C_star C_h q t s hs control0 j
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp (beta * (2 * Bcap)) * Real.exp 1)
    (hbeforeMeas.mul hincrementMeas) (by positivity [rate.eta.property])
  intro z
  have hback := ReferenceFirstLiveQueueEnergyEnvelope.backlogBefore_le_two_Bcap
    rate rewards C_star C_h q t s hs control0 j z
  have hret := beta_mul_retainedIncrement_le_one
    rate rewards C_star C_h q t s hs control0 j z
  have hbefore : expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ≤
      Real.exp (beta * (2 * Bcap)) :=
    Real.exp_le_exp_of_le (mul_le_mul_of_nonneg_left hback (le_of_lt hbeta))
  have hincrement : expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z ≤
      Real.exp 1 := Real.exp_le_exp_of_le hret
  change ‖Real.exp (beta * backlogBefore j z) *
      Real.exp (beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
  exact mul_le_mul hbefore hincrement (Real.exp_nonneg _) (Real.exp_nonneg _)

/-- The actual accepted-arrival conditional first bound implies an upper
bound by one on this exact `Fplus` and `muPlus`; it is not a recording-PMF
calculation. -/
theorem acceptedA_condExp_le_one (j : Fin p.K) :
    muPlus[(fun z : Zplus => acceptedA j z) | Fplus] ≤ᵐ[muPlus]
      (fun _ : Zplus => 1) := by
  have h := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_first_bounds
    rate rewards C_star C_h q t s hs control0 j
  exact h.2.1.trans h.2.2

private theorem condExp_real_const_mul (c : ℝ) (f : Zplus → ℝ) :
    muPlus[(fun z : Zplus => c * f z) | Fplus] =ᵐ[muPlus]
      (fun z : Zplus => c * muPlus[f | Fplus] z) := by
  have hscaled := condExp_smul (μ := muPlus) c f Fplus
  have hfun : (fun z : Zplus => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  calc
    muPlus[(fun z : Zplus => c * f z) | Fplus] =ᵐ[muPlus] muPlus[c • f | Fplus] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hfun z)
    _ =ᵐ[muPlus] (fun z : Zplus => c * muPlus[f | Fplus] z) := by
      filter_upwards [hscaled] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz

/-- Conditional chord estimate for the accepted-arrival exponential. -/
private theorem condExp_expAcceptedArrival_le_chord (j : Fin p.K) :
    muPlus[(fun z : Zplus => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z) | Fplus] ≤ᵐ[muPlus]
      (fun z : Zplus => 1 + ((Real.exp 1 - 1) * beta) *
        muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z) := by
  let c : ℝ := (Real.exp 1 - 1) * beta
  have hbeta := beta_pos rate
  have hAInt := ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA rate rewards C_star C_h q t s hs control0 j
  have hExpInt := integrable_expAcceptedArrival rate rewards C_star C_h q t s hs control0 j
  have hScaledInt : Integrable (fun z : Zplus => c * acceptedA j z) muPlus := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hAInt.const_mul c
  have hChordInt : Integrable (fun z : Zplus => 1 + c * acceptedA j z) muPlus :=
    (integrable_const (1 : ℝ)).add hScaledInt
  have hPointwise : ∀ z : Zplus,
      expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z ≤
        1 + c * acceptedA j z := by
    intro z
    have hA := ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_pointwise_bounds rate rewards C_star C_h q t s hs control0 j z
    have hscaled_nonneg : 0 ≤ beta * acceptedA j z :=
      mul_nonneg (le_of_lt hbeta) hA.1
    have hscaled_le : beta * acceptedA j z ≤ 1 :=
      beta_mul_acceptedA_le_one rate rewards C_star C_h q t s hs control0 j z
    have hchord := RecordedRoundMoments.exp_le_unit_chord hscaled_nonneg hscaled_le
    change Real.exp (beta * acceptedA j z) ≤ _
    calc
      Real.exp (beta * acceptedA j z) ≤
          1 + (Real.exp 1 - 1) * (beta * acceptedA j z) := hchord
      _ = 1 + c * acceptedA j z := by dsimp [c]; ring
  have hmono := condExp_mono (m := Fplus) hExpInt hChordInt
    (Filter.Eventually.of_forall hPointwise)
  have hAdd := condExp_add (integrable_const (1 : ℝ)) hScaledInt Fplus
  have hConst := condExp_const (μ := muPlus)
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0) (1 : ℝ)
  have hSmul := condExp_real_const_mul rate rewards C_star C_h q t s hs control0 c
    (fun z : Zplus => acceptedA j z)
  have hChordEq : (fun z : Zplus => 1 + c * acceptedA j z) =
      (fun _ : Zplus => (1 : ℝ)) + (fun z : Zplus => c * acceptedA j z) := by
    funext z
    rfl
  have hChordCE :
      muPlus[(fun z : Zplus => 1 + c * acceptedA j z) | Fplus] =ᵐ[muPlus]
        (fun z : Zplus => 1 + c * muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z) := by
    calc
      muPlus[(fun z : Zplus => 1 + c * acceptedA j z) | Fplus] =ᵐ[muPlus]
          muPlus[(fun _ : Zplus => (1 : ℝ)) + (fun z : Zplus => c * acceptedA j z) | Fplus] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hChordEq z)
      _ =ᵐ[muPlus] muPlus[(fun _ : Zplus => (1 : ℝ)) | Fplus] +
          muPlus[(fun z : Zplus => c * acceptedA j z) | Fplus] := hAdd
      _ =ᵐ[muPlus] (fun z : Zplus => 1 +
          c * muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z) := by
        filter_upwards [hSmul] with z hsmulZ
        have hconstZ := congrFun hConst z
        simp only [Pi.add_apply, hconstZ, hsmulZ]
  exact Filter.EventuallyLE.trans hmono hChordCE.le

private theorem exp_neg_four_beta_chord_le_one :
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤ 1 := by
  have hbeta := beta_pos rate
  have hc : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) hbeta.le
  have hlin := Real.add_one_le_exp ((Real.exp 1 - 1) * beta)
  have harg : (Real.exp 1 - 1) * beta - 4 * beta ≤ 0 := by
    have hcoef : Real.exp 1 - 5 ≤ 0 := by linarith [Real.exp_one_lt_three]
    calc
      (Real.exp 1 - 1) * beta - 4 * beta =
          (Real.exp 1 - 5) * beta := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoef hbeta.le
  calc
    Real.exp (-4 * beta) *
        (1 + (Real.exp 1 - 1) * beta) ≤
      Real.exp (-4 * beta) *
        Real.exp ((Real.exp 1 - 1) * beta) :=
      mul_le_mul_of_nonneg_left (by linarith [hlin]) (Real.exp_nonneg _)
    _ = Real.exp ((Real.exp 1 - 1) * beta - 4 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp_of_le harg
    _ = 1 := Real.exp_zero

/-- The actual source-cylindrical retained increment has conditional
exponential moment at most one under the finite, unnormalized `muPlus`. -/
theorem expRetainedIncrement_condExp_le_one (j : Fin p.K) :
    muPlus[(fun z : Zplus => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) | Fplus] ≤ᵐ[muPlus]
      (fun _ : Zplus => 1) := by
  let f : Zplus → ℝ := fun z => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z
  let fG : Zplus → ℝ := Set.indicator G f
  let fGc : Zplus → ℝ := Set.indicator Gᶜ (fun _ : Zplus => (1 : ℝ))
  let cExp : ℝ := Real.exp (-4 * beta)
  have hGfield : MeasurableSet[Fplus] G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0
  have hGambient : MeasurableSet G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient rate rewards C_star C_h q t s hs control0
  have hfInt := integrable_expAcceptedArrival rate rewards C_star C_h q t s hs control0 j
  have hfGInt : Integrable fG muPlus := by
    exact (show Integrable f muPlus from by simpa [f] using hfInt).indicator hGambient
  have hfGcInt : Integrable fGc muPlus := by
    exact (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hcExpInt : Integrable (fun z : Zplus => cExp * fG z) muPlus :=
    hfGInt.const_mul cExp
  have hRetEq : (fun z : Zplus => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) =
      (fun z : Zplus => cExp * fG z + fGc z) := by
    funext z
    by_cases hz : z ∈ G
    · have hsplit : Real.exp (beta * (acceptedA j z - 4)) =
          Real.exp (-4 * beta) * Real.exp (beta * acceptedA j z) := by
        rw [show beta * (acceptedA j z - 4) =
          (-4 * beta) + beta * acceptedA j z by ring, Real.exp_add]
      simp [expRetainedIncrement, retainedIncrement, expAcceptedArrival, f, fG, fGc, cExp, hz, hsplit]
    · simp [expRetainedIncrement, retainedIncrement, fG, fGc, cExp, hz]
  have hAdd := condExp_add hcExpInt hfGcInt Fplus
  have hScale := condExp_real_const_mul rate rewards C_star C_h q t s hs control0 cExp fG
  have hMask := condExp_indicator (μ := muPlus) hfInt hGfield
  have hMaskComp := condExp_indicator (μ := muPlus) (integrable_const (1 : ℝ)) hGfield.compl
  have hConst := condExp_const (μ := muPlus)
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0) (1 : ℝ)
  have hCEdecomp :
      muPlus[(fun z : Zplus => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) | Fplus] =ᵐ[muPlus]
        (fun z : Zplus => cExp * Set.indicator G
          (fun x : Zplus => muPlus[f | Fplus] x) z + Set.indicator Gᶜ (fun _ : Zplus => 1) z) := by
    calc
      muPlus[(fun z : Zplus => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) | Fplus] =ᵐ[muPlus]
          muPlus[(fun z : Zplus => cExp * fG z + fGc z) | Fplus] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hRetEq z)
      _ =ᵐ[muPlus] muPlus[(fun z : Zplus => cExp * fG z) | Fplus] +
          muPlus[fGc | Fplus] := hAdd
      _ =ᵐ[muPlus] (fun z : Zplus => cExp * muPlus[fG | Fplus] z +
          muPlus[fGc | Fplus] z) := by
        filter_upwards [hScale] with z hz
        simpa only [Pi.add_apply] using
          congrArg (fun x : ℝ => x + muPlus[fGc | Fplus] z) hz
      _ =ᵐ[muPlus] (fun z : Zplus => cExp * Set.indicator G
          (fun x : Zplus => muPlus[f | Fplus] x) z +
          Set.indicator Gᶜ (fun _ : Zplus => 1) z) := by
        filter_upwards [hMask, hMaskComp] with z hG hGc
        rw [hG, hGc]
        rw [hConst]

  have hCEexpA := condExp_expAcceptedArrival_le_chord
    rate rewards C_star C_h q t s hs control0 j
  have hCEacceptedA := acceptedA_condExp_le_one
    rate rewards C_star C_h q t s hs control0 j
  have hcExpPos : 0 < cExp := by positivity
  have hscalar := exp_neg_four_beta_chord_le_one rate
  filter_upwards [hCEdecomp, hCEexpA, hCEacceptedA] with z hdecomp hExpBound hABound
  rw [hdecomp]
  by_cases hz : z ∈ G
  · have hnot : z ∉ Gᶜ := by simpa using hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem hnot, add_zero]
    calc
      cExp * muPlus[(fun x : Zplus => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j x) | Fplus] z ≤
          cExp * (1 + ((Real.exp 1 - 1) * beta) *
            muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z) :=
        mul_le_mul_of_nonneg_left hExpBound hcExpPos.le
      _ ≤ cExp * (1 + ((Real.exp 1 - 1) * beta)) := by
        have hcoeff : 0 ≤ (Real.exp 1 - 1) * beta := by
          have he := Real.exp_one_gt_two
          exact mul_nonneg (by linarith) (le_of_lt (beta_pos rate))
        have hmul := mul_le_mul_of_nonneg_left hABound hcoeff
        have hinner : 1 + ((Real.exp 1 - 1) * beta) *
              muPlus[(fun x : Zplus => acceptedA j x) | Fplus] z ≤
            1 + ((Real.exp 1 - 1) * beta) := by linarith [hmul]
        exact mul_le_mul_of_nonneg_left hinner hcExpPos.le
      _ ≤ 1 := by simpa [cExp] using hscalar
  · have hnot : z ∉ G := hz
    have hmem : z ∈ Gᶜ := by simpa using hnot
    simp only [Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem,
      mul_zero, zero_add, le_rfl]

/-- Pointwise queue recurrence on the actual inclusive source cell. -/
theorem expBacklogAfter_le_retained_split (j : Fin p.K) (z : Zplus) :
    expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ≤
      Set.indicator G (fun x : Zplus => 1 +
        expBacklogBefore rate rewards C_star C_h q t s hs control0 j x *
          expRetainedIncrement rate rewards C_star C_h q t s hs control0 j x) z +
      Set.indicator Gᶜ (expBacklogBefore rate rewards C_star C_h q t s hs control0 j) z := by
  by_cases hz : z ∈ G
  · have hafter := ReferenceFirstLiveAllArmAcceptedConditionalMoments.backlogAfter_eq_max_on_G
      rate rewards C_star C_h q t s hs control0 j z hz
    have hsum : backlogBefore j z + (acceptedA j z - 4) =
        backlogBefore j z + acceptedA j z - 4 := by ring
    have hqueue := CanonicalQueueProcess.exp_mul_max_le
      (backlogBefore j z) (acceptedA j z - 4) (beta)
    rw [hsum] at hqueue
    calc
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z =
          Real.exp (beta * max (backlogBefore j z + acceptedA j z - 4) 0) := by
        rw [expBacklogAfter, hafter]
      _ ≤ 1 + Real.exp (beta * backlogBefore j z) *
          Real.exp (beta * (acceptedA j z - 4)) := hqueue
      _ = Set.indicator G (fun x : Zplus => 1 +
            expBacklogBefore rate rewards C_star C_h q t s hs control0 j x *
              expRetainedIncrement rate rewards C_star C_h q t s hs control0 j x) z +
          Set.indicator Gᶜ (expBacklogBefore rate rewards C_star C_h q t s hs control0 j) z := by
        simp [hz, expBacklogBefore, expRetainedIncrement, retainedIncrement]
  · have hnoop := ReferenceFirstLiveAllArmAcceptedConditionalMoments.stopped_queue_noop_off_G
      rate rewards C_star C_h q t s hs control0 j z hz
    simp [expBacklogAfter, expBacklogBefore, hnoop.2.2.1, hz]

/-- Actual conditional exponential queue recurrence on the same source
cylinder. The `G`-indicator is retained in the additive service term. -/
theorem expBacklogAfter_condExp_step (j : Fin p.K) :
    muPlus[(fun z : Zplus => expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) | Fplus] ≤ᵐ[muPlus]
      (fun z : Zplus => expBacklogBefore rate rewards C_star C_h q t s hs control0 j z +
        Set.indicator G (fun _ : Zplus => 1) z) := by
  let before : Zplus → ℝ := expBacklogBefore rate rewards C_star C_h q t s hs control0 j
  let increment : Zplus → ℝ := expRetainedIncrement rate rewards C_star C_h q t s hs control0 j
  let inner : Zplus → ℝ := fun z => 1 + before z * increment z
  let onTerm : Zplus → ℝ := Set.indicator G inner
  let offTerm : Zplus → ℝ := Set.indicator Gᶜ before
  let split : Zplus → ℝ := onTerm + offTerm
  have hfieldle := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0
  have hGfield : MeasurableSet[Fplus] G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0
  have hGambient : MeasurableSet G :=
    ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient rate rewards C_star C_h q t s hs control0
  have hGcambient : MeasurableSet Gᶜ := hGambient.compl
  have hBeforeMeas := measurable_expBacklogBefore_prefix
    rate rewards C_star C_h q t s hs control0 j
  have hBeforeStrong : StronglyMeasurable[Fplus] before := by simpa [before] using hBeforeMeas.stronglyMeasurable
  have hBeforeInt := integrable_expBacklogBefore
    rate rewards C_star C_h q t s hs control0 j
  have hIncrementInt := integrable_expRetainedIncrement
    rate rewards C_star C_h q t s hs control0 j
  have hProductInt := integrable_expBacklogBefore_mul_expRetainedIncrement
    rate rewards C_star C_h q t s hs control0 j
  have hInnerInt : Integrable inner muPlus := by
    exact (integrable_const (1 : ℝ)).add (by simpa [inner, before, increment] using hProductInt)
  have hOnInt : Integrable onTerm muPlus := by
    exact hInnerInt.indicator hGambient
  have hOffInt : Integrable offTerm muPlus := by
    exact hBeforeInt.indicator hGcambient
  have hSplitInt : Integrable split muPlus := by
    exact hOnInt.add hOffInt
  have hPointwise : ∀ z : Zplus,
      expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ≤ split z := by
    intro z
    simpa [split, onTerm, offTerm, inner, before, increment] using
      expBacklogAfter_le_retained_split rate rewards C_star C_h q t s hs control0 j z
  have hMono := condExp_mono (m := Fplus)
    (integrable_expBacklogAfter rate rewards C_star C_h q t s hs control0 j)
    hSplitInt (Filter.Eventually.of_forall hPointwise)
  have hInnerCE :
      muPlus[inner | Fplus] =ᵐ[muPlus]
        (fun z : Zplus => 1 + muPlus[(fun x : Zplus => before x * increment x) | Fplus] z) := by
    have hprod := by simpa [before, increment] using hProductInt
    have hadd := condExp_add (integrable_const (1 : ℝ)) hprod Fplus
    have hInnerEq : inner =
        (fun _ : Zplus => (1 : ℝ)) + (fun z : Zplus => before z * increment z) := by
      funext z
      rfl
    have hAddInner := (condExp_congr_ae
      (Filter.Eventually.of_forall fun z => congrFun hInnerEq z)).trans hadd
    have hconst := condExp_const (μ := muPlus) hfieldle (1 : ℝ)
    filter_upwards [hAddInner] with z hz
    have hconstZ := congrFun hconst z
    simpa only [Pi.add_apply, hconstZ] using hz
  have hPull := condExp_mul_of_stronglyMeasurable_left
    hBeforeStrong hProductInt hIncrementInt
  have hBeforeCE : muPlus[before | Fplus] = before :=
    condExp_of_stronglyMeasurable (μ := muPlus) hfieldle hBeforeStrong hBeforeInt
  have hOnCE := condExp_indicator (μ := muPlus) hInnerInt hGfield
  have hOffCE := condExp_indicator (μ := muPlus) hBeforeInt hGfield.compl
  have hSplitCE :
      muPlus[split | Fplus] =ᵐ[muPlus]
        (fun z : Zplus =>
          Set.indicator G (fun x : Zplus => 1 + before x *
            muPlus[(fun y : Zplus => increment y) | Fplus] x) z +
          Set.indicator Gᶜ before z) := by
    have hadd := condExp_add hOnInt hOffInt Fplus
    filter_upwards [hadd, hOnCE, hOffCE, hInnerCE, hPull] with z haddZ hOnZ hOffZ hInnerZ hPullZ
    calc
      muPlus[split | Fplus] z = (muPlus[onTerm | Fplus] + muPlus[offTerm | Fplus]) z := haddZ
      _ = Set.indicator G (fun x : Zplus => muPlus[inner | Fplus] x) z +
          Set.indicator Gᶜ (muPlus[before | Fplus]) z := by
        change (muPlus[Set.indicator G inner | Fplus] z +
          muPlus[Set.indicator Gᶜ before | Fplus] z) = _
        rw [hOnZ, hOffZ]
      _ = Set.indicator G (fun x : Zplus => 1 + before x *
            muPlus[(fun y : Zplus => increment y) | Fplus] x) z +
            Set.indicator Gᶜ before z := by
        by_cases hz : z ∈ G
        · have hnot : z ∉ Gᶜ := by simpa using hz
          simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem hnot]
          have hPullZ' : muPlus[(fun x : Zplus => before x * increment x) | Fplus] z =
              before z * muPlus[(fun y : Zplus => increment y) | Fplus] z := by
            exact hPullZ
          rw [hInnerZ, hPullZ']
        · have hnot : z ∉ G := hz
          have hmem : z ∈ Gᶜ := by simpa using hnot
          simp only [Set.indicator_of_notMem hnot, Set.indicator_of_mem hmem]
          simp [hBeforeCE]
  have hCEincrement := expRetainedIncrement_condExp_le_one
    rate rewards C_star C_h q t s hs control0 j
  have hBeforeNonneg : ∀ z : Zplus, 0 ≤ before z := by
    intro z
    exact Real.exp_nonneg _
  filter_upwards [hMono, hSplitCE, hCEincrement] with z hmono hsplit hinc
  rw [hsplit] at hmono
  by_cases hz : z ∈ G
  · have hprodBound : before z *
        muPlus[(fun y : Zplus => increment y) | Fplus] z ≤ before z := by
      calc
        before z * muPlus[(fun y : Zplus => increment y) | Fplus] z ≤ before z * 1 :=
          mul_le_mul_of_nonneg_left hinc (hBeforeNonneg z)
        _ = before z := mul_one _
    have hupper : 1 + before z *
        muPlus[(fun y : Zplus => increment y) | Fplus] z ≤ before z + 1 := by
      linarith
    have hmonoG : muPlus[(fun z : Zplus =>
        expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) | Fplus] z ≤
        before z + 1 := by
      have hmonoG' : muPlus[(fun z : Zplus =>
          expBacklogAfter rate rewards C_star C_h q t s hs control0 j z) | Fplus] z ≤
          1 + before z * muPlus[(fun y : Zplus => increment y) | Fplus] z := by
        simpa [hz] using hmono
      exact hmonoG'.trans hupper
    simpa [hz, before, expBacklogBefore] using hmonoG
  · simpa [hz, before, expBacklogBefore] using hmono

/-- Integration of one conditional queue step on the same unnormalized
`muPlus`; this does not iterate over a changed source measure. -/
theorem integral_expBacklogAfter_step (j : Fin p.K) :
    (∫ z : Zplus, expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ∂muPlus) ≤
      (∫ z : Zplus, expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∂muPlus) +
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate rewards C_star C_h q t s hs control0).real G := by
  let indicatorG : Zplus → ℝ := Set.indicator G (fun _ => (1 : ℝ))
  have hfieldle := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le rate rewards C_star C_h q t s hs control0
  have hGambient := ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
    rate rewards C_star C_h q t s hs control0
  have hBeforeInt := integrable_expBacklogBefore rate rewards C_star C_h q t s hs control0 j
  have hAfterInt := integrable_expBacklogAfter rate rewards C_star C_h q t s hs control0 j
  have hIndicatorInt : Integrable indicatorG muPlus := by
    exact (integrable_const (1 : ℝ)).indicator hGambient
  have hRhsInt : Integrable (fun z : Zplus =>
      expBacklogBefore rate rewards C_star C_h q t s hs control0 j z +
        Set.indicator G (fun _ : Zplus => 1) z) muPlus := by
    exact hBeforeInt.add (by simpa [indicatorG] using hIndicatorInt)
  calc
    (∫ z : Zplus, expBacklogAfter rate rewards C_star C_h q t s hs control0 j z ∂muPlus) =
        ∫ z : Zplus, muPlus[(fun x : Zplus =>
          expBacklogAfter rate rewards C_star C_h q t s hs control0 j x) | Fplus] z ∂muPlus :=
      (integral_condExp hfieldle).symm
    _ ≤ ∫ z : Zplus,
        expBacklogBefore rate rewards C_star C_h q t s hs control0 j z +
          Set.indicator G (fun _ : Zplus => 1) z ∂muPlus :=
      integral_mono_ae integrable_condExp hRhsInt
        (expBacklogAfter_condExp_step rate rewards C_star C_h q t s hs control0 j)
    _ = (∫ z : Zplus,
          expBacklogBefore rate rewards C_star C_h q t s hs control0 j z ∂muPlus) +
          (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
            rate rewards C_star C_h q t s hs control0).real G := by
      rw [integral_add hBeforeInt (by simpa [indicatorG] using hIndicatorInt)]
      have hIndicatorIntegral :
          (∫ z : Zplus, Set.indicator G (fun _ : Zplus => (1 : ℝ)) z ∂muPlus) =
            (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
              rate rewards C_star C_h q t s hs control0).real G := by
        have hone : (fun _ : Zplus => (1 : ℝ)) = (1 : Zplus → ℝ) := by
          funext z
          rfl
        rw [hone]
        exact integral_indicator_one (μ := muPlus) (s := G) hGambient
      rw [hIndicatorIntegral]

end Bandits.Support.ReferenceFirstLiveConditionalExponentialQueue

end
