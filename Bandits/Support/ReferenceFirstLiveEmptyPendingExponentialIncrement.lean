/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveEmptyPendingAcceptedMoments

import Mathlib.Tactic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponential increment on the actual empty-pending source

This module proves the one-cell exponential estimate on the original empty-
pending source carrier and its finite, unnormalized measure. The strict-past
overflow event retains the current enabled update, including its service when
the accepted arrival is zero and the update which first overflows. The results
do not use queue energy, iterate a backlog bound, or identify the source field
with a manuscript history.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveEmptyPendingExponentialIncrement

abbrev Parameters := ReferenceFirstLiveEmptyPendingAcceptedMoments.Parameters
abbrev RateInput := ReferenceFirstLiveEmptyPendingAcceptedMoments.RateInput
abbrev RewardTable := ReferenceFirstLiveEmptyPendingAcceptedMoments.RewardTable
abbrev TimeControl := ReferenceFirstLiveEmptyPendingAcceptedMoments.TimeControl

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
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

/-- The retained current arrival minus enabled service, masked only by strict
past overflow. The current enabled cell remains included even if it overflows.
-/
def retainedIncrement (j : Fin p.K) (z : Ze) : ℝ :=
  Set.indicator G (fun x => acceptedA j x - 4) z

/-- Exponential of the accepted current arrival before service. -/
def expAcceptedArrival (j : Fin p.K) (z : Ze) : ℝ :=
  Real.exp (beta * acceptedA j z)

/-- Exponential of the literal retained current increment. -/
def expRetainedIncrement (j : Fin p.K) (z : Ze) : ℝ :=
  Real.exp (beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z)

private theorem beta_pos : 0 < beta :=
  CanonicalRecordingRates.beta_pos p rate.eta.property

private theorem beta_mul_acceptedA_le_one (j : Fin p.K) (z : Ze) :
    beta * acceptedA j z ≤ 1 := by
  have hbeta := beta_pos rate
  have hA := ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_pointwise_bounds
    rate rewards C_star C_h q t s hs control0 j z
  have hmul : acceptedA j z * beta ≤ 1 := (le_div_iff₀ hbeta).mp hA.2
  simpa [mul_comm] using hmul

/-- On the strict-past retained set, this is the actual accepted arrival
minus four units of service. -/
theorem retainedIncrement_eq_acceptedA_sub_four_of_mem_G (j : Fin p.K)
    (z : Ze) (hz : z ∈ G) :
    retainedIncrement rate rewards C_star C_h q t s hs control0 j z = acceptedA j z - 4 := by
  simp [retainedIncrement, hz]

/-- After strict-past overflow, the retained increment is zero. -/
theorem retainedIncrement_eq_zero_of_not_mem_G (j : Fin p.K)
    (z : Ze) (hz : z ∉ G) :
    retainedIncrement rate rewards C_star C_h q t s hs control0 j z = 0 := by
  simp [retainedIncrement, hz]

/-- An enabled retained zero-arrival cell still incurs its four units of
service. -/
theorem retainedIncrement_eq_neg_four_of_zero_acceptedA (j : Fin p.K)
    (z : Ze) (hz : z ∈ G) (hzero : acceptedA j z = 0) :
    retainedIncrement rate rewards C_star C_h q t s hs control0 j z = -4 := by
  rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
    rate rewards C_star C_h q t s hs control0 j z hz, hzero]
  ring

private theorem beta_mul_retainedIncrement_le_one (j : Fin p.K) (z : Ze) :
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

/-- Ambient measurability of the exponential of the accepted arrival. -/
theorem measurable_expAcceptedArrival (j : Fin p.K) :
    Measurable (fun z : Ze => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z) := by
  have hA := ReferenceFirstLiveEmptyPendingAcceptedMoments.measurable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hscaled : Measurable (fun z : Ze => beta * acceptedA j z) :=
    (measurable_const : Measurable (fun _ : Ze => beta)).mul hA
  simpa [expAcceptedArrival] using hscaled.exp

/-- Ambient measurability of the exponential of the retained increment. -/
theorem measurable_expRetainedIncrement (j : Fin p.K) :
    Measurable (fun z : Ze =>
      expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) := by
  have hinc : Measurable
      (fun z : Ze => retainedIncrement rate rewards C_star C_h q t s hs control0 j z) := by
    exact (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurable_acceptedA
      rate rewards C_star C_h q t s hs control0 j).sub_const 4 |>.indicator
        (ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
          rate rewards C_star C_h q t s hs control0)
  have hscaled : Measurable (fun z : Ze =>
      beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z) :=
    (measurable_const : Measurable (fun _ : Ze => beta)).mul hinc
  simpa [expRetainedIncrement] using hscaled.exp

private theorem integrable_of_norm_le_uniform {f : Ze → ℝ} {C : ℝ}
    (hf : Measurable f) (hC : 0 ≤ C) (hbound : ∀ z, ‖f z‖ ≤ C) :
    Integrable f muE := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  have habs : |C| = C := abs_of_nonneg hC
  simpa only [Real.norm_eq_abs, habs] using hbound z

/-- Integrability of the accepted-arrival exponential under the same finite,
unnormalized empty-pending source measure. -/
theorem integrable_expAcceptedArrival (j : Fin p.K) :
    Integrable (fun z : Ze => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z) muE := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp 1)
    (measurable_expAcceptedArrival rate rewards C_star C_h q t s hs control0 j)
    (by positivity)
  intro z
  change ‖Real.exp (beta * acceptedA j z)‖ ≤ Real.exp 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp_of_le
    (beta_mul_acceptedA_le_one rate rewards C_star C_h q t s hs control0 j z)

/-- Integrability of the retained-increment exponential under the same
finite, unnormalized source measure. -/
theorem integrable_expRetainedIncrement (j : Fin p.K) :
    Integrable (fun z : Ze =>
      expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) muE := by
  apply integrable_of_norm_le_uniform rate rewards C_star C_h q t s hs control0
    (C := Real.exp 1)
    (measurable_expRetainedIncrement rate rewards C_star C_h q t s hs control0 j)
    (by positivity)
  intro z
  change ‖Real.exp (beta * retainedIncrement rate rewards C_star C_h q t s hs control0 j z)‖ ≤ Real.exp 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp_of_le
    (beta_mul_retainedIncrement_le_one rate rewards C_star C_h q t s hs control0 j z)

/-- The conditional first moment of the accepted arrival is at most one on
the original empty-pending field. -/
theorem acceptedA_condExp_le_one (j : Fin p.K) :
    muE[(fun z : Ze => acceptedA j z) | Fempty] ≤ᵐ[muE] (fun _ : Ze => 1) := by
  have h := ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_first_bounds
    rate rewards C_star C_h q t s hs control0 j
  have hrho := ReferenceFirstLiveEmptyPendingSourceMoments.rho_bounds
    rate rewards C_star C_h q t s hs control0 j
  filter_upwards [h.2] with z hz
  by_cases hzG : z ∈ G
  · calc
      muE[(fun z : Ze => acceptedA j z) | Fempty] z ≤
          ReferenceFirstLiveEmptyPendingSourceMoments.rho rate rewards C_star C_h q t s hs control0 j := by
            simpa [Set.indicator_of_mem hzG] using hz
      _ ≤ 1 := hrho.2
  · have hz0 : muE[(fun z : Ze => acceptedA j z) | Fempty] z ≤ 0 := by
      simpa [Set.indicator_of_notMem hzG] using hz
    exact hz0.trans (by norm_num)

private theorem condExp_real_const_mul (c : ℝ) (f : Ze → ℝ) :
    muE[(fun z : Ze => c * f z) | Fempty] =ᵐ[muE]
      (fun z : Ze => c * muE[f | Fempty] z) := by
  have hscaled := condExp_smul (μ := muE) c f Fempty
  have hfun : (fun z : Ze => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  calc
    muE[(fun z : Ze => c * f z) | Fempty] =ᵐ[muE] muE[c • f | Fempty] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hfun z)
    _ =ᵐ[muE] (fun z : Ze => c * muE[f | Fempty] z) := by
      filter_upwards [hscaled] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz

/-- Conditional exponential chord estimate on the actual empty-pending
carrier, using its accepted-arrival conditional moment. -/
theorem condExp_expAcceptedArrival_le_chord (j : Fin p.K) :
    muE[(fun z : Ze => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z) | Fempty] ≤ᵐ[muE]
      (fun z : Ze => 1 + ((Real.exp 1 - 1) * beta) *
        muE[(fun z : Ze => acceptedA j z) | Fempty] z) := by
  let c : ℝ := (Real.exp 1 - 1) * beta
  have hAInt := ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
    rate rewards C_star C_h q t s hs control0 j
  have hExpInt := integrable_expAcceptedArrival
    rate rewards C_star C_h q t s hs control0 j
  have hScaledInt : Integrable (fun z : Ze => c * acceptedA j z) muE := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hAInt.const_mul c
  have hChordInt : Integrable (fun z : Ze => 1 + c * acceptedA j z) muE :=
    (integrable_const (1 : ℝ)).add hScaledInt
  have hPointwise : ∀ z : Ze,
      expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z ≤
        1 + c * acceptedA j z := by
    intro z
    have hA := ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_pointwise_bounds
      rate rewards C_star C_h q t s hs control0 j z
    have hscaled_nonneg : 0 ≤ beta * acceptedA j z :=
      mul_nonneg (le_of_lt (beta_pos rate)) hA.1
    have hscaled_le : beta * acceptedA j z ≤ 1 :=
      beta_mul_acceptedA_le_one rate rewards C_star C_h q t s hs control0 j z
    have hchord := RecordedRoundMoments.exp_le_unit_chord hscaled_nonneg hscaled_le
    change Real.exp (beta * acceptedA j z) ≤ _
    calc
      Real.exp (beta * acceptedA j z) ≤
          1 + (Real.exp 1 - 1) * (beta * acceptedA j z) := hchord
      _ = 1 + c * acceptedA j z := by dsimp [c]; ring
  have hmono := condExp_mono (m := Fempty) hExpInt hChordInt
    (Filter.Eventually.of_forall hPointwise)
  have hAdd := condExp_add (integrable_const (1 : ℝ)) hScaledInt Fempty
  have hConst := condExp_const (μ := muE)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) (1 : ℝ)
  have hSmul := condExp_real_const_mul rate rewards C_star C_h q t s hs control0 c
    (fun z : Ze => acceptedA j z)
  have hChordEq : (fun z : Ze => 1 + c * acceptedA j z) =
      (fun _ : Ze => (1 : ℝ)) + (fun z : Ze => c * acceptedA j z) := by
    funext z
    rfl
  have hChordCE :
      muE[(fun z : Ze => 1 + c * acceptedA j z) | Fempty] =ᵐ[muE]
        (fun z : Ze => 1 + c * muE[(fun x : Ze => acceptedA j x) | Fempty] z) := by
    calc
      muE[(fun z : Ze => 1 + c * acceptedA j z) | Fempty] =ᵐ[muE]
          muE[(fun _ : Ze => (1 : ℝ)) + (fun z : Ze => c * acceptedA j z) | Fempty] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hChordEq z)
      _ =ᵐ[muE] muE[(fun _ : Ze => (1 : ℝ)) | Fempty] +
          muE[(fun z : Ze => c * acceptedA j z) | Fempty] := hAdd
      _ =ᵐ[muE] (fun z : Ze => 1 +
          c * muE[(fun x : Ze => acceptedA j x) | Fempty] z) := by
        filter_upwards [hSmul] with z hsmulZ
        have hconstZ := congrFun hConst z
        simp only [Pi.add_apply, hconstZ, hsmulZ]
  exact Filter.EventuallyLE.trans hmono hChordCE.le

/-- The exponential service penalty dominates the unit-interval chord factor. -/
theorem exp_neg_four_beta_chord_le_one :
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤ 1 := by
  have hbeta := beta_pos rate
  have hc : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) hbeta.le
  have hlin := Real.add_one_le_exp ((Real.exp 1 - 1) * beta)
  have harg : (Real.exp 1 - 1) * beta - 4 * beta ≤ 0 := by
    have hcoef : Real.exp 1 - 5 ≤ 0 := by linarith [Real.exp_one_lt_three]
    calc
      (Real.exp 1 - 1) * beta - 4 * beta = (Real.exp 1 - 5) * beta := by ring
      _ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hcoef hbeta.le
  calc
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤
        Real.exp (-4 * beta) * Real.exp ((Real.exp 1 - 1) * beta) :=
      mul_le_mul_of_nonneg_left (by linarith [hlin]) (Real.exp_nonneg _)
    _ = Real.exp ((Real.exp 1 - 1) * beta - 4 * beta) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp 0 := Real.exp_le_exp_of_le harg
    _ = 1 := Real.exp_zero

/-- Pointwise decomposition into the accepted-arrival exponential on the
retained set and the value one off that set. -/
theorem expRetainedIncrement_indicator_identity (j : Fin p.K) (z : Ze) :
    expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z =
      Real.exp (-4 * beta) *
          Set.indicator G
            (fun x : Ze => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j x) z +
        Set.indicator Gᶜ (fun _ : Ze => (1 : ℝ)) z := by
  by_cases hz : z ∈ G
  · have hsplit : Real.exp (beta * (acceptedA j z - 4)) =
        Real.exp (-4 * beta) * Real.exp (beta * acceptedA j z) := by
      rw [show beta * (acceptedA j z - 4) = (-4 * beta) + beta * acceptedA j z by ring,
        Real.exp_add]
    simp [expRetainedIncrement, retainedIncrement, expAcceptedArrival, hz, hsplit]
  · simp [expRetainedIncrement, retainedIncrement, hz]

/-- The retained exponential has conditional expectation at most one under the
same finite, unnormalized empty-pending measure. -/
theorem expRetainedIncrement_condExp_le_one (j : Fin p.K) :
    muE[(fun z : Ze => expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z) | Fempty] ≤ᵐ[muE]
      (fun _ : Ze => 1) := by
  let f : Ze → ℝ := fun z => expAcceptedArrival rate rewards C_star C_h q t s hs control0 j z
  let fG : Ze → ℝ := Set.indicator G f
  let fGc : Ze → ℝ := Set.indicator Gᶜ (fun _ : Ze => (1 : ℝ))
  let cExp : ℝ := Real.exp (-4 * beta)
  have hGfield : MeasurableSet[Fempty] G :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G
      rate rewards C_star C_h q t s hs control0
  have hGambient : MeasurableSet G :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
      rate rewards C_star C_h q t s hs control0
  have hfInt : Integrable f muE := by
    simpa [f] using integrable_expAcceptedArrival
      rate rewards C_star C_h q t s hs control0 j
  have hfGInt : Integrable fG muE := by
    exact hfInt.indicator hGambient
  have hfGcInt : Integrable fGc muE := by
    exact (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hcExpInt : Integrable (fun z : Ze => cExp * fG z) muE := hfGInt.const_mul cExp
  have hRetEq : (fun z : Ze => expRetainedIncrement
      rate rewards C_star C_h q t s hs control0 j z) =
      (fun z : Ze => cExp * fG z + fGc z) := by
    funext z
    simpa [f, fG, fGc, cExp] using
      expRetainedIncrement_indicator_identity
        rate rewards C_star C_h q t s hs control0 j z
  have hAdd := condExp_add hcExpInt hfGcInt Fempty
  have hScale := condExp_real_const_mul rate rewards C_star C_h q t s hs control0 cExp fG
  have hMask := condExp_indicator (μ := muE) hfInt hGfield
  have hMaskComp := condExp_indicator (μ := muE) (integrable_const (1 : ℝ)) hGfield.compl
  have hConst := condExp_const (μ := muE)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0) (1 : ℝ)
  have hCEdecomp :
      muE[(fun z : Ze => expRetainedIncrement
        rate rewards C_star C_h q t s hs control0 j z) | Fempty] =ᵐ[muE]
        (fun z : Ze => cExp * Set.indicator G
          (fun x : Ze => muE[f | Fempty] x) z +
            Set.indicator Gᶜ (fun _ : Ze => 1) z) := by
    calc
      muE[(fun z : Ze => expRetainedIncrement
          rate rewards C_star C_h q t s hs control0 j z) | Fempty] =ᵐ[muE]
          muE[(fun z : Ze => cExp * fG z + fGc z) | Fempty] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hRetEq z)
      _ =ᵐ[muE] muE[(fun z : Ze => cExp * fG z) | Fempty] +
          muE[fGc | Fempty] := hAdd
      _ =ᵐ[muE] (fun z : Ze => cExp * muE[fG | Fempty] z +
          muE[fGc | Fempty] z) := by
        filter_upwards [hScale] with z hz
        simpa only [Pi.add_apply] using
          congrArg (fun x : ℝ => x + muE[fGc | Fempty] z) hz
      _ =ᵐ[muE] (fun z : Ze => cExp * Set.indicator G
          (fun x : Ze => muE[f | Fempty] x) z +
            Set.indicator Gᶜ (fun _ : Ze => 1) z) := by
        filter_upwards [hMask, hMaskComp] with z hG hGc
        rw [hG, hGc]
        rw [hConst]
  have hCEexpA := condExp_expAcceptedArrival_le_chord
    rate rewards C_star C_h q t s hs control0 j
  have hCEacceptedA := acceptedA_condExp_le_one
    rate rewards C_star C_h q t s hs control0 j
  have hcExpPos : 0 < cExp := by positivity
  have hcoeff : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) (le_of_lt (beta_pos rate))
  have hscalar := exp_neg_four_beta_chord_le_one rate
  filter_upwards [hCEdecomp, hCEexpA, hCEacceptedA] with z hdecomp hExpBound hABound
  rw [hdecomp]
  by_cases hz : z ∈ G
  · have hnot : z ∉ Gᶜ := by simpa using hz
    simp only [Set.indicator_of_mem hz, Set.indicator_of_notMem hnot, add_zero]
    calc
      cExp * muE[(fun x : Ze => expAcceptedArrival
          rate rewards C_star C_h q t s hs control0 j x) | Fempty] z ≤
          cExp * (1 + ((Real.exp 1 - 1) * beta) *
            muE[(fun x : Ze => acceptedA j x) | Fempty] z) :=
        mul_le_mul_of_nonneg_left hExpBound hcExpPos.le
      _ ≤ cExp * (1 + ((Real.exp 1 - 1) * beta)) := by
        apply mul_le_mul_of_nonneg_left _ hcExpPos.le
        have hmul := mul_le_mul_of_nonneg_left hABound hcoeff
        linarith
      _ ≤ 1 := by simpa [cExp] using hscalar
  · have hmem : z ∈ Gᶜ := by simpa using hz
    simp only [Set.indicator_of_notMem hz, Set.indicator_of_mem hmem,
      mul_zero, zero_add, le_rfl]

/-- Integrating the conditional estimate gives an upper bound by the mass of
the same source carrier, not by one. -/
theorem integral_expRetainedIncrement_le_measure_univ (j : Fin p.K) :
    (∫ z : Ze, expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z ∂muE) ≤
      (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0).real Set.univ := by
  have hfield := ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
    rate rewards C_star C_h q t s hs control0
  have hInt := integrable_expRetainedIncrement
    rate rewards C_star C_h q t s hs control0 j
  calc
    (∫ z : Ze, expRetainedIncrement rate rewards C_star C_h q t s hs control0 j z ∂muE) =
        ∫ z : Ze, muE[(fun x : Ze =>
          expRetainedIncrement rate rewards C_star C_h q t s hs control0 j x) | Fempty] z ∂muE :=
      (by
        simpa only [setIntegral_univ] using
          (setIntegral_condExp hfield hInt MeasurableSet.univ).symm)
    _ ≤ ∫ z : Ze, (1 : ℝ) ∂muE :=
      integral_mono_ae integrable_condExp (integrable_const (1 : ℝ))
        (expRetainedIncrement_condExp_le_one rate rewards C_star C_h q t s hs control0 j)
    _ = (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
        rate rewards C_star C_h q t s hs control0).real Set.univ := by
      simp only [integral_const, smul_eq_mul, mul_one]

end Bandits.Support.ReferenceFirstLiveEmptyPendingExponentialIncrement

end
