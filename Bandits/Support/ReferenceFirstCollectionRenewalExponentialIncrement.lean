/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exponential increment on the actual first-renewal complement

This module proves the retained exponential-increment estimate on the same
finite, unnormalized renewal pair law and actual retained-coordinate field as
the accepted complement moments. The strict-past overflow test retains the
current enabled update, including zero-arrival service and the update that
first overflows. The final integral bound uses the mass of this source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ContinuousLearningRows

namespace Bandits.Support.ReferenceFirstCollectionRenewalExponentialIncrement

abbrev Params := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Pair {p : Params} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
abbrev RetainedCoordinates (p : Params) :=
  ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p

variable {p : Params}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : TimeControl p)

local instance sourceInputMeasurableSpace (p : Params) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" => Pair rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "R" =>
  ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap R
  (inferInstance : MeasurableSpace (RetainedCoordinates p))
local notation "G" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0
local notation "acceptedA" =>
  ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
    rate rewards C_star C_h u t
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

/-- The actual accepted arrival minus four units of service, retained exactly
when the actual incoming queue has no earlier overflow. -/
def retainedIncrement (j : Fin p.K) (b : B) : ℝ :=
  Set.indicator G (fun b => acceptedA j b - 4) b

/-- The exponential of the actual accepted arrival before service. -/
def expAcceptedArrival (_control0 : TimeControl p) (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta * acceptedA j b)

/-- The exponential of the literal retained current increment. -/
def expRetainedIncrement (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta * retainedIncrement rate rewards C_star C_h u t control0 j b)

/-- Canonical exponential rate is strictly positive. -/
theorem beta_pos : 0 < beta :=
  CanonicalRecordingRates.beta_pos p rate.eta.property

/-- The actual accepted arrival remains in the canonical unit exponential
interval, including its stopped zero branch. -/
theorem beta_mul_acceptedA_le_one (j : Fin p.K) (b : B) :
    beta * acceptedA j b ≤ 1 := by
  have hbeta := beta_pos rate
  have hA := ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA_bounds
    rate rewards C_star C_h u t b j
  have hmul : acceptedA j b * beta ≤ 1 := (le_div_iff₀ hbeta).mp hA.2
  simpa [mul_comm] using hmul

/-- On the exact retained set, the increment is the current actual accepted
arrival minus service. -/
theorem retainedIncrement_eq_acceptedA_sub_four_of_mem_G (j : Fin p.K)
    (b : B) (hb : b ∈ G) :
    retainedIncrement rate rewards C_star C_h u t control0 j b = acceptedA j b - 4 := by
  simp [retainedIncrement, hb]

/-- After an earlier overflow, the retained increment is zero. -/
theorem retainedIncrement_eq_zero_of_not_mem_G (j : Fin p.K)
    (b : B) (hb : b ∉ G) :
    retainedIncrement rate rewards C_star C_h u t control0 j b = 0 := by
  simp [retainedIncrement, hb]

/-- A retained enabled zero-arrival cell still incurs four units of service. -/
theorem retainedIncrement_eq_neg_four_of_zero_acceptedA (j : Fin p.K)
    (b : B) (hb : b ∈ G) (hzero : acceptedA j b = 0) :
    retainedIncrement rate rewards C_star C_h u t control0 j b = -4 := by
  rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
    rate rewards C_star C_h u t control0 j b hb, hzero]
  ring

/-- The retained increment has a finite pointwise interval. -/
theorem retainedIncrement_bounds (j : Fin p.K) (b : B) :
    -4 ≤ retainedIncrement rate rewards C_star C_h u t control0 j b ∧
      retainedIncrement rate rewards C_star C_h u t control0 j b ≤ 1 / beta := by
  have hA := ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA_bounds
    rate rewards C_star C_h u t b j
  have hbeta := beta_pos rate
  by_cases hb : b ∈ G
  · rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    constructor <;> linarith
  · rw [retainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    constructor
    · norm_num
    · positivity

private theorem beta_mul_retainedIncrement_le_one (j : Fin p.K) (b : B) :
    beta * retainedIncrement rate rewards C_star C_h u t control0 j b ≤ 1 := by
  by_cases hb : b ∈ G
  · rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    calc
      beta * (acceptedA j b - 4) = beta * acceptedA j b - 4 * beta := by ring
      _ ≤ beta * acceptedA j b := by nlinarith [beta_pos rate]
      _ ≤ 1 := beta_mul_acceptedA_le_one rate rewards C_star C_h u t j b
  · rw [retainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    norm_num

/-- The accepted-arrival exponential is nonnegative and bounded by `exp 1`. -/
theorem expAcceptedArrival_bounds (j : Fin p.K) (b : B) :
    0 ≤ expAcceptedArrival rate rewards C_star C_h u t control0 j b ∧
      expAcceptedArrival rate rewards C_star C_h u t control0 j b ≤ Real.exp 1 := by
  constructor
  · exact Real.exp_nonneg _
  · exact Real.exp_le_exp_of_le
      (beta_mul_acceptedA_le_one rate rewards C_star C_h u t j b)

/-- The retained-increment exponential is nonnegative and bounded by `exp 1`.
-/
theorem expRetainedIncrement_bounds (j : Fin p.K) (b : B) :
    0 ≤ expRetainedIncrement rate rewards C_star C_h u t control0 j b ∧
      expRetainedIncrement rate rewards C_star C_h u t control0 j b ≤ Real.exp 1 := by
  constructor
  · exact Real.exp_nonneg _
  · exact Real.exp_le_exp_of_le
      (beta_mul_retainedIncrement_le_one rate rewards C_star C_h u t control0 j b)

/-- Ambient Borel measurability of the accepted-arrival exponential. -/
theorem measurable_expAcceptedArrival (j : Fin p.K) :
    Measurable (fun b : B => expAcceptedArrival rate rewards C_star C_h u t control0 j b) := by
  have hA := ReferenceFirstCollectionRenewalAcceptedComplementMoments.measurable_acceptedA
    rate rewards C_star C_h u t j
  have hscaled : Measurable (fun b : B => beta * acceptedA j b) :=
    (measurable_const : Measurable (fun _ : B => beta)).mul hA
  simpa [expAcceptedArrival] using hscaled.exp

/-- Ambient Borel measurability of the literal retained increment. -/
theorem measurable_retainedIncrement (j : Fin p.K) :
    Measurable (fun b : B =>
      retainedIncrement rate rewards C_star C_h u t control0 j b) := by
  have hGfield := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  rcases hGfield with ⟨S, hS, hpre⟩
  have hR : Measurable R := (comap_measurable R).mono hdom le_rfl
  have hGambient : MeasurableSet G := by
    rw [← hpre]
    exact hS.preimage hR
  exact (ReferenceFirstCollectionRenewalAcceptedComplementMoments.measurable_acceptedA
    rate rewards C_star C_h u t j).sub_const 4 |>.indicator hGambient

/-- Ambient Borel measurability of the retained-increment exponential. -/
theorem measurable_expRetainedIncrement (j : Fin p.K) :
    Measurable (fun b : B =>
      expRetainedIncrement rate rewards C_star C_h u t control0 j b) := by
  have hinc := measurable_retainedIncrement rate rewards C_star C_h u t control0 j
  have hscaled : Measurable (fun b : B =>
      beta * retainedIncrement rate rewards C_star C_h u t control0 j b) :=
    (measurable_const : Measurable (fun _ : B => beta)).mul hinc
  simpa [expRetainedIncrement] using hscaled.exp

private theorem integrable_of_norm_le_const {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) : Integrable f ν := by
  have hconst : Integrable (fun _ : α => C) ν := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa using hbound x

/-- Finite-measure integrability of the bounded retained increment. -/
theorem integrable_retainedIncrement (j : Fin p.K) :
    Integrable
      (fun b : B => retainedIncrement rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_norm_le_const (ν := mu)
    (measurable_retainedIncrement rate rewards C_star C_h u t control0 j)
    (4 + 1 / beta)
  intro b
  have hb := retainedIncrement_bounds rate rewards C_star C_h u t control0 j b
  have hbeta := beta_pos rate
  have hInv : 0 ≤ 1 / beta := by positivity
  rw [Real.norm_eq_abs]
  exact (abs_le.mpr ⟨by linarith, by linarith⟩)

/-- Finite-measure integrability of the accepted-arrival exponential. -/
theorem integrable_expAcceptedArrival (j : Fin p.K) :
    Integrable
      (fun b : B => expAcceptedArrival rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_norm_le_const (ν := mu)
    (measurable_expAcceptedArrival rate rewards C_star C_h u t control0 j)
    (Real.exp 1)
  intro b
  have hb := expAcceptedArrival_bounds rate rewards C_star C_h u t control0 j b
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

/-- Finite-measure integrability of the retained-increment exponential. -/
theorem integrable_expRetainedIncrement (j : Fin p.K) :
    Integrable
      (fun b : B => expRetainedIncrement rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_norm_le_const (ν := mu)
    (measurable_expRetainedIncrement rate rewards C_star C_h u t control0 j)
    (Real.exp 1)
  intro b
  have hb := expRetainedIncrement_bounds rate rewards C_star C_h u t control0 j b
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

/-- The actual accepted arrival's conditional first moment is at most one on
the exact retained field. This follows from the complement coefficient and
the unit interval bounds for its literal `chi` and reward. -/
theorem acceptedA_condExp_le_one (j : Fin p.K) :
    mu[(fun b : B => acceptedA j b) | F_R] ≤ᵐ[mu] (fun _ : B => 1) := by
  have hce := ReferenceFirstCollectionRenewalAcceptedComplementMoments.condExp_acceptedA_bounds
    rate rewards C_star C_h u t control0 j
  have hrange := RealRewardGridCount.realRewardGridValue_mem_Icc
    (D p) (D_pos p) (rewards t j)
  have hr : 0 ≤ ReferenceFirstCollectionRenewalComplementMoments.r rewards t j ∧
      ReferenceFirstCollectionRenewalComplementMoments.r rewards t j ≤ 1 := by
    simpa [ReferenceFirstCollectionRenewalComplementMoments.r] using hrange
  filter_upwards [hce] with b hb
  have hchi :
      0 ≤ ReferenceFirstCollectionRenewalComplementMoments.chi
          rate rewards C_star C_h u t b j ∧
      ReferenceFirstCollectionRenewalComplementMoments.chi
          rate rewards C_star C_h u t b j ≤ 1 := by
    unfold ReferenceFirstCollectionRenewalComplementMoments.chi
    split <;> norm_num
  by_cases hG : b ∈ G
  · have hupper := hb.2.2
    have hupper' :
        mu[(fun x : B => acceptedA j x) | F_R] b ≤
          ReferenceFirstCollectionRenewalComplementMoments.chi
            rate rewards C_star C_h u t b j *
            ReferenceFirstCollectionRenewalComplementMoments.r rewards t j := by
      simpa [Set.indicator_of_mem hG] using hupper
    calc
      mu[(fun x : B => acceptedA j x) | F_R] b ≤ _ := hupper'
      _ ≤ 1 := by
        calc
          ReferenceFirstCollectionRenewalComplementMoments.chi
                rate rewards C_star C_h u t b j *
              ReferenceFirstCollectionRenewalComplementMoments.r rewards t j ≤
            1 * ReferenceFirstCollectionRenewalComplementMoments.r rewards t j :=
              mul_le_mul_of_nonneg_right hchi.2 hr.1
          _ ≤ 1 := by simpa using hr.2
  · have hupper := hb.2.2
    have hzero : mu[(fun x : B => acceptedA j x) | F_R] b ≤ 0 := by
      simpa [Set.indicator_of_notMem hG] using hupper
    exact hzero.trans (by norm_num)

private theorem condExp_real_const_mul (c : ℝ) (f : B → ℝ) :
    mu[(fun b : B => c * f b) | F_R] =ᵐ[mu]
      (fun b : B => c * mu[f | F_R] b) := by
  have hscaled := condExp_smul (μ := mu) c f F_R
  have hfun : (fun b : B => c * f b) = c • f := by
    funext b
    simp [smul_eq_mul]
  calc
    mu[(fun b : B => c * f b) | F_R] =ᵐ[mu] mu[c • f | F_R] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun b => congrFun hfun b)
    _ =ᵐ[mu] (fun b : B => c * mu[f | F_R] b) := by
      filter_upwards [hscaled] with b hb
      simpa only [Pi.smul_apply, smul_eq_mul] using hb

/-- Conditional exponential chord estimate using the actual first moment on
the same renewal pair law and retained-coordinate field. -/
theorem condExp_expAcceptedArrival_le_chord (j : Fin p.K) :
    mu[(fun b : B => expAcceptedArrival rate rewards C_star C_h u t control0 j b) | F_R] ≤ᵐ[mu]
      (fun b : B => 1 + ((Real.exp 1 - 1) * beta) *
        mu[(fun x : B => acceptedA j x) | F_R] b) := by
  let c : ℝ := (Real.exp 1 - 1) * beta
  have hAInt := ReferenceFirstCollectionRenewalAcceptedComplementMoments.integrable_acceptedA
    rate rewards C_star C_h u t j
  have hExpInt := integrable_expAcceptedArrival
    rate rewards C_star C_h u t control0 j
  have hScaledInt : Integrable (fun b : B => c * acceptedA j b) mu := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hAInt.const_mul c
  have hChordInt : Integrable (fun b : B => 1 + c * acceptedA j b) mu :=
    (integrable_const (1 : ℝ)).add hScaledInt
  have hPointwise : ∀ b : B,
      expAcceptedArrival rate rewards C_star C_h u t control0 j b ≤
        1 + c * acceptedA j b := by
    intro b
    have hA := ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA_bounds
      rate rewards C_star C_h u t b j
    have hscaled_nonneg : 0 ≤ beta * acceptedA j b :=
      mul_nonneg (le_of_lt (beta_pos rate)) hA.1
    have hscaled_le := beta_mul_acceptedA_le_one
      rate rewards C_star C_h u t j b
    have hchord := RecordedRoundMoments.exp_le_unit_chord hscaled_nonneg hscaled_le
    change Real.exp (beta * acceptedA j b) ≤ _
    calc
      Real.exp (beta * acceptedA j b) ≤
          1 + (Real.exp 1 - 1) * (beta * acceptedA j b) := hchord
      _ = 1 + c * acceptedA j b := by dsimp [c]; ring
  have hmono := condExp_mono (m := F_R) hExpInt hChordInt
    (Filter.Eventually.of_forall hPointwise)
  have hAdd := condExp_add (integrable_const (1 : ℝ)) hScaledInt F_R
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hConst := condExp_const (μ := mu) hdom (1 : ℝ)
  have hSmul := condExp_real_const_mul rate rewards C_star C_h u t control0 c
    (fun b : B => acceptedA j b)
  have hChordEq : (fun b : B => 1 + c * acceptedA j b) =
      (fun _ : B => (1 : ℝ)) + (fun b : B => c * acceptedA j b) := by
    funext b
    rfl
  have hChordCE :
      mu[(fun b : B => 1 + c * acceptedA j b) | F_R] =ᵐ[mu]
        (fun b : B => 1 + c * mu[(fun x : B => acceptedA j x) | F_R] b) := by
    calc
      mu[(fun b : B => 1 + c * acceptedA j b) | F_R] =ᵐ[mu]
          mu[(fun _ : B => (1 : ℝ)) + (fun b : B => c * acceptedA j b) | F_R] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun b => congrFun hChordEq b)
      _ =ᵐ[mu] mu[(fun _ : B => (1 : ℝ)) | F_R] +
          mu[(fun b : B => c * acceptedA j b) | F_R] := hAdd
      _ =ᵐ[mu] (fun b : B =>
          1 + c * mu[(fun x : B => acceptedA j x) | F_R] b) := by
        filter_upwards [hSmul] with b hsmul
        have hconst := congrFun hConst b
        simp only [Pi.add_apply, hconst, hsmul]
  exact Filter.EventuallyLE.trans hmono hChordCE.le

/-- The exponential service penalty dominates the unit-interval chord factor.
-/
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
retained set and one off that set. -/
theorem expRetainedIncrement_indicator_identity (j : Fin p.K) (b : B) :
    expRetainedIncrement rate rewards C_star C_h u t control0 j b =
      Real.exp (-4 * beta) *
          Set.indicator G
            (fun x : B => expAcceptedArrival rate rewards C_star C_h u t control0 j x) b +
        Set.indicator Gᶜ (fun _ : B => (1 : ℝ)) b := by
  by_cases hb : b ∈ G
  · have hsplit : Real.exp (beta * (acceptedA j b - 4)) =
        Real.exp (-4 * beta) * Real.exp (beta * acceptedA j b) := by
      rw [show beta * (acceptedA j b - 4) = (-4 * beta) + beta * acceptedA j b by ring,
        Real.exp_add]
    simp [expRetainedIncrement, retainedIncrement, expAcceptedArrival, hb, hsplit]
  · simp [expRetainedIncrement, retainedIncrement, expAcceptedArrival, hb]

/-- Conditional expectation of the actual retained-increment exponential is
at most one on the same field and original unnormalized measure. -/
theorem expRetainedIncrement_condExp_le_one (j : Fin p.K) :
    mu[(fun b : B => expRetainedIncrement rate rewards C_star C_h u t control0 j b) | F_R] ≤ᵐ[mu]
      (fun _ : B => 1) := by
  let f : B → ℝ := fun b => expAcceptedArrival rate rewards C_star C_h u t control0 j b
  let fG : B → ℝ := Set.indicator G f
  let fGc : B → ℝ := Set.indicator Gᶜ (fun _ : B => (1 : ℝ))
  let cExp : ℝ := Real.exp (-4 * beta)
  have hGfield := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  rcases hGfield with ⟨S, hS, hpre⟩
  have hGfield' : MeasurableSet[F_R] G := ⟨S, hS, hpre⟩
  have hR : Measurable R := (comap_measurable R).mono hdom le_rfl
  have hGambient : MeasurableSet G := by
    rw [← hpre]
    exact hS.preimage hR
  have hfInt : Integrable f mu := by
    simpa [f] using integrable_expAcceptedArrival
      rate rewards C_star C_h u t control0 j
  have hfGInt : Integrable fG mu := by
    simpa [fG] using hfInt.indicator hGambient
  have hfGcInt : Integrable fGc mu := by
    simpa [fGc] using (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hcExpInt : Integrable (fun b : B => cExp * fG b) mu := hfGInt.const_mul cExp
  have hRetEq : (fun b : B => expRetainedIncrement
      rate rewards C_star C_h u t control0 j b) =
      (fun b : B => cExp * fG b + fGc b) := by
    funext b
    simpa [f, fG, fGc, cExp] using
      expRetainedIncrement_indicator_identity
        rate rewards C_star C_h u t control0 j b
  have hAdd := condExp_add hcExpInt hfGcInt F_R
  have hScale := condExp_real_const_mul rate rewards C_star C_h u t control0 cExp fG
  have hMask := condExp_indicator (μ := mu) hfInt hGfield'
  have hMaskComp := condExp_indicator (μ := mu) (integrable_const (1 : ℝ)) hGfield'.compl
  have hConst := condExp_const (μ := mu) hdom (1 : ℝ)
  have hCEdecomp :
      mu[(fun b : B => expRetainedIncrement
        rate rewards C_star C_h u t control0 j b) | F_R] =ᵐ[mu]
        (fun b : B => cExp * Set.indicator G
          (fun x : B => mu[f | F_R] x) b +
            Set.indicator Gᶜ (fun _ : B => 1) b) := by
    calc
      mu[(fun b : B => expRetainedIncrement
          rate rewards C_star C_h u t control0 j b) | F_R] =ᵐ[mu]
          mu[(fun b : B => cExp * fG b + fGc b) | F_R] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun b => congrFun hRetEq b)
      _ =ᵐ[mu] mu[(fun b : B => cExp * fG b) | F_R] +
          mu[fGc | F_R] := hAdd
      _ =ᵐ[mu] (fun b : B => cExp * mu[fG | F_R] b +
          mu[fGc | F_R] b) := by
        filter_upwards [hScale] with b hscale
        simpa only [Pi.add_apply] using
          congrArg (fun x : ℝ => x + mu[fGc | F_R] b) hscale
      _ =ᵐ[mu] (fun b : B => cExp * Set.indicator G
          (fun x : B => mu[f | F_R] x) b +
            Set.indicator Gᶜ (fun _ : B => 1) b) := by
        filter_upwards [hMask, hMaskComp] with b hG hGc
        rw [hG, hGc]
        rw [hConst]
  have hCEexpA := condExp_expAcceptedArrival_le_chord
    rate rewards C_star C_h u t control0 j
  have hCEacceptedA := acceptedA_condExp_le_one
    rate rewards C_star C_h u t control0 j
  have hcExpPos : 0 < cExp := by positivity
  have hcoeff : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) (le_of_lt (beta_pos rate))
  have hscalar := exp_neg_four_beta_chord_le_one rate
  filter_upwards [hCEdecomp, hCEexpA, hCEacceptedA] with b hdecomp hExpBound hABound
  rw [hdecomp]
  by_cases hb : b ∈ G
  · have hnot : b ∉ Gᶜ := by simpa using hb
    simp only [Set.indicator_of_mem hb, Set.indicator_of_notMem hnot, add_zero]
    calc
      cExp * mu[(fun x : B => expAcceptedArrival
          rate rewards C_star C_h u t control0 j x) | F_R] b ≤
          cExp * (1 + ((Real.exp 1 - 1) * beta) *
            mu[(fun x : B => acceptedA j x) | F_R] b) :=
        mul_le_mul_of_nonneg_left hExpBound hcExpPos.le
      _ ≤ cExp * (1 + ((Real.exp 1 - 1) * beta)) := by
        apply mul_le_mul_of_nonneg_left _ hcExpPos.le
        have hmul := mul_le_mul_of_nonneg_left hABound hcoeff
        linarith
      _ ≤ 1 := by simpa [cExp] using hscalar
  · have hmem : b ∈ Gᶜ := by simpa using hb
    simp [Set.indicator_of_notMem hb, Set.indicator_of_mem hmem]

/-- Integrating the conditional exponential bound adds the mass of this same
finite unnormalized pair law, including when its mass is zero. -/
theorem integral_expRetainedIncrement_le_mass (j : Fin p.K) :
    (∫ b : B,
      expRetainedIncrement rate rewards C_star C_h u t control0 j b ∂mu) ≤
      (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
        rate rewards C_star C_h u t).real Set.univ := by
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hconstInt : Integrable (fun _ : B => (1 : ℝ)) mu := integrable_const _
  calc
    (∫ b : B,
      expRetainedIncrement rate rewards C_star C_h u t control0 j b ∂mu) =
        ∫ b : B,
          mu[(fun x : B =>
            expRetainedIncrement rate rewards C_star C_h u t control0 j x) | F_R] b ∂mu :=
      (integral_condExp hdom).symm
    _ ≤ ∫ _ : B, (1 : ℝ) ∂mu :=
      integral_mono_ae integrable_condExp hconstInt
        (expRetainedIncrement_condExp_le_one
          rate rewards C_star C_h u t control0 j)
    _ = (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
        rate rewards C_star C_h u t).real Set.univ := by
      simp only [integral_const, smul_eq_mul, mul_one]

/-- On one simultaneous support, the actual call and recording identity from
the accepted-complement producer retains every one of its fields and appends
the literal increment's normalized actual accepted-record identity. -/
theorem ae_actual_retainedIncrement_acceptedRecord_identity :
    ∀ᵐ b : B ∂mu,
      ∃ d : ReferenceFirstCollectionRenewalAcceptedComplementMoments.ActualCall
          rate rewards C_star C_h u t b,
        ∃ recording : CoordinatorRecordingOperation.Output p,
          (d.record = ReferenceFirstCollectionRenewalIncomingQueuePrefix.callRecord
              rate rewards C_star C_h u t b.2 ∧
            d.record.output.coordinator.recording = some recording ∧
            ReferenceFirstCollectionRenewalComplementMoments.v
                rate rewards C_star C_h u t b =
              AssignmentScoreReconstruction.currentWeight d.out ∧
            (∀ j : Fin p.K, recording.gateArm = some j ↔
              b ∈ ReferenceFirstCollectionRenewalGateCoefficient.gateEvent
                rate rewards C_star C_h u t j) ∧
            (∀ j : Fin p.K, recording.gateArm = some j →
              PublicDiscreteDraws.slotDraw (d.record.input.row.2 d.record.input.time).1 =
                  PublicDiscreteDraws.dataSlot ∧
              PublicDiscreteDraws.recorderSourceDraw p.two_le_m p.m_lt_K
                  (d.record.input.row.2 d.record.input.time).1 =
                ActiveRoundActions.coordinator p.two_le_m ∧
              d.record.output.preparation.feedback.feedback
                  (ActiveRoundActions.coordinator p.two_le_m) = rewards t j ∧
              d.record.output.preparation.coordinatorObservation = rewards t j ∧
              (d.record.output.preparation.feedback.observations
                  (ActiveRoundActions.coordinator p.two_le_m)).val.val =
                RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)) ∧
            ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                rate rewards C_star C_h u t b.2).overflow = false ↔
              ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
                  rate rewards C_star C_h u t b.2 <
                UnstoppedRecordedQueueComparison.firstOverflowPrefix
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
                    rate rewards C_star C_h u t b.2)) ∧
            (∀ j : Fin p.K,
              acceptedA j b =
                if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                    rate rewards C_star C_h u t b.2).overflow then 0
                else if recording.gateArm = some j then
                  (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ))
                else 0) ∧
            (∀ j : Fin p.K,
              b ∈ ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
                  rate rewards C_star C_h u t control0 →
              (AssignmentScoreReconstruction.sourceScore d.out j,
                AssignmentScoreReconstruction.initialQueue d.out j) =
                  (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                    rate rewards C_star C_h u t b.2).registers j) ∧
            (∀ j : Fin p.K,
              acceptedA j b =
                ((RecordedQueueRun.acceptedRecord
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                    rate rewards C_star C_h u t b.2)
                  (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
                    rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
                  (rate.eta.val * (D p : ℝ)))) ∧
          (∀ j : Fin p.K,
            retainedIncrement rate rewards C_star C_h u t control0 j b =
              if (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                    rate rewards C_star C_h u t b.2).overflow = false then
                ((RecordedQueueRun.acceptedRecord
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
                    rate rewards C_star C_h u t b.2)
                  (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
                    rate rewards C_star C_h u t b d recording) j).2 : ℝ) /
                    (rate.eta.val * (D p : ℝ)) - 4
              else 0) := by
  filter_upwards [
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.ae_actual_recorder_acceptedRecord_identity
      rate rewards C_star C_h u t control0,
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.ae_actual_strict_past_identification
      rate rewards C_star C_h u t control0] with b hactual hretained
  rcases hactual with ⟨d, recording, hcall, hrecording, hweight, hgate, hfeedback,
    hstrict, hraw, hregisters, hacceptedRecord⟩
  have hGoverflow : b ∈ G ↔
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = false := by
    exact hretained.trans hstrict.symm
  refine ⟨d, recording, ?_, ?_⟩
  · exact ⟨hcall, hrecording, hweight, hgate, hfeedback, hstrict, hraw,
      hregisters, hacceptedRecord⟩
  · intro j
    by_cases hflag :
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2).overflow = false
    · rw [ite_eq_left hflag]
      have hmem : b ∈ G := hGoverflow.mpr hflag
      rw [retainedIncrement_eq_acceptedA_sub_four_of_mem_G
        rate rewards C_star C_h u t control0 j b hmem, hacceptedRecord j]
    · rw [ite_eq_right hflag]
      have hnotmem : b ∉ G := by
        intro hmem
        exact hflag (hGoverflow.mp hmem)
      exact retainedIncrement_eq_zero_of_not_mem_G
        rate rewards C_star C_h u t control0 j b hnotmem

end Bandits.Support.ReferenceFirstCollectionRenewalExponentialIncrement

end
