/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw
public import Bandits.Support.ReferenceFirstCollectionRenewalExponentialQueueStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Whole-marker first-renewal exponential queue step

This module exponentiates the actual whole-cell accepted arrival and the
post-readout of the same whole numerical prefix. Followers remain in the
recorded marker, and the incoming queue, unnormalized pair law, and retained
control field are the existing first-renewal objects.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalWholeExponentialQueueStep

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev Pair {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
abbrev IncomingReadout (p : Parameters) :=
  (Fin p.K → ℕ × ℕ) × (Bool × (Fin p.K → List (Bool × ℕ)))

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalBaseMeasurableSpace :
    MeasurableSpace
      (ReferenceFirstCollectionRenewalControlFactor.RenewalBase
        rate rewards C_star C_h u t) := by
  change MeasurableSpace
    (ReferenceFirstCollectionRenewalControlFactor.Source
        rate rewards C_star C_h u t ×
      ReferenceFirstCollectionRenewalControlFactor.AuxiliaryArray p)
  infer_instance

local notation "B" => Pair rate rewards C_star C_h u t
local notation "Z" => ReferenceFirstCollectionRenewalSourceCurrentPrefix.Source
  rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "R" =>
  ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap R
  (inferInstance : MeasurableSpace
    (ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p))
local notation "G" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "fullA" =>
  ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.fullAcceptedA
    rate rewards C_star C_h u t

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

/-- The retained increment of the actual whole accepted marker, including
enabled zero-arrival service and excluding every update after incoming stop. -/
def fullRetainedIncrement (j : Fin p.K) (b : B) : ℝ :=
  Set.indicator G (fun b => fullA j b - 4) b

/-- Exponential of the actual whole accepted arrival. -/
def fullExpAcceptedArrival (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta * fullA j b)

/-- Exponential of the retained actual whole-marker increment. -/
def fullExpRetainedIncrement (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta * fullRetainedIncrement rate rewards C_star C_h u t control0 j b)

/-- Exponential of the actual whole post-readout queue register. The
projection order is the state readout's registers, then arm, then backlog. -/
def fullXPlus (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta *
    ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t b.2).1 j).2 : ℝ) / (rate.n : ℝ)))

private theorem retainedField_le : F_R ≤ (inferInstance : MeasurableSpace B) :=
  ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0

private theorem measurableSet_G_R_ambient : MeasurableSet G := by
  have hfield := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  rcases hfield with ⟨S, hS, hpre⟩
  have hR : Measurable R := (comap_measurable R).mono hdom le_rfl
  rw [← hpre]
  exact hS.preimage hR

private theorem beta_pos : 0 < beta :=
  CanonicalRecordingRates.beta_pos p rate.eta.property

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

private theorem integrable_of_bounded_measurable {f : B → ℝ}
    (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ b, ‖f b‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : B => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with b
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound b

/-- The whole marker's accepted floor is bounded by the actual feasible
recording rate, giving the sharper source envelope `1 / beta`. -/
theorem fullAcceptedA_bounds (j : Fin p.K) (b : B) :
    0 ≤ fullA j b ∧ fullA j b ≤ 1 / beta := by
  have hn : 0 < (rate.n : ℝ) := Nat.cast_pos.mpr
    (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
  cases ho : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow with
  | true =>
    rw [ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.fullAcceptedA_eq
      rate rewards C_star C_h u t j b, ho]
    constructor
    · norm_num
    · exact div_nonneg (by norm_num) (beta_pos rate).le
  | false =>
    have hnum := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_numerical
      rate rewards C_star C_h u t b.2
    obtain ⟨_, selected, _, hrewardEq, hrate⟩ := hnum
    have hrateLower : beta ≤ (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
        rate rewards C_star C_h u t b.2).rate j := by
      rw [hrate]
      exact selected.view.payload.beta_le_rate j
    have hreward := RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) (rewards t j)
    have hreward_le :
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2).reward j ≤ 1 := by
      rw [hrewardEq]
      exact hreward.2
    have hratePos : 0 < (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
        rate rewards C_star C_h u t b.2).rate j :=
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
        rate rewards C_star C_h u t b.2).rate_pos j
    have hratio : ((rate.n : ℝ) *
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2).reward j) /
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2).rate j ≤ (rate.n : ℝ) / beta := by
      have hrewardRate :
          (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
            rate rewards C_star C_h u t b.2).reward j /
            (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
              rate rewards C_star C_h u t b.2).rate j ≤ 1 / beta := by
        calc
          _ ≤ 1 / (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
                rate rewards C_star C_h u t b.2).rate j :=
            div_le_div_of_nonneg_right hreward_le hratePos.le
          _ ≤ 1 / beta := one_div_le_one_div_of_le (beta_pos rate) hrateLower
      calc
        _ = (rate.n : ℝ) *
            ((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
              rate rewards C_star C_h u t b.2).reward j /
              (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
                rate rewards C_star C_h u t b.2).rate j) := by ring
        _ ≤ (rate.n : ℝ) * (1 / beta) :=
          mul_le_mul_of_nonneg_left hrewardRate (Nat.cast_nonneg _)
        _ = (rate.n : ℝ) / beta := by ring
    have hfloor' : (Nat.floor (((rate.n : ℝ) *
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2).reward j) /
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2).rate j) : ℝ) ≤
        (rate.n : ℝ) / beta := by
      have harg : 0 ≤ ((rate.n : ℝ) *
          (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
            rate rewards C_star C_h u t b.2).reward j) /
          (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
            rate rewards C_star C_h u t b.2).rate j :=
        div_nonneg (mul_nonneg hn.le (by
          rw [hrewardEq]
          exact hreward.1)) hratePos.le
      exact (Nat.floor_le harg).trans hratio
    by_cases hrecorded :
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2).recordedArm = some j
    · rw [ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.fullAcceptedA_eq
        rate rewards C_star C_h u t j b, ho]
      rw [RecordedQueueRun.quantizedArrival_eq_floor
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2) j hrecorded]
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hn.le
      · calc
          _ ≤ ((rate.n : ℝ) / beta) / (rate.n : ℝ) :=
            div_le_div_of_nonneg_right hfloor' hn.le
          _ = 1 / beta := by field_simp [ne_of_gt hn]
    · have hA0 : fullA j b = 0 := by
        rw [ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.fullAcceptedA_eq
          rate rewards C_star C_h u t j b, ho]
        simp [RecordedQueueRun.quantizedArrival, hrecorded]
      rw [hA0]
      constructor
      · norm_num
      · exact one_div_nonneg.mpr (beta_pos rate).le

/-- The exponent of the full accepted arrival lies in the source unit interval. -/
theorem beta_mul_fullAcceptedA_le_one (j : Fin p.K) (b : B) :
    beta * fullA j b ≤ 1 := by
  have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
  simpa only [mul_comm] using (le_div_iff₀ (beta_pos rate)).mp hA.2

private theorem fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
    (j : Fin p.K) (b : B) (hb : b ∈ G) :
    fullRetainedIncrement rate rewards C_star C_h u t control0 j b = fullA j b - 4 := by
  simp [fullRetainedIncrement, hb]

private theorem fullRetainedIncrement_eq_zero_of_not_mem_G
    (j : Fin p.K) (b : B) (hb : b ∉ G) :
    fullRetainedIncrement rate rewards C_star C_h u t control0 j b = 0 := by
  simp [fullRetainedIncrement, hb]

private theorem beta_mul_fullRetainedIncrement_le_one (j : Fin p.K) (b : B) :
    beta * fullRetainedIncrement rate rewards C_star C_h u t control0 j b ≤ 1 := by
  by_cases hb : b ∈ G
  · rw [fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    calc
      beta * (fullA j b - 4) = beta * fullA j b - 4 * beta := by ring
      _ ≤ beta * fullA j b := by nlinarith [beta_pos rate]
      _ ≤ 1 := beta_mul_fullAcceptedA_le_one rate rewards C_star C_h u t j b
  · rw [fullRetainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    norm_num

private theorem fullRetainedIncrement_bounds (j : Fin p.K) (b : B) :
    -4 ≤ fullRetainedIncrement rate rewards C_star C_h u t control0 j b ∧
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b ≤ 1 / beta := by
  by_cases hb : b ∈ G
  · rw [fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
    constructor <;> linarith
  · rw [fullRetainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hb]
    constructor
    · norm_num
    · exact div_nonneg (by norm_num) (beta_pos rate).le

/-- Ambient measurability of the literal retained whole-marker increment. -/
theorem measurable_fullRetainedIncrement (j : Fin p.K) :
    Measurable (fun b : B =>
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b) := by
  have hGfield := ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
    rate rewards C_star C_h u t control0
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  rcases hGfield with ⟨S, hS, hpre⟩
  have hR : Measurable R := (comap_measurable R).mono hdom le_rfl
  have hGambient : MeasurableSet G := by
    rw [← hpre]
    exact hS.preimage hR
  exact (ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.measurable_fullAcceptedA
    rate rewards C_star C_h u t j).sub_const 4 |>.indicator hGambient

/-- Ambient measurability of the whole-marker exponential increment. -/
theorem measurable_fullExpRetainedIncrement (j : Fin p.K) :
    Measurable (fun b : B =>
      fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b) := by
  have hinc := measurable_fullRetainedIncrement rate rewards C_star C_h u t control0 j
  have hscaled : Measurable (fun b : B => beta *
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b) :=
    (measurable_const : Measurable (fun _ : B => beta)).mul hinc
  simpa [fullExpRetainedIncrement] using hscaled.exp

/-- Ambient measurability of the full accepted-arrival exponential. -/
theorem measurable_fullExpAcceptedArrival (j : Fin p.K) :
    Measurable (fun b : B => fullExpAcceptedArrival rate rewards C_star C_h u t j b) := by
  have hA := ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.measurable_fullAcceptedA
    rate rewards C_star C_h u t j
  have hscaled : Measurable (fun b : B => beta * fullA j b) :=
    (measurable_const : Measurable (fun _ : B => beta)).mul hA
  simpa [fullExpAcceptedArrival] using hscaled.exp

/-- Ambient measurability of the actual whole post-readout exponential. -/
theorem measurable_fullXPlus (j : Fin p.K) :
    Measurable (fun b : B => fullXPlus rate rewards C_star C_h u t j b) := by
  have hsource : Measurable (fun b : B => b.2) := measurable_snd
  have hpost :=
    (ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholePostReadout
      rate rewards C_star C_h u t).comp hsource
  have hreg := measurable_pi_apply j |>.comp (measurable_fst.comp hpost)
  have hback : Measurable (fun b : B =>
      ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t b.2).1 j).2 : ℝ))) :=
    (measurable_of_countable fun n : ℕ => (n : ℝ)).comp
      (measurable_snd.comp hreg)
  have hscaled : Measurable (fun b : B => beta *
      ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t b.2).1 j).2 : ℝ) / (rate.n : ℝ))) :=
    (measurable_const : Measurable (fun _ : B => beta)).mul (hback.div_const _)
  simpa [fullXPlus] using hscaled.exp

/-- The full accepted first moment is at most one, using the whole-marker
conditional identity and the quantized scalar first-moment estimate. -/
theorem fullAcceptedA_condExp_le_one (j : Fin p.K) :
    mu[(fun b : B => fullA j b) | F_R] ≤ᵐ[mu] (fun _ : B => 1) := by
  have hce := ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.condExp_fullAcceptedA
    rate rewards C_star C_h u t control0 j
  have hprod : ∀ b : B,
      ReferenceFirstCollectionRenewalComplementMoments.xi
          rate rewards C_star C_h u t b j *
        ReferenceFirstCollectionRenewalComplementMoments.q
          rate rewards C_star C_h u t b j ≤ 1 := by
    intro b
    let xi := ReferenceFirstCollectionRenewalComplementMoments.xi
      rate rewards C_star C_h u t b j
    let q := ReferenceFirstCollectionRenewalComplementMoments.q
      rate rewards C_star C_h u t b j
    let r := ReferenceFirstCollectionRenewalComplementMoments.r rewards t j
    have hxi : 0 < xi := by
      dsimp [xi, ReferenceFirstCollectionRenewalComplementMoments.xi]
      exact CanonicalRecordingRates.xi_pos p rate.eta.property
        (ReferenceFirstCollectionRenewalComplementMoments.v
          rate rewards C_star C_h u t b) j
    have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp [r, ReferenceFirstCollectionRenewalComplementMoments.r]
      exact RealRewardGridCount.realRewardGridValue_mem_Icc
        (D p) (D_pos p) (rewards t j)
    calc
      xi * q ≤ r := by
        dsimp [xi, q, r, ReferenceFirstCollectionRenewalComplementMoments.xi,
          ReferenceFirstCollectionRenewalComplementMoments.q,
          ReferenceFirstCollectionRenewalComplementMoments.r]
        exact QuantizedRecordingMoments.quantizedValue_firstMoment_le
          (D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val
            (ReferenceFirstCollectionRenewalComplementMoments.v
              rate rewards C_star C_h u t b) j)
          (RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j))
          (D_pos p) rate.eta.property hxi hr
      _ ≤ 1 := hr.2
  filter_upwards [hce] with b hb
  rw [hb]
  by_cases hg : b ∈ G
  · simpa [Set.indicator_of_mem hg] using hprod b
  · simp [Set.indicator_of_notMem hg]

/-- The actual whole-marker arrival exponential is bounded by `exp 1`. -/
theorem fullExpAcceptedArrival_bounds (j : Fin p.K) (b : B) :
    1 ≤ fullExpAcceptedArrival rate rewards C_star C_h u t j b ∧
      fullExpAcceptedArrival rate rewards C_star C_h u t j b ≤ Real.exp 1 := by
  have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
  have hβ := beta_pos rate
  have hnonneg : 0 ≤ beta * fullA j b := mul_nonneg hβ.le hA.1
  have hle := beta_mul_fullAcceptedA_le_one rate rewards C_star C_h u t j b
  constructor
  · apply Real.one_le_exp_iff.mpr
    exact hnonneg
  · rw [fullExpAcceptedArrival]
    exact Real.exp_le_exp_of_le hle

/-- The bounded whole accepted-arrival exponential is integrable on the
original finite pair law. -/
theorem integrable_fullExpAcceptedArrival (j : Fin p.K) :
    Integrable (fun b : B => fullExpAcceptedArrival rate rewards C_star C_h u t j b) mu := by
  apply integrable_of_bounded_measurable rate rewards C_star C_h u t
    (measurable_fullExpAcceptedArrival rate rewards C_star C_h u t j) (Real.exp 1)
  · positivity
  · intro b
    have hb := fullExpAcceptedArrival_bounds rate rewards C_star C_h u t j b
    rw [Real.norm_of_nonneg (le_trans (by norm_num) hb.1)]
    exact hb.2

/-- Conditional chord bound for the whole-marker exponential, using the
actual whole accepted first moment on the retained field. -/
theorem condExp_fullExpAcceptedArrival_le_chord (j : Fin p.K) :
    mu[(fun b : B => fullExpAcceptedArrival rate rewards C_star C_h u t j b) | F_R] ≤ᵐ[mu]
      (fun b : B => 1 + ((Real.exp 1 - 1) * beta) *
        mu[(fun x : B => fullA j x) | F_R] b) := by
  let c : ℝ := (Real.exp 1 - 1) * beta
  have hAInt := ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.integrable_fullAcceptedA
    rate rewards C_star C_h u t j
  have hExpInt := integrable_fullExpAcceptedArrival
    rate rewards C_star C_h u t j
  have hScaledInt : Integrable (fun b : B => c * fullA j b) mu := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hAInt.const_mul c
  have hChordInt : Integrable (fun b : B => 1 + c * fullA j b) mu :=
    (integrable_const (1 : ℝ)).add hScaledInt
  have hPointwise : ∀ b : B,
      fullExpAcceptedArrival rate rewards C_star C_h u t j b ≤ 1 + c * fullA j b := by
    intro b
    have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
    have hscaled_nonneg : 0 ≤ beta * fullA j b :=
      mul_nonneg (le_of_lt (beta_pos rate)) hA.1
    have hscaled_le := beta_mul_fullAcceptedA_le_one rate rewards C_star C_h u t j b
    have hchord := RecordedRoundMoments.exp_le_unit_chord hscaled_nonneg hscaled_le
    change Real.exp (beta * fullA j b) ≤ _
    calc
      Real.exp (beta * fullA j b) ≤
          1 + (Real.exp 1 - 1) * (beta * fullA j b) := hchord
      _ = 1 + c * fullA j b := by dsimp [c]; ring
  have hmono := condExp_mono (m := F_R) hExpInt hChordInt
    (Filter.Eventually.of_forall hPointwise)
  have hAdd := condExp_add (integrable_const (1 : ℝ)) hScaledInt F_R
  have hdom := ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0
  have hConst := condExp_const (μ := mu) hdom (1 : ℝ)
  have hSmul := condExp_real_const_mul rate rewards C_star C_h u t control0 c
    (fun b : B => fullA j b)
  have hChordEq : (fun b : B => 1 + c * fullA j b) =
      (fun _ : B => (1 : ℝ)) + (fun b : B => c * fullA j b) := by
    funext b
    rfl
  have hChordCE :
      mu[(fun b : B => 1 + c * fullA j b) | F_R] =ᵐ[mu]
        (fun b : B => 1 + c * mu[(fun x : B => fullA j x) | F_R] b) := by
    calc
      mu[(fun b : B => 1 + c * fullA j b) | F_R] =ᵐ[mu]
          mu[(fun _ : B => (1 : ℝ)) + (fun b : B => c * fullA j b) | F_R] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun b => congrFun hChordEq b)
      _ =ᵐ[mu] mu[(fun _ : B => (1 : ℝ)) | F_R] +
          mu[(fun b : B => c * fullA j b) | F_R] := hAdd
      _ =ᵐ[mu] (fun b : B => 1 + c * mu[(fun x : B => fullA j x) | F_R] b) := by
        filter_upwards [hSmul] with b hsmul
        have hconst := congrFun hConst b
        simp only [Pi.add_apply, hconst, hsmul]
  exact Filter.EventuallyLE.trans hmono hChordCE.le

/-- The exponential service penalty dominates the whole-marker unit-interval
chord factor. -/
theorem exp_neg_four_beta_chord_le_one :
    Real.exp (-4 * beta) * (1 + (Real.exp 1 - 1) * beta) ≤ 1 :=
  ReferenceFirstCollectionRenewalExponentialIncrement.exp_neg_four_beta_chord_le_one
    rate

/-- The whole retained increment exponential has a retained/off-retained
indicator decomposition. -/
theorem fullExpRetainedIncrement_indicator_identity (j : Fin p.K) (b : B) :
    fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b =
      Real.exp (-4 * beta) *
          Set.indicator G
            (fun x : B => fullExpAcceptedArrival rate rewards C_star C_h u t j x) b +
        Set.indicator Gᶜ (fun _ : B => (1 : ℝ)) b := by
  by_cases hb : b ∈ G
  · have hsplit : Real.exp (beta * (fullA j b - 4)) =
        Real.exp (-4 * beta) * Real.exp (beta * fullA j b) := by
      rw [show beta * (fullA j b - 4) = (-4 * beta) + beta * fullA j b by ring,
        Real.exp_add]
    simp [fullExpRetainedIncrement, fullRetainedIncrement,
      fullExpAcceptedArrival, Set.indicator, hb, hsplit]
  · simp [fullExpRetainedIncrement, fullRetainedIncrement,
      Set.indicator, hb]

/-- Conditional expectation of the full retained exponential is at most one
on the same pair law and retained-control field. -/
theorem fullExpRetainedIncrement_condExp_le_one (j : Fin p.K) :
    mu[(fun b : B => fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b) | F_R] ≤ᵐ[mu]
      (fun _ : B => 1) := by
  let f : B → ℝ := fun b => fullExpAcceptedArrival rate rewards C_star C_h u t j b
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
    simpa [f] using integrable_fullExpAcceptedArrival
      rate rewards C_star C_h u t j
  have hfGInt : Integrable fG mu := by
    simpa [fG] using hfInt.indicator hGambient
  have hfGcInt : Integrable fGc mu := by
    simpa [fGc] using (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hcExpInt : Integrable (fun b : B => cExp * fG b) mu := hfGInt.const_mul cExp
  have hRetEq : (fun b : B => fullExpRetainedIncrement
      rate rewards C_star C_h u t control0 j b) =
      (fun b : B => cExp * fG b + fGc b) := by
    funext b
    simpa [f, fG, fGc, cExp] using
      fullExpRetainedIncrement_indicator_identity
        rate rewards C_star C_h u t control0 j b
  have hAdd := condExp_add hcExpInt hfGcInt F_R
  have hScale := condExp_real_const_mul rate rewards C_star C_h u t control0 cExp fG
  have hMask := condExp_indicator (μ := mu) hfInt hGfield'
  have hMaskComp := condExp_indicator (μ := mu)
    (integrable_const (1 : ℝ)) hGfield'.compl
  have hConst := condExp_const (μ := mu) hdom (1 : ℝ)
  have hCEdecomp :
      mu[(fun b : B => fullExpRetainedIncrement
        rate rewards C_star C_h u t control0 j b) | F_R] =ᵐ[mu]
        (fun b : B => cExp * Set.indicator G
          (fun x : B => mu[f | F_R] x) b +
            Set.indicator Gᶜ (fun _ : B => 1) b) := by
    calc
      mu[(fun b : B => fullExpRetainedIncrement
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
  have hCEexpA := condExp_fullExpAcceptedArrival_le_chord
    rate rewards C_star C_h u t control0 j
  have hCEacceptedA := fullAcceptedA_condExp_le_one
    rate rewards C_star C_h u t control0 j
  have hcExpPos : 0 < cExp := by positivity
  have hcoeff : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he := Real.exp_one_gt_two
    exact mul_nonneg (by linarith) (le_of_lt (beta_pos rate))
  have hscalar := exp_neg_four_beta_chord_le_one
    rate
  filter_upwards [hCEdecomp, hCEexpA, hCEacceptedA] with b hdecomp hExpBound hABound
  rw [hdecomp]
  by_cases hb : b ∈ G
  · have hnot : b ∉ Gᶜ := by simpa using hb
    simp only [Set.indicator_of_mem hb, Set.indicator_of_notMem hnot, add_zero]
    calc
      cExp * mu[(fun x : B => fullExpAcceptedArrival rate rewards C_star C_h u t j x) | F_R] b ≤
          cExp * (1 + ((Real.exp 1 - 1) * beta) *
            mu[(fun x : B => fullA j x) | F_R] b) :=
        mul_le_mul_of_nonneg_left hExpBound hcExpPos.le
      _ ≤ cExp * (1 + ((Real.exp 1 - 1) * beta)) := by
        apply mul_le_mul_of_nonneg_left _ hcExpPos.le
        have hmul := mul_le_mul_of_nonneg_left hABound hcoeff
        linarith
      _ ≤ 1 := by simpa [cExp] using hscalar
  · have hmem : b ∈ Gᶜ := by simpa using hb
    simp [Set.indicator_of_notMem hb, Set.indicator_of_mem hmem]

private theorem normalized_transition_backlog (n score backlog arrival : ℕ)
    (hn : 0 < n) :
    ((QueueReplay.transition (4 * n) (score, backlog) (true, arrival)).2 : ℝ) /
        (n : ℝ) =
      max ((backlog : ℝ) / (n : ℝ) + (arrival : ℝ) / (n : ℝ) - 4) 0 := by
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  unfold QueueReplay.transition
  simp only [↓reduceIte]
  by_cases hcap : 4 * n ≤ backlog + arrival
  · rw [Nat.min_eq_left hcap, Nat.cast_sub hcap, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat]
    have hreal : 4 * (n : ℝ) ≤ (backlog : ℝ) + (arrival : ℝ) := by
      exact_mod_cast hcap
    have hnonneg : 0 ≤ (backlog : ℝ) / (n : ℝ) +
        (arrival : ℝ) / (n : ℝ) - 4 := by
      rw [← add_div]
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hnR).2
      nlinarith
    rw [max_eq_left hnonneg]
    field_simp [ne_of_gt hnR]
  · have hlt : backlog + arrival < 4 * n := lt_of_not_ge hcap
    rw [Nat.min_eq_right (Nat.le_of_lt hlt), Nat.sub_self]
    have hreal : (backlog : ℝ) + (arrival : ℝ) < 4 * (n : ℝ) := by
      exact_mod_cast hlt
    have hnonpos : (backlog : ℝ) / (n : ℝ) +
        (arrival : ℝ) / (n : ℝ) - 4 ≤ 0 := by
      rw [← add_div]
      apply sub_nonpos.mpr
      apply (div_le_iff₀ hnR).2
      nlinarith
    rw [max_eq_right hnonpos]
    norm_num

/-- The actual whole post-readout backlog is the reflected update of the
whole accepted marker on the same whole numerical prefix. The incoming stop
preserves all registers, and the transition at the first overflowing cell is
still included. -/
theorem ae_fullPostBacklog_eq_reflected_increment :
    ∀ᵐ b : B ∂mu, ∀ j : Fin p.K,
      ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t b.2).1 j).2 : ℝ) / (rate.n : ℝ)) =
        max (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b +
          fullRetainedIncrement rate rewards C_star C_h u t control0 j b) 0 := by
  filter_upwards [ReferenceFirstCollectionRenewalExponentialQueueStep.ae_G_iff_incoming_noOverflow
      rate rewards C_star C_h u t control0] with b hG
  intro j
  let incoming := ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t b.2
  let cell := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
    rate rewards C_star C_h u t b.2
  let wholePost := ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
    rate rewards C_star C_h u t b.2
  cases hf : incoming.overflow with
  | false =>
    have hmem : b ∈ G := hG.mpr (by simpa [incoming] using hf)
    have henabled : cell.enabled = true := by
      simpa [cell] using
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_enabled
          rate rewards C_star C_h u t b.2)
    have hpostRegisters : wholePost.1 j =
        (QueueReplay.transition (4 * rate.n) (incoming.registers j)
          (true, RecordedQueueRun.quantizedArrival
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j)) := by
      change (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t b.2).1 j = _
      rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_projections]
      change (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2)).registers j = _
      simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
        ReferenceFirstLaunchNumericalCell.queueParameters,
        incoming, cell, hf, henabled]
    have hnorm := normalized_transition_backlog rate.n
      (incoming.registers j).1
      (incoming.registers j).2
      (RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j)
      (by simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos)
    have hinc := fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hmem
    have hA := ReferenceFirstCollectionRenewalWholeMarkerAcceptedLaw.fullAcceptedA_eq
      rate rewards C_star C_h u t j b
    have hnormA : ((RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell j : ℝ) /
          (rate.n : ℝ)) = fullA j b := by
      simpa [incoming, cell, hf] using hA.symm
    change ((wholePost.1 j).2 : ℝ) / (rate.n : ℝ) = _
    rw [hpostRegisters, hnorm]
    rw [hinc, hnormA]
    have hbEq : ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b =
        ((incoming.registers j).2 : ℝ) / (rate.n : ℝ) := by
      change (((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).registers j).2 : ℝ) / (rate.n : ℝ) = _
      rfl
    rw [← hbEq]
    apply congrArg (fun x : ℝ => max x 0)
    ring
  | true =>
    have hnot : b ∉ G := by
      intro hb
      have hfalse := hG.mp hb
      simp [incoming, hf] at hfalse
    have hpostRegisters : wholePost.1 j = incoming.registers j := by
      change (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t b.2).1 j = _
      rw [ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout_projections]
      change (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2)
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t b.2)).registers j = _
      simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
        ReferenceFirstLaunchNumericalCell.queueParameters, QueueReplay.transition,
        incoming, hf]
    change ((wholePost.1 j).2 : ℝ) / (rate.n : ℝ) = _
    rw [hpostRegisters]
    rw [fullRetainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hnot]
    have hback := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
      rate rewards C_star C_h u t control0 j b
    have hbEq : ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b =
        ((incoming.registers j).2 : ℝ) / (rate.n : ℝ) := by
      change (((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).registers j).2 : ℝ) / (rate.n : ℝ) = _
      rfl
    rw [add_zero, max_eq_left hback, ← hbEq]

private theorem beta_floor : 32 * rate.eta.val ≤ beta := by
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  rw [CanonicalRecordingRates.beta]
  calc
    32 * rate.eta.val = (32 * rate.eta.val) * 1 := by ring
    _ ≤ (32 * rate.eta.val) * (CanonicalRecordingRates.L_stab p : ℝ) :=
      mul_le_mul_of_nonneg_left hL
        (le_of_lt (mul_pos (by norm_num) rate.eta.property))

private theorem one_div_beta_le_Bcap :
    1 / beta ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0 := by
  have hη : 0 < rate.eta.val := rate.eta.property
  have hη32 : 0 < 32 * rate.eta.val := mul_pos (by norm_num) hη
  rw [ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap]
  exact one_div_le_one_div_of_le hη32 (beta_floor rate)

/-- The literal whole post-readout queue retains the global stopped-queue
envelope, including the first overflowing update and every later preserved
state. -/
theorem ae_fullPostBacklog_bounds (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      0 ≤ ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t b.2).1 j).2 : ℝ) / (rate.n : ℝ)) ∧
        ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t b.2).1 j).2 : ℝ) / (rate.n : ℝ)) ≤
          2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 := by
  filter_upwards [ae_fullPostBacklog_eq_reflected_increment
      rate rewards C_star C_h u t control0,
    ReferenceFirstCollectionRenewalExponentialQueueStep.ae_G_iff_incoming_noOverflow
      rate rewards C_star C_h u t control0] with b hrec hG
  have htwo := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_two_Bcap
    rate rewards C_star C_h u t control0 j b
  by_cases hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = false
  · have hmem : b ∈ G := hG.mpr hf
    have hpre := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_Bcap_of_noOverflow
      rate rewards C_star C_h u t control0 j b hf
    have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
    have hinc := fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hmem
    have hpost : max (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b +
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b) 0 ≤
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b + 1 / beta := by
      apply max_le
      · rw [hinc]
        linarith
      · exact add_nonneg
          (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
            rate rewards C_star C_h u t control0 j b)
          (one_div_nonneg.mpr (beta_pos rate).le)
    have hbound :
        max (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b +
          fullRetainedIncrement rate rewards C_star C_h u t control0 j b) 0 ≤
          2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 := by
      calc
        _ ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b + 1 / beta := hpost
        _ ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 +
              ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0 :=
          add_le_add hpre (one_div_beta_le_Bcap rate rewards C_star C_h u t control0)
        _ = 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 := by ring
    rw [hrec j]
    exact ⟨le_max_right _ _, hbound⟩
  · have htrue : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = true := by
      cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow <;> simp_all
    have hnot : b ∉ G := by
      intro hg
      have hfalse := hG.mp hg
      simp [htrue] at hfalse
    have hinc := fullRetainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hnot
    rw [hrec j, hinc]
    have hback := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
      rate rewards C_star C_h u t control0 j b
    simpa [add_zero, max_eq_left hback] using ⟨hback, htwo⟩

/-- Deterministic range of the retained whole-marker increment. -/
theorem fullRetainedIncrement_range (j : Fin p.K) (b : B) :
    -4 ≤ fullRetainedIncrement rate rewards C_star C_h u t control0 j b ∧
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b ≤ 1 / beta := by
  by_cases hg : b ∈ G
  · rw [fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hg]
    have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
    constructor <;> linarith
  · rw [fullRetainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hg]
    constructor
    · norm_num
    · exact (div_nonneg (by norm_num) (beta_pos rate).le)

/-- The literal retained whole-marker increment is integrable from its
deterministic envelope on the finite pair law. -/
theorem integrable_fullRetainedIncrement (j : Fin p.K) :
    Integrable (fun b : B => fullRetainedIncrement rate rewards C_star C_h u t control0 j b) mu := by
  let C : ℝ := 4 + 1 / beta
  have hrecip : 0 ≤ 1 / beta := div_nonneg (by norm_num) (beta_pos rate).le
  have hC : 0 ≤ C := by dsimp [C]; linarith
  apply integrable_of_bounded_measurable rate rewards C_star C_h u t
    (measurable_fullRetainedIncrement rate rewards C_star C_h u t control0 j) C hC
  intro b
  have hb := fullRetainedIncrement_bounds rate rewards C_star C_h u t control0 j b
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · change -(4 + 1 / beta) ≤
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b
    linarith
  · change fullRetainedIncrement rate rewards C_star C_h u t control0 j b ≤
      4 + 1 / beta
    linarith

/-- A deterministic envelope for the retained whole-marker exponential. -/
theorem fullExpRetainedIncrement_bounds (j : Fin p.K) (b : B) :
    0 < fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b ∧
      fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b ≤ Real.exp 1 := by
  have hinc : fullRetainedIncrement rate rewards C_star C_h u t control0 j b ≤ 1 / beta := by
    by_cases hg : b ∈ G
    · rw [fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
        rate rewards C_star C_h u t control0 j b hg]
      have hA := fullAcceptedA_bounds rate rewards C_star C_h u t j b
      linarith
    · rw [fullRetainedIncrement_eq_zero_of_not_mem_G
        rate rewards C_star C_h u t control0 j b hg]
      exact (div_nonneg (by norm_num) (beta_pos rate).le)
  constructor
  · change 0 < Real.exp (beta *
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b)
    exact Real.exp_pos _
  · change Real.exp (beta *
      fullRetainedIncrement rate rewards C_star C_h u t control0 j b) ≤ Real.exp 1
    apply Real.exp_le_exp_of_le
    calc
      beta * fullRetainedIncrement rate rewards C_star C_h u t control0 j b ≤
          beta * (1 / beta) := mul_le_mul_of_nonneg_left hinc (beta_pos rate).le
      _ = 1 := by field_simp [ne_of_gt (beta_pos rate)]

/-- Integrability of the retained whole-marker exponential follows from its
uniform envelope and the finite unnormalized pair law. -/
theorem integrable_fullExpRetainedIncrement (j : Fin p.K) :
    Integrable
      (fun b : B => fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_bounded_measurable rate rewards C_star C_h u t
    (measurable_fullExpRetainedIncrement rate rewards C_star C_h u t control0 j)
    (Real.exp 1)
  · positivity
  · intro b
    have hb := fullExpRetainedIncrement_bounds rate rewards C_star C_h u t control0 j b
    rw [Real.norm_of_nonneg hb.1.le]
    exact hb.2

/-- Almost everywhere deterministic envelope of the actual full post queue's
exponential, inherited from its real queue transition. -/
theorem ae_fullXPlus_bounds (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      1 ≤ fullXPlus rate rewards C_star C_h u t j b ∧
        fullXPlus rate rewards C_star C_h u t j b ≤
          Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0)) := by
  filter_upwards [ae_fullPostBacklog_bounds
    rate rewards C_star C_h u t control0 j] with b hb
  rcases hb with ⟨hback0, hback⟩
  have hβ := beta_pos rate
  constructor
  · apply Real.one_le_exp_iff.mpr
    exact mul_nonneg hβ.le hback0
  · apply Real.exp_le_exp_of_le
    exact mul_le_mul_of_nonneg_left hback hβ.le

/-- Integrability of the actual full post-readout exponential on the same
finite original pair law. -/
theorem integrable_fullXPlus (control0 : TimeControl p) (j : Fin p.K) :
    Integrable (fun b : B => fullXPlus rate rewards C_star C_h u t j b) mu := by
  have hbound := ae_fullXPlus_bounds rate rewards C_star C_h u t control0 j
  have hmeas := measurable_fullXPlus rate rewards C_star C_h u t j
  let C := Real.exp (beta * (2 *
    ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0))
  have hconst : Integrable (fun _ : B => C) mu := integrable_const C
  have hnorm : ∀ᵐ b ∂mu, ‖fullXPlus rate rewards C_star C_h u t j b‖ ≤ C := by
    filter_upwards [hbound] with b hb
    rw [Real.norm_of_nonneg (le_trans (by norm_num) hb.1)]
    exact hb.2
  exact hconst.mono' hmeas.aestronglyMeasurable hnorm

private theorem measurable_indicatorG_full :
    Measurable (ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
      rate rewards C_star C_h u t control0) := by
  have hG := measurableSet_G_R_ambient rate rewards C_star C_h u t control0
  exact measurable_const.indicator hG

private theorem integrable_indicatorG_full :
    Integrable
      (ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
        rate rewards C_star C_h u t control0) mu := by
  change Integrable (Set.indicator G (fun _ : B => (1 : ℝ))) mu
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_G_R_ambient rate rewards C_star C_h u t control0)

private theorem exp_max_add_le (β x y : ℝ) :
    Real.exp (β * max (x + y) 0) ≤
      1 + Real.exp (β * x) * Real.exp (β * y) := by
  by_cases h : 0 ≤ x + y
  · rw [max_eq_left h]
    have heq : β * (x + y) = β * x + β * y := by ring
    rw [heq, Real.exp_add]
    have hprod := mul_pos (Real.exp_pos (β * x)) (Real.exp_pos (β * y))
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    simp only [mul_zero, Real.exp_zero]
    have hprod := mul_pos (Real.exp_pos (β * x)) (Real.exp_pos (β * y))
    linarith

/-- Pointwise actual whole-post queue majorant, with the incoming exponential
left unmasked and the retained service penalty in the increment. -/
theorem ae_fullXPlus_le_indicatorG_add_product (j : Fin p.K) :
    (fun b : B => fullXPlus rate rewards C_star C_h u t j b) ≤ᵐ[mu]
      (fun b => ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b +
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b *
          fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b) := by
  filter_upwards [ae_fullPostBacklog_eq_reflected_increment
    rate rewards C_star C_h u t control0] with b hrec
  by_cases hG : b ∈ G
  · have hinc := fullRetainedIncrement_eq_fullA_sub_four_of_mem_G
      rate rewards C_star C_h u t control0 j b hG
    have hmax := exp_max_add_le beta
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b)
      (fullA j b - 4)
    simpa [fullXPlus,
      ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus,
      ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG,
      fullExpRetainedIncrement, fullRetainedIncrement, Set.indicator,
      hG, hrec j, hinc] using hmax
  · have hinc := fullRetainedIncrement_eq_zero_of_not_mem_G
      rate rewards C_star C_h u t control0 j b hG
    have hback :
        ((((ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t b.2).1 j).2 : ℝ) / (rate.n : ℝ)) =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b := by
      rw [hrec j, hinc]
      simp [max_eq_left (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
        rate rewards C_star C_h u t control0 j b)]
    simp [fullXPlus,
      ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus,
      ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG,
      fullExpRetainedIncrement, hG, hback, hinc]

/-- The product required by conditional pull-out is integrable from the
actual incoming queue envelope and the whole-marker exponential envelope. -/
theorem integrable_XMinus_mul_fullExpRetainedIncrement (j : Fin p.K) :
    Integrable
      (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b *
        fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b) mu := by
  have hX := ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus_bounds
    rate rewards C_star C_h u t control0 j
  have hmX : AEStronglyMeasurable
      (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b) mu :=
    (ReferenceFirstCollectionRenewalExponentialQueueStep.measurable_XMinus
      rate rewards C_star C_h u t control0 j).aestronglyMeasurable
  have hbound : ∀ᵐ b ∂mu,
      ‖ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b‖ ≤
        Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0)) := by
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (le_trans (by norm_num) (hX b).1)]
    exact (hX b).2
  exact (integrable_fullExpRetainedIncrement rate rewards C_star C_h u t control0 j).bdd_mul
    hmX hbound

/-- Conditional exponential queue step for the actual whole post-readout
queue, pulled against the existing incoming queue and retained event. -/
theorem condExp_fullXPlus_le_XMinus_add_indicatorG (j : Fin p.K) :
    mu[(fun b : B => fullXPlus rate rewards C_star C_h u t j b) | F_R] ≤ᵐ[mu]
      (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b +
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b) := by
  let y : B → ℝ := fun b =>
    fullExpRetainedIncrement rate rewards C_star C_h u t control0 j b
  let prod : B → ℝ := fun b =>
    ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
      rate rewards C_star C_h u t control0 j b * y b
  let majorant : B → ℝ := fun b =>
    ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
      rate rewards C_star C_h u t control0 b + prod b
  have hGfield : MeasurableSet[F_R] G :=
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
      rate rewards C_star C_h u t control0
  have hGint := integrable_indicatorG_full rate rewards C_star C_h u t control0
  have hXminus := ReferenceFirstCollectionRenewalExponentialQueueStep.integrable_XMinus
    rate rewards C_star C_h u t control0 j
  have hXplus := integrable_fullXPlus rate rewards C_star C_h u t control0 j
  have hy := integrable_fullExpRetainedIncrement rate rewards C_star C_h u t control0 j
  have hprod : Integrable prod mu := by
    simpa [prod, y] using integrable_XMinus_mul_fullExpRetainedIncrement
      rate rewards C_star C_h u t control0 j
  have hmajorant : Integrable majorant mu := hGint.add hprod
  have hpoint :
      (fun b : B => fullXPlus rate rewards C_star C_h u t j b) ≤ᵐ[mu] majorant := by
    simpa [majorant, prod, y] using ae_fullXPlus_le_indicatorG_add_product
      rate rewards C_star C_h u t control0 j
  have hmono := condExp_mono (m := F_R) hXplus hmajorant hpoint
  have hAdd := condExp_add hGint hprod F_R
  have hOneIntegrable : Integrable (fun _ : B => (1 : ℝ)) mu := integrable_const 1
  have hMask := condExp_indicator (μ := mu) (m := F_R) hOneIntegrable hGfield
  have hConst : mu[(fun _ : B => (1 : ℝ)) | F_R] = (fun _ : B => (1 : ℝ)) :=
    condExp_const (μ := mu) (m := F_R)
      (m₀ := (inferInstance : MeasurableSpace B))
      (retainedField_le rate rewards C_star C_h u t control0) (1 : ℝ)
  have hIndicatorCE :
      mu[(fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
        rate rewards C_star C_h u t control0 b) | F_R] =ᵐ[mu]
        (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b) := by
    filter_upwards [hMask] with b hb
    rw [hConst] at hb
    simpa [ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG] using hb
  have hPull := condExp_mul_of_aestronglyMeasurable_left
    (ReferenceFirstCollectionRenewalExponentialQueueStep.aestronglyMeasurable_XMinus
      rate rewards C_star C_h u t control0 j)
    hprod hy
  have hPullProd : mu[prod | F_R] =ᵐ[mu]
      (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b * mu[y | F_R] b) := by
    have hleft : prod = (fun b : B =>
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b) * y := by
      funext b
      rfl
    have hright :
        (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b * mu[y | F_R] b) =
          (fun b : B => ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
            rate rewards C_star C_h u t control0 j b) * mu[y | F_R] := by
      funext b
      rfl
    rw [hleft, hright]
    exact hPull
  have hYce := fullExpRetainedIncrement_condExp_le_one
    rate rewards C_star C_h u t control0 j
  have hXnonneg : ∀ᵐ b ∂mu,
      0 ≤ ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b := by
    filter_upwards [] with b
    exact le_trans (by norm_num)
      (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus_bounds
        rate rewards C_star C_h u t control0 j b).1
  filter_upwards [hmono, hAdd, hIndicatorCE, hPullProd, hYce, hXnonneg]
      with b hmono_b hAdd_b hMask_b hPull_b hYce_b hXnonneg_b
  calc
    mu[(fun x : B => fullXPlus rate rewards C_star C_h u t j x) | F_R] b ≤
        mu[majorant | F_R] b := hmono_b
    _ = mu[(fun x : B => ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 x) | F_R] b +
        mu[prod | F_R] b := hAdd_b
    _ = ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b +
        ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b * mu[y | F_R] b := by
      rw [hMask_b, hPull_b]
    _ = ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b * mu[y | F_R] b +
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b := by ring
    _ ≤ ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b * 1 +
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b :=
      add_le_add_left (mul_le_mul_of_nonneg_left hYce_b hXnonneg_b) _
    _ = ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b +
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b := by ring

/-- Weighted integral form for every nonnegative integrable test on the
retained field. Products are integrable from the proved queue envelopes. -/
theorem integral_mul_fullXPlus_le (j : Fin p.K) {H : B → ℝ}
    (hHmeas : AEStronglyMeasurable[F_R] H mu)
    (hHnonneg : 0 ≤ᵐ[mu] H) (hHint : Integrable H mu) :
    (∫ b : B, H b * fullXPlus rate rewards C_star C_h u t j b ∂mu) ≤
      (∫ b : B, H b * ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b ∂mu) +
        ∫ b : B, H b *
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b ∂mu := by
  let Hbound : ℝ := Real.exp (beta * (2 *
    ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0))
  have hXminusBound : ∀ᵐ b ∂mu,
      ‖ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b‖ ≤ Hbound := by
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (le_trans (by norm_num)
      (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus_bounds
        rate rewards C_star C_h u t control0 j b).1)]
    exact (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus_bounds
      rate rewards C_star C_h u t control0 j b).2
  have hXplusBound : ∀ᵐ b ∂mu, ‖fullXPlus rate rewards C_star C_h u t j b‖ ≤ Hbound := by
    filter_upwards [ae_fullXPlus_bounds rate rewards C_star C_h u t control0 j] with b hb
    rw [Real.norm_of_nonneg (le_trans (by norm_num) hb.1)]
    exact hb.2
  have hHplus : Integrable
      (fun b : B => H b * fullXPlus rate rewards C_star C_h u t j b) mu :=
    hHint.mul_bdd (measurable_fullXPlus rate rewards C_star C_h u t j).aestronglyMeasurable
      hXplusBound
  have hHminus : Integrable
      (fun b : B => H b * ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b) mu :=
    hHint.mul_bdd
      (ReferenceFirstCollectionRenewalExponentialQueueStep.measurable_XMinus
        rate rewards C_star C_h u t control0 j).aestronglyMeasurable hXminusBound
  have hIndicatorBound : ∀ᵐ b ∂mu,
      ‖ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
        rate rewards C_star C_h u t control0 b‖ ≤ 1 := by
    filter_upwards [] with b
    have hn : 0 ≤ ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
        rate rewards C_star C_h u t control0 b := by
      by_cases hb : b ∈ G <;>
        simp [ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG, hb]
    have hu : ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
        rate rewards C_star C_h u t control0 b ≤ 1 := by
      by_cases hb : b ∈ G <;>
        simp [ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG, hb]
    rw [Real.norm_of_nonneg hn]
    exact hu
  have hHindicator : Integrable
      (fun b : B => H b *
        ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b) mu :=
    hHint.mul_bdd
      (measurable_indicatorG_full rate rewards C_star C_h u t control0).aestronglyMeasurable
      hIndicatorBound
  have hPull := condExp_mul_of_aestronglyMeasurable_left hHmeas hHplus
    (integrable_fullXPlus rate rewards C_star C_h u t control0 j)
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  have hCEweighted : Integrable
      (fun b : B => H b * mu[(fun x : B => fullXPlus rate rewards C_star C_h u t j x) | F_R] b)
      mu :=
    (integrable_condExp (μ := mu) (m := F_R)
      (f := fun b : B => H b * fullXPlus rate rewards C_star C_h u t j b)).congr hPull
  have hpoint :
      (fun b : B => H b *
        mu[(fun x : B => fullXPlus rate rewards C_star C_h u t j x) | F_R] b) ≤ᵐ[mu]
      (fun b : B => H b *
        (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b +
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b)) := by
    filter_upwards [condExp_fullXPlus_le_XMinus_add_indicatorG
      rate rewards C_star C_h u t control0 j, hHnonneg] with b hce hH
    exact mul_le_mul_of_nonneg_left hce hH
  have hright : Integrable
      (fun b : B => H b *
        (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b +
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b)) mu := by
    have h := hHminus.add hHindicator
    exact h.congr (Filter.Eventually.of_forall fun b => by
      change H b * ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b +
        H b * ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
          rate rewards C_star C_h u t control0 b =
        H b * (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
            rate rewards C_star C_h u t control0 j b +
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b)
      rw [mul_add])
  calc
    (∫ b : B, H b * fullXPlus rate rewards C_star C_h u t j b ∂mu) =
        ∫ b : B, H b *
          mu[(fun x : B => fullXPlus rate rewards C_star C_h u t j x) | F_R] b ∂mu := by
      calc
        _ = ∫ b : B,
            mu[(fun x : B => H x * fullXPlus rate rewards C_star C_h u t j x) | F_R] b ∂mu :=
          (integral_condExp hdom).symm
        _ = _ := integral_congr_ae hPull
    _ ≤ ∫ b : B, H b *
        (ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b +
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b) ∂mu :=
      integral_mono_ae hCEweighted hright hpoint
    _ = (∫ b : B, H b *
          ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
            rate rewards C_star C_h u t control0 j b ∂mu) +
        ∫ b : B, H b *
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b ∂mu := by
      calc
        _ = ∫ b : B,
            (H b * ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
              rate rewards C_star C_h u t control0 j b) +
              (H b * ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
                rate rewards C_star C_h u t control0 b) ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with b
          rw [mul_add]
        _ = _ := integral_add hHminus hHindicator

/-- Weighted queue estimate for any bounded nonnegative Borel function of
the actual incoming readout. Its retained-field adaptation follows from the
existing incoming-readout AE identity. -/
theorem integral_incomingReadout_mul_fullXPlus_le (j : Fin p.K)
    (psi : IncomingReadout p → ℝ) (hpsi : Measurable psi)
    (C : ℝ) (hC : 0 ≤ C) (hpsiBound : ∀ x, 0 ≤ psi x ∧ psi x ≤ C) :
    (∫ b : B, psi
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
          rate rewards C_star C_h u t b.2) *
        fullXPlus rate rewards C_star C_h u t j b ∂mu) ≤
      (∫ b : B, psi
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
            rate rewards C_star C_h u t b.2) *
          ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
            rate rewards C_star C_h u t control0 j b ∂mu) +
        ∫ b : B, psi
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
            rate rewards C_star C_h u t b.2) *
          ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG
            rate rewards C_star C_h u t control0 b ∂mu := by
  let H : B → ℝ := fun b => psi
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t b.2)
  let Hret : B → ℝ := fun b => psi
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
      rate rewards C_star C_h u t
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.erasedSource
          rate rewards C_star C_h u t control0 b.1.1))
  have hretMeas : Measurable[F_R] Hret := by
    change Measurable[F_R] (fun b : B => psi
      (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.erasedSource
            rate rewards C_star C_h u t control0 b.1.1)))
    exact hpsi.comp
      (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncomingReadout
        rate rewards C_star C_h u t control0)
  have hae : H =ᵐ[mu] Hret := by
    filter_upwards [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.ae_incomingReadout_eq_retained
      rate rewards C_star C_h u t control0] with b hb
    exact congrArg psi hb
  have hHmeas : AEStronglyMeasurable[F_R] H mu :=
    hretMeas.aestronglyMeasurable.congr hae.symm
  have hHnonneg : 0 ≤ᵐ[mu] H := Filter.Eventually.of_forall fun b =>
    (hpsiBound _).1
  have hHbound : ∀ b, ‖H b‖ ≤ C := by
    intro b
    rw [Real.norm_of_nonneg (hpsiBound _).1]
    exact (hpsiBound _).2
  have hHint := integrable_of_bounded_measurable rate rewards C_star C_h u t
    ((hpsi.comp (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t)).comp measurable_snd) C hC hHbound
  have h := integral_mul_fullXPlus_le rate rewards C_star C_h u t control0 j
    (H := H) hHmeas hHnonneg hHint
  simpa [H] using h

/-- Unweighted whole-marker queue estimate, retaining the exact mass of the
no-overflow event under the unnormalized pair law. -/
theorem integral_fullXPlus_le_integral_XMinus_add_G (j : Fin p.K) :
    (∫ b : B, fullXPlus rate rewards C_star C_h u t j b ∂mu) ≤
      (∫ b : B, ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
        rate rewards C_star C_h u t control0 j b ∂mu) +
      (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
        rate rewards C_star C_h u t).real G := by
  have h := integral_mul_fullXPlus_le rate rewards C_star C_h u t control0 j
    (H := fun _ : B => (1 : ℝ))
    (by exact stronglyMeasurable_const.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun _ => by norm_num) (integrable_const (1 : ℝ))
  have h' :
      (∫ b : B, fullXPlus rate rewards C_star C_h u t j b ∂mu) ≤
        (∫ b : B, ReferenceFirstCollectionRenewalExponentialQueueStep.XMinus
          rate rewards C_star C_h u t control0 j b ∂mu) +
          ∫ b : B, Set.indicator G (fun _ : B => (1 : ℝ)) b ∂mu := by
    simpa only [one_mul,
      ReferenceFirstCollectionRenewalExponentialQueueStep.indicatorG] using h
  have hind :
      (∫ b : B, Set.indicator G (fun _ : B => (1 : ℝ)) b ∂mu) =
        (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real G := by
    rw [integral_indicator_const (1 : ℝ)
      (measurableSet_G_R_ambient rate rewards C_star C_h u t control0)]
    simp
  rw [hind] at h'
  exact h'

end Bandits.Support.ReferenceFirstCollectionRenewalWholeExponentialQueueStep

end
