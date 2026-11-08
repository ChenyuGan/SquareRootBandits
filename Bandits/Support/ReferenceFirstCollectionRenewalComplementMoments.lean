/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalGateCoefficient
public import Bandits.Support.ReferenceFirstCollectionRenewalRecordingFeedback
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# First collection renewal complement recording moments

Sources: sources/zip4/manuscript/06_interruptions.tex:399-423,
sources/zip4/manuscript/05_binary_transport.tex:352-431, and
sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264.

The readouts remain on the original unnormalized first-renewal pair law. The
coordinator gate coefficient, retained control factorization, and actual
recorder feedback are joined here. No conditional law is substituted. The
outputs are scalar first and square moments for one complement arm.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalGateCoefficient
open Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw

namespace Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)

local instance slowSetMeasurableSpace :
    MeasurableSpace (SlowSet p) := ⊤
local instance slowSetDiscrete : DiscreteMeasurableSpace (SlowSet p) :=
  ⟨fun _ => trivial⟩

local notation "B" =>
  ReferenceFirstCollectionRenewalControlFactor.Pair rate rewards C_star C_h u t
local notation "H" => ReferenceFirstCollectionRenewalControlFactor.RetainedCoordinates p
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw rate rewards C_star C_h u t
local notation "R" =>
  ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap R (inferInstance : MeasurableSpace H)

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

private theorem integrable_of_norm_le_const {α : Type*} [MeasurableSpace α]
    {ν : Measure α} [IsFiniteMeasure ν] {f : α → ℝ} (hf : Measurable f)
    (C : ℝ) (hbound : ∀ x, ‖f x‖ ≤ C) : Integrable f ν := by
  have hconst : Integrable (fun _ : α => C) ν := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with x
  simpa using hbound x

/-- The whole original auxiliary array retained by the renewal base. -/
@[expose] def U (b : B) : SlowSet p :=
  renewalAuxiliarySample rate rewards C_star C_h u t b.1.1 b.1.2

/-- The complete prechoice vector at the renewal call. -/
@[expose] def v (b : B) : Fin p.K → ℝ :=
  (renewalCallParameter rate rewards C_star C_h u t b.1.1).2

/-- The canonical recording rate for a fixed arm. -/
@[expose] def xi (b : B) (j : Fin p.K) : ℝ :=
  CanonicalRecordingRates.xi p rate.eta.val (v rate rewards C_star C_h u t b) j

/-- The fixed denominator-D rounded reward at the collection time. -/
@[expose] def r (j : Fin p.K) : ℝ :=
  RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards t j)

/-- The literal scalar floor readout used by the actual recorder. -/
@[expose] def q (b : B) (j : Fin p.K) : ℝ :=
  QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
    (xi rate rewards C_star C_h u t b j) (r rewards t j)

/-- The actual coordinator gate indicator times the literal scalar floor. -/
@[expose] def a (b : B) (j : Fin p.K) : ℝ :=
  (gateEvent rate rewards C_star C_h u t j).indicator
    (fun b => q rate rewards C_star C_h u t b j) b

/-- The coefficient for the first complement moment on the renewal pair law. -/
@[expose] def c1 (b : B) (j : Fin p.K) : ℝ :=
  coefficient rate rewards C_star C_h u t j b * q rate rewards C_star C_h u t b j

/-- The coefficient for the square complement moment on the same pair law. -/
@[expose] def c2 (b : B) (j : Fin p.K) : ℝ :=
  coefficient rate rewards C_star C_h u t j b * (q rate rewards C_star C_h u t b j) ^ 2

/-- The literal indicator that arm j is in the original renewal complement. -/
@[expose] def chi (b : B) (j : Fin p.K) : ℝ :=
  if j ∉ (U rate rewards C_star C_h u t b).val then 1 else 0

private theorem measurable_xi_of_measurable_weight {α : Type*} [MeasurableSpace α]
    (w : α → Fin p.K → ℝ) (hw : Measurable w) (j : Fin p.K) :
    Measurable (fun x => CanonicalRecordingRates.xi p rate.eta.val (w x) j) := by
  have hprod (S : Finset (Fin p.K)) :
      Measurable (fun w : Fin p.K → ℝ => ProductSetLaw.setWeight w S) := by
    unfold ProductSetLaw.setWeight
    exact Finset.measurable_fun_prod S (fun i _ => measurable_pi_apply i)
  have htotal : Measurable (fun w : Fin p.K → ℝ =>
      FiniteNormalization.totalMass (ProductSetLaw.support p.K p.m)
        (ProductSetLaw.setWeight w)) := by
    unfold FiniteNormalization.totalMass
    exact Finset.measurable_fun_sum _ (fun S _ => hprod S)
  have htheta : Measurable (fun w : Fin p.K → ℝ => ProductSetLaw.theta p.m w j) := by
    unfold ProductSetLaw.theta FiniteNormalization.mass
    apply Finset.measurable_fun_sum
    intro S _
    unfold FiniteNormalization.normalizedWeight
    exact (hprod S).div htotal
  have hf : Measurable (fun w : Fin p.K → ℝ => CanonicalRecordingRates.f p w j) := by
    unfold CanonicalRecordingRates.f
    fun_prop
  exact AssignmentPayloadDerivedMeasurability.measurable_dyadicCeiling.comp
    ((measurable_const.max hf).comp hw)

private theorem measurable_q_of_measurable_xi {α : Type*} [MeasurableSpace α]
    (x : α → ℝ) (hx : Measurable x) (reward : ℝ) :
    Measurable (fun z => QuantizedRecordingMoments.quantizedValue
      (D p) rate.eta.val (x z) reward) := by
  have harg : Measurable (fun z => ((D p : ℝ) * rate.eta.val * reward) / x z) := by
    exact (measurable_const.mul measurable_const).div hx
  have hfloor : Measurable (fun z =>
      (Nat.floor (((D p : ℝ) * rate.eta.val * reward) / x z) : ℝ)) :=
    (measurable_of_countable _).comp (Nat.measurable_floor.comp harg)
  change Measurable (fun z =>
    (Nat.floor (((D p : ℝ) * rate.eta.val * reward) / x z) : ℝ) /
      (rate.eta.val * (D p : ℝ)))
  exact hfloor.div_const _

/-- The source floor value is measurable on the existing pair carrier. -/
theorem measurable_q (j : Fin p.K) : Measurable ((fun b => q rate rewards C_star C_h u t b j)) := by
  have hp := (measurable_renewalCallParameter rate rewards C_star C_h u t).comp
    (measurable_fst.comp measurable_fst : Measurable (fun b : B => b.1.1))
  have hw : Measurable (v rate rewards C_star C_h u t) := measurable_snd.comp hp
  exact measurable_q_of_measurable_xi
    rate
    (fun b => CanonicalRecordingRates.xi p rate.eta.val
      (v rate rewards C_star C_h u t b) j)
    (measurable_xi_of_measurable_weight rate
      (v rate rewards C_star C_h u t) hw j)
    (r rewards t j)

/-- The floor readout is measurable in the specified retained coordinates. -/
theorem measurable_q_retained (j : Fin p.K) :
    Measurable[F_R] ((fun b => q rate rewards C_star C_h u t b j)) := by
  let m := F_R
  let Rfun := R
  have hR : Measurable[m] Rfun := comap_measurable _
  let erased : B → RenewalCallSource rate rewards C_star C_h u t :=
    fun b => ReferenceFirstCollectionRenewalPastLocality.renewalSourceWithSuffix
      rate rewards C_star C_h u t b.1.1 (fun _ => control0)
  have hz : Measurable[m] erased := by
    apply Measurable.subtype_mk
    exact (measurable_fst.comp (measurable_fst.comp measurable_fst)).comp hR
  have hp := (measurable_renewalCallParameter rate rewards C_star C_h u t).comp hz
  have hw : Measurable[m] (fun b : B =>
      (renewalCallParameter rate rewards C_star C_h u t (erased b)).2) :=
    measurable_snd.comp hp
  have hxi := measurable_xi_of_measurable_weight rate
    (fun b => (renewalCallParameter rate rewards C_star C_h u t (erased b)).2) hw j
  have hq := measurable_q_of_measurable_xi
    rate
    (fun b => CanonicalRecordingRates.xi p rate.eta.val
      (renewalCallParameter rate rewards C_star C_h u t (erased b)).2 j)
    hxi (r rewards t j)
  have hqeq : (fun b : B => q rate rewards C_star C_h u t b j) =
      (fun b : B => QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (CanonicalRecordingRates.xi p rate.eta.val
          (renewalCallParameter rate rewards C_star C_h u t (erased b)).2 j)
        (r rewards t j)) := by
    funext b
    dsimp [q, xi, v, erased]
    rw [(erased_parameter_and_sample rate rewards C_star C_h u t control0
      b.1.1 b.1.2).1]
  rw [hqeq]
  exact hq

/-- The literal retained field is dominated by the ambient pair-law field. -/
theorem retainedField_le : F_R ≤ (inferInstance : MeasurableSpace B) := by
  exact measurable_iff_comap_le.mp
    (measurable_retainedControlCoordinates rate rewards C_star C_h u t control0)

/-- The finite original pair measure remains finite after trimming to the retained field. -/
theorem retainedField_trim_finite :
    IsFiniteMeasure ((mu).trim (retainedField_le rate rewards C_star C_h u t control0)) := by
  infer_instance

/-- The same retained-field trim is sigma finite, with no normalization. -/
theorem retainedField_trim_sigmaFinite :
    SigmaFinite ((mu).trim (retainedField_le rate rewards C_star C_h u t control0)) := by
  infer_instance

/-- The estimate and both coefficient readouts are retained-field measurable. -/
theorem measurable_retained_readouts (j : Fin p.K) :
    Measurable[F_R] ((fun b => q rate rewards C_star C_h u t b j)) ∧
      Measurable[F_R] ((fun b => c1 rate rewards C_star C_h u t b j)) ∧
      Measurable[F_R] ((fun b => c2 rate rewards C_star C_h u t b j)) := by
  have hq := measurable_q_retained rate rewards C_star C_h u t control0 j
  have hc := measurable_coefficient_retained rate rewards C_star C_h u t control0 j
  exact ⟨hq, hc.mul hq, hc.mul (hq.pow_const 2)⟩

/-- Ambient measurability of the first estimate and its square. -/
theorem measurable_a (j : Fin p.K) : Measurable ((fun b => a rate rewards C_star C_h u t b j)) := by
  exact (measurable_q rate rewards C_star C_h u t j).indicator
    (measurableSet_gateEvent rate rewards C_star C_h u t j)

theorem measurable_a_sq (j : Fin p.K) :
    Measurable (fun b => (a rate rewards C_star C_h u t b j) ^ 2) :=
  (measurable_a rate rewards C_star C_h u t j).pow_const 2

/-- Ambient measurability of the first and square coefficient readouts. -/
theorem measurable_coefficients (j : Fin p.K) :
    Measurable ((fun b => c1 rate rewards C_star C_h u t b j)) ∧
      Measurable ((fun b => c2 rate rewards C_star C_h u t b j)) := by
  have hq := measurable_q rate rewards C_star C_h u t j
  have hc := measurable_coefficient rate rewards C_star C_h u t j
  exact ⟨hc.mul hq, hc.mul (hq.pow_const 2)⟩

/-- The quantized readout has a uniform finite bound from the recording-rate floor. -/
theorem q_nonneg_le_inv (b : B) (j : Fin p.K) :
    0 ≤ q rate rewards C_star C_h u t b j ∧
      q rate rewards C_star C_h u t b j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbetaxi := CanonicalRecordingRates.beta_le_xi p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hr := RealRewardGridCount.realRewardGridValue_mem_Icc
    (D p) (D_pos p) (rewards t j)
  constructor
  · exact QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
      (xi rate rewards C_star C_h u t b j) (r rewards t j)
      rate.eta.property
  · exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le
      (D p) rate.eta.val (xi rate rewards C_star C_h u t b j)
      (r rewards t j) (CanonicalRecordingRates.beta p rate.eta.val)
      (D_pos p) rate.eta.property hxi hr hbeta hbetaxi

private theorem coefficient_eq_chi_mul_xi (b : B) (j : Fin p.K) :
    coefficient rate rewards C_star C_h u t j b =
      chi rate rewards C_star C_h u t b j * xi rate rewards C_star C_h u t b j := by
  by_cases h : j ∉ (renewalAuxiliarySample rate rewards C_star C_h u t
      b.1.1 b.1.2).val
  · simp [coefficient, chi, xi, v, U, h]
  · simp [coefficient, chi, xi, v, U, h]

private theorem chi_nonneg_le_one (b : B) (j : Fin p.K) :
    0 ≤ chi rate rewards C_star C_h u t b j ∧
      chi rate rewards C_star C_h u t b j ≤ 1 := by
  unfold chi
  split <;> norm_num

/-- The pointwise first-moment coefficient has the source rounding bounds. -/
theorem c1_bounds (b : B) (j : Fin p.K) :
    0 ≤ c1 rate rewards C_star C_h u t b j ∧
      chi rate rewards C_star C_h u t b j *
          (r rewards t j -
            xi rate rewards C_star C_h u t b j /
              (rate.eta.val * (D p : ℝ))) ≤
        c1 rate rewards C_star C_h u t b j ∧
      c1 rate rewards C_star C_h u t b j ≤
        chi rate rewards C_star C_h u t b j * r rewards t j := by
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hr := RealRewardGridCount.realRewardGridValue_mem_Icc
    (D p) (D_pos p) (rewards t j)
  have hq0 := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
    (xi rate rewards C_star C_h u t b j) (r rewards t j)
    rate.eta.property
  have hround := QuantizedRecordingMoments.quantizedValue_roundingError
    (D p) rate.eta.val (xi rate rewards C_star C_h u t b j)
    (r rewards t j) (D_pos p) rate.eta.property hxi hr
  have hfirst := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (D p) rate.eta.val (xi rate rewards C_star C_h u t b j)
    (r rewards t j) (D_pos p) rate.eta.property hxi hr
  have hfirst' : xi rate rewards C_star C_h u t b j *
      q rate rewards C_star C_h u t b j ≤ r rewards t j := by
    simpa [q] using hfirst
  have hchi := chi_nonneg_le_one rate rewards C_star C_h u t b j
  change 0 ≤ coefficient rate rewards C_star C_h u t j b *
      q rate rewards C_star C_h u t b j ∧
    chi rate rewards C_star C_h u t b j *
      (r rewards t j -
        xi rate rewards C_star C_h u t b j /
          (rate.eta.val * (D p : ℝ))) ≤
      coefficient rate rewards C_star C_h u t j b *
        q rate rewards C_star C_h u t b j ∧
    coefficient rate rewards C_star C_h u t j b *
      q rate rewards C_star C_h u t b j ≤
        chi rate rewards C_star C_h u t b j * r rewards t j
  rw [coefficient_eq_chi_mul_xi rate rewards C_star C_h u t b j]
  constructor
  · exact mul_nonneg (mul_nonneg hchi.1 hxi.le) hq0
  constructor
  · calc
      chi rate rewards C_star C_h u t b j *
          (r rewards t j -
            xi rate rewards C_star C_h u t b j /
              (rate.eta.val * (D p : ℝ))) ≤
        chi rate rewards C_star C_h u t b j *
          (xi rate rewards C_star C_h u t b j *
            q rate rewards C_star C_h u t b j) :=
        mul_le_mul_of_nonneg_left hround hchi.1
      _ = chi rate rewards C_star C_h u t b j *
          xi rate rewards C_star C_h u t b j *
            q rate rewards C_star C_h u t b j := by ring
  · calc
      chi rate rewards C_star C_h u t b j *
          xi rate rewards C_star C_h u t b j *
            q rate rewards C_star C_h u t b j ≤
        chi rate rewards C_star C_h u t b j * r rewards t j := by
          calc
            chi rate rewards C_star C_h u t b j *
                xi rate rewards C_star C_h u t b j *
                q rate rewards C_star C_h u t b j =
              chi rate rewards C_star C_h u t b j *
                (xi rate rewards C_star C_h u t b j *
                  q rate rewards C_star C_h u t b j) := by ring
            _ ≤ chi rate rewards C_star C_h u t b j * r rewards t j :=
              mul_le_mul_of_nonneg_left hfirst' hchi.1

/-- The pointwise square coefficient has the source second-moment bound. -/
theorem c2_bounds (b : B) (j : Fin p.K) :
    0 ≤ c2 rate rewards C_star C_h u t b j ∧
      c2 rate rewards C_star C_h u t b j ≤
        chi rate rewards C_star C_h u t b j *
          (r rewards t j) ^ 2 /
            xi rate rewards C_star C_h u t b j := by
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hr := RealRewardGridCount.realRewardGridValue_mem_Icc
    (D p) (D_pos p) (rewards t j)
  have hq0 := QuantizedRecordingMoments.quantizedValue_nonneg (D p) rate.eta.val
    (xi rate rewards C_star C_h u t b j) (r rewards t j)
    rate.eta.property
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (xi rate rewards C_star C_h u t b j)
    (r rewards t j) (D_pos p) rate.eta.property hxi hr
  have hchi := chi_nonneg_le_one rate rewards C_star C_h u t b j
  change 0 ≤ coefficient rate rewards C_star C_h u t j b *
      (q rate rewards C_star C_h u t b j) ^ 2 ∧
    coefficient rate rewards C_star C_h u t j b *
      (q rate rewards C_star C_h u t b j) ^ 2 ≤
        chi rate rewards C_star C_h u t b j *
          (r rewards t j) ^ 2 /
            xi rate rewards C_star C_h u t b j
  rw [coefficient_eq_chi_mul_xi rate rewards C_star C_h u t b j]
  constructor
  · exact mul_nonneg (mul_nonneg hchi.1 hxi.le) (sq_nonneg _)
  · calc
      chi rate rewards C_star C_h u t b j *
          xi rate rewards C_star C_h u t b j *
            (q rate rewards C_star C_h u t b j) ^ 2 =
        chi rate rewards C_star C_h u t b j *
          (xi rate rewards C_star C_h u t b j *
            (q rate rewards C_star C_h u t b j) ^ 2) := by ring
      _ ≤
        chi rate rewards C_star C_h u t b j *
          ((r rewards t j) ^ 2 /
            xi rate rewards C_star C_h u t b j) :=
        mul_le_mul_of_nonneg_left hsecond hchi.1
      _ = chi rate rewards C_star C_h u t b j *
          (r rewards t j) ^ 2 /
            xi rate rewards C_star C_h u t b j := by ring

private theorem coefficient_nonneg_le_one (b : B) (j : Fin p.K) :
    0 ≤ coefficient rate rewards C_star C_h u t j b ∧
      coefficient rate rewards C_star C_h u t j b ≤ 1 := by
  obtain ⟨d, hweight, hpos, _⟩ :=
    actual_renewal_call_weight_equations rate rewards C_star C_h u t b.1.1
  have hvpos : ∀ i, 0 < v rate rewards C_star C_h u t b i := by
    intro i
    change 0 < (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 i
    rw [hweight]
    exact hpos i
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hxiUpper := CanonicalRecordingRates.xi_le_one_div_16mK p
    rate.eta.property rate.sourceCap (v rate rewards C_star C_h u t b) hvpos j
  have hden : 1 ≤ 16 * (p.m : ℝ) * (p.K : ℝ) := by
    have hm2 : 2 ≤ p.m := p.two_le_m
    have hmNat : 1 ≤ p.m := by omega
    have hKNat : 1 ≤ p.K := le_trans hmNat (Nat.le_of_lt p.m_lt_K)
    have hm : (1 : ℝ) ≤ (p.m : ℝ) := by exact_mod_cast hmNat
    have hK : (1 : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast hKNat
    nlinarith
  have hxiOne : xi rate rewards C_star C_h u t b j ≤ 1 := by
    calc
      xi rate rewards C_star C_h u t b j ≤
          1 / (16 * (p.m : ℝ) * (p.K : ℝ)) := hxiUpper
      _ ≤ 1 := (div_le_one (by positivity)).2 hden
  have hchi := chi_nonneg_le_one rate rewards C_star C_h u t b j
  rw [coefficient_eq_chi_mul_xi rate rewards C_star C_h u t b j]
  refine ⟨mul_nonneg hchi.1 hxi.le, ?_⟩
  calc
    chi rate rewards C_star C_h u t b j * xi rate rewards C_star C_h u t b j ≤
        1 * xi rate rewards C_star C_h u t b j :=
      mul_le_mul_of_nonneg_right hchi.2 hxi.le
    _ ≤ 1 := by simpa [xi] using hxiOne

/-- Uniform bounds from the accepted xi floor and ceiling certify integrability. -/
theorem uniform_readout_bounds (b : B) (j : Fin p.K) :
    0 ≤ a rate rewards C_star C_h u t b j ∧
      a rate rewards C_star C_h u t b j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val ∧
      0 ≤ c1 rate rewards C_star C_h u t b j ∧
      c1 rate rewards C_star C_h u t b j ≤ 1 ∧
      0 ≤ c2 rate rewards C_star C_h u t b j ∧
      c2 rate rewards C_star C_h u t b j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hchi := chi_nonneg_le_one rate rewards C_star C_h u t b j
  have hxi := CanonicalRecordingRates.xi_pos p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hbetaxi := CanonicalRecordingRates.beta_le_xi p rate.eta.property
    (v rate rewards C_star C_h u t b) j
  have hr := RealRewardGridCount.realRewardGridValue_mem_Icc
    (D p) (D_pos p) (rewards t j)
  have ha := q_nonneg_le_inv rate rewards C_star C_h u t b j
  have hc1 := c1_bounds rate rewards C_star C_h u t b j
  have hc2 := c2_bounds rate rewards C_star C_h u t b j
  have hc2div : chi rate rewards C_star C_h u t b j *
      ((r rewards t j) ^ 2 /
        xi rate rewards C_star C_h u t b j) ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
    have hr' : r rewards t j ∈ Set.Icc 0 1 := by simpa [r] using hr
    have hsquare : (r rewards t j) ^ 2 ≤ 1 := by nlinarith [hr'.1, hr'.2]
    have hdiv0 : 0 ≤ (r rewards t j) ^ 2 /
        xi rate rewards C_star C_h u t b j :=
      div_nonneg (sq_nonneg _) hxi.le
    calc
      chi rate rewards C_star C_h u t b j *
          ((r rewards t j) ^ 2 /
            xi rate rewards C_star C_h u t b j) ≤
        1 * ((r rewards t j) ^ 2 /
          xi rate rewards C_star C_h u t b j) :=
        mul_le_mul_of_nonneg_right hchi.2 hdiv0
      _ ≤ 1 / xi rate rewards C_star C_h u t b j :=
        by simpa [one_mul, xi, v] using
          (div_le_div_of_nonneg_right hsquare hxi.le)
      _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
        one_div_le_one_div_of_le hbeta hbetaxi
  have hr' : r rewards t j ∈ Set.Icc 0 1 := by simpa [r] using hr
  have hchiR : chi rate rewards C_star C_h u t b j *
      r rewards t j ≤ 1 := by
    calc
      chi rate rewards C_star C_h u t b j * r rewards t j ≤
          1 * r rewards t j :=
        mul_le_mul_of_nonneg_right hchi.2 hr.1
      _ ≤ 1 := by nlinarith [hr'.1, hr'.2]
  have hc2top : chi rate rewards C_star C_h u t b j *
      (r rewards t j) ^ 2 / xi rate rewards C_star C_h u t b j ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    calc
      chi rate rewards C_star C_h u t b j * (r rewards t j) ^ 2 /
          xi rate rewards C_star C_h u t b j =
        chi rate rewards C_star C_h u t b j *
          ((r rewards t j) ^ 2 / xi rate rewards C_star C_h u t b j) := by ring
      _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := hc2div
  by_cases hg : b ∈ gateEvent rate rewards C_star C_h u t j
  · refine ⟨?_, ?_, hc1.1, hc1.2.2.trans hchiR, hc2.1, hc2.2.trans hc2top⟩
    · simpa [a, hg] using ha.1
    · simpa [a, hg] using ha.2
  · refine ⟨?_, ?_, hc1.1, hc1.2.2.trans hchiR, hc2.1, hc2.2.trans hc2top⟩
    · norm_num [a, hg]
    · simpa [a, hg] using
        (div_nonneg (show (0 : ℝ) ≤ 1 by norm_num) hbeta.le)

/-- Uniform pointwise bounds make all four readouts integrable on the original law. -/
theorem integrable_readouts (j : Fin p.K) :
    Integrable ((fun b => a rate rewards C_star C_h u t b j)) mu ∧
      Integrable (fun b => (a rate rewards C_star C_h u t b j) ^ 2) mu ∧
      Integrable ((fun b => c1 rate rewards C_star C_h u t b j)) mu ∧
      Integrable ((fun b => c2 rate rewards C_star C_h u t b j)) mu := by
  have ha := measurable_a rate rewards C_star C_h u t j
  have ha2 := measurable_a_sq rate rewards C_star C_h u t j
  have hc := measurable_coefficients rate rewards C_star C_h u t j
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  refine ⟨integrable_of_norm_le_const (ν := mu) ha
      (1 / CanonicalRecordingRates.beta p rate.eta.val) ?_,
    integrable_of_norm_le_const (ν := mu) ha2
      ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2) ?_,
    integrable_of_norm_le_const (ν := mu) hc.1 1 ?_,
    integrable_of_norm_le_const (ν := mu) hc.2
      (1 / CanonicalRecordingRates.beta p rate.eta.val) ?_⟩
  · intro b
    have h := uniform_readout_bounds rate rewards C_star C_h u t b j
    change ‖a rate rewards C_star C_h u t b j‖ ≤ _
    rw [Real.norm_of_nonneg h.1]
    exact h.2.1
  · intro b
    have h := uniform_readout_bounds rate rewards C_star C_h u t b j
    change ‖(a rate rewards C_star C_h u t b j) ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg (a rate rewards C_star C_h u t b j))]
    have hsq := mul_le_mul h.2.1 h.2.1 h.1
      (div_nonneg (by norm_num) hbeta.le)
    simpa [pow_two] using hsq
  · intro b
    have h := uniform_readout_bounds rate rewards C_star C_h u t b j
    change ‖c1 rate rewards C_star C_h u t b j‖ ≤ _
    rw [Real.norm_of_nonneg h.2.2.1]
    exact h.2.2.2.1
  · intro b
    have h := uniform_readout_bounds rate rewards C_star C_h u t b j
    change ‖c2 rate rewards C_star C_h u t b j‖ ≤ _
    rw [Real.norm_of_nonneg h.2.2.2.2.1]
    exact h.2.2.2.2.2

private theorem gate_indicator_setIntegral_eq (j : Fin p.K)
    (Hset : Set H) (hHset : MeasurableSet Hset) :
    ∫ b in {b : B | R b ∈ Hset},
        (gateEvent rate rewards C_star C_h u t j).indicator (fun _ => (1 : ℝ)) b ∂mu =
      ∫ b in {b : B | R b ∈ Hset},
        coefficient rate rewards C_star C_h u t j b ∂mu := by
  let Rfun := R
  let S : Set B := {b | Rfun b ∈ Hset}
  let E : Set B := {b | Rfun b ∈ Hset ∧
    b ∈ gateEvent rate rewards C_star C_h u t j}
  let gate : B → ℝ := (gateEvent rate rewards C_star C_h u t j).indicator
    (fun _ => (1 : ℝ))
  have hR : Measurable Rfun :=
    measurable_retainedControlCoordinates rate rewards C_star C_h u t control0
  have hS : MeasurableSet S := hHset.preimage hR
  have hgate : MeasurableSet (gateEvent rate rewards C_star C_h u t j) :=
    measurableSet_gateEvent rate rewards C_star C_h u t j
  have hE : MeasurableSet E := hS.inter hgate
  have hEeq : E = S ∩ gateEvent rate rewards C_star C_h u t j := by
    ext b
    simp only [E, S, Set.mem_setOf_eq, Set.mem_inter_iff]
  have hcy := gate_cylinder rate rewards C_star C_h u t control0 j Hset hHset
  have hmass : mu E = ∫⁻ b in S,
      ENNReal.ofReal (coefficient rate rewards C_star C_h u t j b) ∂mu := by
    simpa only [E, S] using hcy
  have hcoeff : ∀ b, 0 ≤ coefficient rate rewards C_star C_h u t j b := by
    intro b
    exact (coefficient_nonneg_le_one rate rewards C_star C_h u t b j).1
  have hcoeffInt : Integrable (coefficient rate rewards C_star C_h u t j) mu :=
    integrable_of_norm_le_const (ν := mu)
      (measurable_coefficient rate rewards C_star C_h u t j) 1 (fun b => by
        have h := coefficient_nonneg_le_one rate rewards C_star C_h u t b j
        rw [Real.norm_of_nonneg h.1]
        exact h.2)
  have hcoeffIndicatorIntegrable : Integrable
      (S.indicator (coefficient rate rewards C_star C_h u t j)) mu :=
    hcoeffInt.indicator hS
  have hcoeffIndicatorNonneg : ∀ᵐ b ∂mu, 0 ≤ S.indicator
      (coefficient rate rewards C_star C_h u t j) b := by
    filter_upwards [] with b
    by_cases hb : b ∈ S
    · simpa [Set.indicator_of_mem, hb] using hcoeff b
    · simp [Set.indicator_of_notMem, hb]
  have hcoeffCast :
      (fun b => ENNReal.ofReal (S.indicator
        (coefficient rate rewards C_star C_h u t j) b)) =
        S.indicator (fun b => ENNReal.ofReal
          (coefficient rate rewards C_star C_h u t j b)) := by
    funext b
    by_cases hb : b ∈ S
    · simp [Set.indicator_of_mem, hb]
    · simp [Set.indicator_of_notMem, hb]
  have hcoeffNN :
      ∫⁻ b, ENNReal.ofReal (S.indicator
        (coefficient rate rewards C_star C_h u t j) b) ∂mu = mu E := by
    rw [hcoeffCast, lintegral_indicator hS]
    exact hmass.symm
  have hgateFun : S.indicator gate = E.indicator (fun _ => (1 : ℝ)) := by
    funext b
    by_cases hs : b ∈ S
    · by_cases hg : b ∈ gateEvent rate rewards C_star C_h u t j
      · have he : b ∈ E := by
          change b ∈ S ∧ b ∈ gateEvent rate rewards C_star C_h u t j
          exact ⟨hs, hg⟩
        change S.indicator gate b = E.indicator (fun _ => (1 : ℝ)) b
        rw [Set.indicator_of_mem hs]
        change (gateEvent rate rewards C_star C_h u t j).indicator
            (fun _ => (1 : ℝ)) b = E.indicator (fun _ => (1 : ℝ)) b
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem he]
      · have he : b ∉ E := by
          intro he
          exact hg he.2
        change S.indicator gate b = E.indicator (fun _ => (1 : ℝ)) b
        rw [Set.indicator_of_mem hs]
        change (gateEvent rate rewards C_star C_h u t j).indicator
            (fun _ => (1 : ℝ)) b = E.indicator (fun _ => (1 : ℝ)) b
        rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem he]
    · have he : b ∉ E := by
        intro he
        exact hs he.1
      change S.indicator gate b = E.indicator (fun _ => (1 : ℝ)) b
      rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem he]
  have hgateCast :
      (fun b => ENNReal.ofReal (S.indicator gate b)) =
        E.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext b
    rw [hgateFun]
    by_cases hb : b ∈ E <;> simp [hb]
  have hgateNN :
      ∫⁻ b, ENNReal.ofReal (S.indicator gate b) ∂mu = mu E := by
    calc
      ∫⁻ b, ENNReal.ofReal (S.indicator gate b) ∂mu =
          ∫⁻ b, E.indicator (fun _ => (1 : ℝ≥0∞)) b ∂mu := by rw [hgateCast]
      _ = mu E := lintegral_indicator_one hE
  have hgateIndicatorIntegrable : Integrable (S.indicator gate) mu := by
    apply integrable_of_norm_le_const (ν := mu)
      ((measurable_const.indicator hgate).indicator hS) 1
    intro b
    by_cases hs : b ∈ S
    · by_cases hg : b ∈ gateEvent rate rewards C_star C_h u t j <;>
        simp [hs, hg, gate]
    · simp [hs]
  have hgateIndicatorNonneg : ∀ᵐ b ∂mu, 0 ≤ S.indicator gate b := by
    filter_upwards [] with b
    by_cases hs : b ∈ S
    · simp only [Set.indicator_of_mem hs]
      by_cases hg : b ∈ gateEvent rate rewards C_star C_h u t j
      · simp [gate, Set.indicator_of_mem hg]
      · simp [gate, Set.indicator_of_notMem hg]
    · simp [Set.indicator_of_notMem, hs]
  have hcoeffIntegral :
      ∫ b in S, coefficient rate rewards C_star C_h u t j b ∂mu =
        ENNReal.toReal (mu E) := by
    rw [← integral_indicator hS]
    rw [integral_eq_lintegral_of_nonneg_ae hcoeffIndicatorNonneg
      hcoeffIndicatorIntegrable.aestronglyMeasurable]
    rw [hcoeffNN]
  have hgateIntegral :
      ∫ b in S, gate b ∂mu = ENNReal.toReal (mu E) := by
    rw [← integral_indicator hS]
    rw [integral_eq_lintegral_of_nonneg_ae hgateIndicatorNonneg
      hgateIndicatorIntegrable.aestronglyMeasurable]
    rw [hgateNN]
  rw [hgateIntegral, hcoeffIntegral]

private theorem gate_indicator_condExp
    (j : Fin p.K) :
    mu[(gateEvent rate rewards C_star C_h u t j).indicator
      (fun _ => (1 : ℝ)) | F_R] =ᵐ[mu] coefficient rate rewards C_star C_h u t j := by
  let Rfun := R
  let gate := (gateEvent rate rewards C_star C_h u t j).indicator
    (fun _ => (1 : ℝ))
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  have hgateMeas := measurableSet_gateEvent rate rewards C_star C_h u t j
  have hgateMeasurable : Measurable gate :=
    measurable_const.indicator hgateMeas
  have hgateInt : Integrable gate mu := by
    apply integrable_of_norm_le_const (ν := mu) hgateMeasurable 1
    intro b
    by_cases hb : b ∈ gateEvent rate rewards C_star C_h u t j <;> simp [gate, hb]
  have hcoeffInt := integrable_of_norm_le_const (ν := mu)
    (measurable_coefficient rate rewards C_star C_h u t j) 1 (fun b => by
      have h := coefficient_nonneg_le_one rate rewards C_star C_h u t b j
      rw [Real.norm_of_nonneg h.1]
      exact h.2)
  have hce : coefficient rate rewards C_star C_h u t j =ᵐ[mu] mu[gate | F_R] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hdom hgateInt
    · intro s hs _
      exact hcoeffInt.integrableOn
    · intro s hs _
      obtain ⟨Hset, hHset, hs_eq⟩ := (MeasurableSpace.measurableSet_comap).mp hs
      have hs_eq' : s = {b : B | Rfun b ∈ Hset} := by
        ext b
        exact Iff.of_eq (by
          simpa [Rfun] using (congrArg (fun z : Set B => b ∈ z) hs_eq).symm)
      rw [hs_eq']
      exact (gate_indicator_setIntegral_eq rate rewards C_star C_h u t control0 j
        Hset hHset).symm
    · exact (measurable_coefficient_retained
        rate rewards C_star C_h u t control0 j).aestronglyMeasurable
  exact hce.symm

private theorem first_condExp_ae (j : Fin p.K) :
    mu[((fun b => a rate rewards C_star C_h u t b j)) | F_R] =ᵐ[mu]
      (fun b => c1 rate rewards C_star C_h u t b j) := by
  let gate := (gateEvent rate rewards C_star C_h u t j).indicator
    (fun _ => (1 : ℝ))
  have haeq : (fun b => a rate rewards C_star C_h u t b j) =
      (fun b => q rate rewards C_star C_h u t b j) * gate := by
    funext b
    by_cases hb : b ∈ gateEvent rate rewards C_star C_h u t j
    · simp [a, gate, hb]
    · simp [a, gate, hb]
  have hqStrong : StronglyMeasurable[F_R] ((fun b => q rate rewards C_star C_h u t b j)) :=
    (measurable_q_retained rate rewards C_star C_h u t control0 j).stronglyMeasurable
  have hgateInt : Integrable gate mu := by
    apply integrable_of_norm_le_const (ν := mu)
      (measurable_const.indicator
        (measurableSet_gateEvent rate rewards C_star C_h u t j)) 1
    intro b
    by_cases hb : b ∈ gateEvent rate rewards C_star C_h u t j <;> simp [gate, hb]
  have hprodInt : Integrable ((fun b => q rate rewards C_star C_h u t b j) * gate) mu := by
    rw [← haeq]
    exact (integrable_readouts rate rewards C_star C_h u t j).1
  have hmul := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
    hqStrong hprodInt hgateInt
  have hgateCE := gate_indicator_condExp rate rewards C_star C_h u t control0 j
  calc
    mu[((fun b => a rate rewards C_star C_h u t b j)) | F_R] =ᵐ[mu]
        mu[((fun b => q rate rewards C_star C_h u t b j) * gate) | F_R] := by
      exact MeasureTheory.condExp_congr_ae
        (Filter.Eventually.of_forall fun b => congrFun haeq b)
    _ =ᵐ[mu] (fun b => q rate rewards C_star C_h u t b j) * mu[gate | F_R] := hmul
    _ =ᵐ[mu] (fun b => c1 rate rewards C_star C_h u t b j) := by
      filter_upwards [hgateCE] with b hb
      change q rate rewards C_star C_h u t b j * mu[gate | F_R] b =
        coefficient rate rewards C_star C_h u t j b *
          q rate rewards C_star C_h u t b j
      rw [hb]
      ring

private theorem second_condExp_ae (j : Fin p.K) :
    mu[(fun b => (a rate rewards C_star C_h u t b j) ^ 2) | F_R] =ᵐ[mu]
      (fun b => c2 rate rewards C_star C_h u t b j) := by
  let gate := (gateEvent rate rewards C_star C_h u t j).indicator
    (fun _ => (1 : ℝ))
  have haeq : (fun b => (a rate rewards C_star C_h u t b j) ^ 2) =
      ((fun b => q rate rewards C_star C_h u t b j)) ^ 2 * gate := by
    funext b
    by_cases hb : b ∈ gateEvent rate rewards C_star C_h u t j
    · simp [a, gate, hb]
    · simp [a, gate, hb]
  have hqStrong : StronglyMeasurable[F_R] (fun b =>
      (q rate rewards C_star C_h u t b j) ^ 2) :=
    ((measurable_q_retained rate rewards C_star C_h u t control0 j).pow_const 2).stronglyMeasurable
  have hgateInt : Integrable gate mu := by
    apply integrable_of_norm_le_const (ν := mu)
      (measurable_const.indicator
        (measurableSet_gateEvent rate rewards C_star C_h u t j)) 1
    intro b
    by_cases hb : b ∈ gateEvent rate rewards C_star C_h u t j <;> simp [gate, hb]
  have hprodInt : Integrable (((fun b => q rate rewards C_star C_h u t b j)) ^ 2 * gate) mu := by
    rw [← haeq]
    exact (integrable_readouts rate rewards C_star C_h u t j).2.1
  have hmul := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
    hqStrong hprodInt hgateInt
  have hgateCE := gate_indicator_condExp rate rewards C_star C_h u t control0 j
  calc
    mu[(fun b => (a rate rewards C_star C_h u t b j) ^ 2) | F_R] =ᵐ[mu]
        mu[(((fun b => q rate rewards C_star C_h u t b j)) ^ 2 * gate) | F_R] := by
      exact MeasureTheory.condExp_congr_ae
        (Filter.Eventually.of_forall fun b => congrFun haeq b)
    _ =ᵐ[mu] ((fun b => q rate rewards C_star C_h u t b j)) ^ 2 * mu[gate | F_R] := hmul
    _ =ᵐ[mu] (fun b => c2 rate rewards C_star C_h u t b j) := by
      filter_upwards [hgateCE] with b hb
      change (q rate rewards C_star C_h u t b j) ^ 2 * mu[gate | F_R] b =
        coefficient rate rewards C_star C_h u t j b *
          (q rate rewards C_star C_h u t b j) ^ 2
      rw [hb]
      ring

/-- First-moment equality on every retained-coordinate cylinder, under mu. -/
theorem first_moment_setIntegral (j : Fin p.K) (Hset : Set H)
    (hHset : MeasurableSet Hset) :
    ∫ b in {b : B | R b ∈ Hset}, a rate rewards C_star C_h u t b j ∂mu =
      ∫ b in {b : B | R b ∈ Hset}, c1 rate rewards C_star C_h u t b j ∂mu := by
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  have hS : MeasurableSet[F_R] {b : B | R b ∈ Hset} :=
    hHset.preimage (comap_measurable _)
  have hce := first_condExp_ae rate rewards C_star C_h u t control0 j
  have hceS : ∀ᵐ b ∂mu, b ∈ {b : B | R b ∈ Hset} →
      mu[(fun b => a rate rewards C_star C_h u t b j) | F_R] b =
        c1 rate rewards C_star C_h u t b j :=
    hce.mono fun b hb _ => hb
  calc
    _ = ∫ b in {b : B | R b ∈ Hset}, mu[((fun b => a rate rewards C_star C_h u t b j)) | F_R] b ∂mu :=
      (setIntegral_condExp hdom
        (integrable_readouts rate rewards C_star C_h u t j).1 hS).symm
    _ = _ := setIntegral_congr_ae (hdom _ hS) hceS

/-- Square-moment equality on every retained-coordinate cylinder, under mu. -/
theorem second_moment_setIntegral (j : Fin p.K) (Hset : Set H)
    (hHset : MeasurableSet Hset) :
    ∫ b in {b : B | R b ∈ Hset}, (a rate rewards C_star C_h u t b j) ^ 2 ∂mu =
      ∫ b in {b : B | R b ∈ Hset}, c2 rate rewards C_star C_h u t b j ∂mu := by
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  have hS : MeasurableSet[F_R] {b : B | R b ∈ Hset} :=
    hHset.preimage (comap_measurable _)
  have hce := second_condExp_ae rate rewards C_star C_h u t control0 j
  have hceS : ∀ᵐ b ∂mu, b ∈ {b : B | R b ∈ Hset} →
      mu[(fun b => (a rate rewards C_star C_h u t b j) ^ 2) | F_R] b =
        c2 rate rewards C_star C_h u t b j :=
    hce.mono fun b hb _ => hb
  calc
    _ = ∫ b in {b : B | R b ∈ Hset},
        mu[(fun b => (a rate rewards C_star C_h u t b j) ^ 2) | F_R] b ∂mu :=
      (setIntegral_condExp hdom
        (integrable_readouts rate rewards C_star C_h u t j).2.1 hS).symm
    _ = _ := setIntegral_congr_ae (hdom _ hS) hceS

/-- The retained-field conditional first moment on the same unnormalized law. -/
theorem condExp_first_moment (j : Fin p.K) :
    mu[((fun b => a rate rewards C_star C_h u t b j)) | F_R] =ᵐ[mu]
      (fun b => c1 rate rewards C_star C_h u t b j) :=
  first_condExp_ae rate rewards C_star C_h u t control0 j

/-- The retained-field conditional square moment on the same unnormalized law. -/
theorem condExp_second_moment (j : Fin p.K) :
    mu[(fun b => (a rate rewards C_star C_h u t b j) ^ 2) | F_R] =ᵐ[mu]
      (fun b => c2 rate rewards C_star C_h u t b j) :=
  second_condExp_ae rate rewards C_star C_h u t control0 j

private theorem same_time_record_eq
    (source : ReferenceFirstCollectionRenewalInstallationCoupling.Source
      rate rewards C_star C_h u t)
    (r₁ r₂ : ReferenceFirstCollectionSamplerCall.RoundRecord p rate)
    (h₁ : r₁ ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source.val rewards C_star C_h) (ht₁ : r₁.input.time = t)
    (h₂ : r₂ ∈ ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source.val rewards C_star C_h) (ht₂ : r₂.input.time = t) : r₁ = r₂ := by
  obtain ⟨n₁, hn₁⟩ := List.mem_iff_getElem?.mp h₁
  obtain ⟨n₂, hn₂⟩ := List.mem_iff_getElem?.mp h₂
  have ht₁' := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate source.val rewards C_star C_h n₁ r₁ hn₁
  have ht₂' := ReferenceFirstCollectionRenewalRecordingFeedback.complete_record_time
    rate source.val rewards C_star C_h n₂ r₂ hn₂
  have hidx : n₁ = n₂ := by
    have h₁val := congrArg Fin.val ht₁
    have h₂val := congrArg Fin.val ht₂
    omega
  subst n₂
  exact Option.some.inj (hn₁.symm.trans hn₂)

/-- The same actual call and recorder identify the gate with the produced
raw-arrival estimator. Record uniqueness uses the complete literal calendar
list; recorder equality is read from the equal actual record outputs. -/
theorem ae_actual_recording_identification :
    ∀ᵐ b : B ∂mu,
      ∃ d : ActualRenewalCall rate rewards C_star C_h u t b.2,
        ∃ recording : CoordinatorRecordingOperation.Output p,
          d.record.output.coordinator.recording = some recording ∧
          v rate rewards C_star C_h u t b =
            AssignmentScoreReconstruction.currentWeight d.out ∧
          (∀ j : Fin p.K, recording.gateArm = some j ↔
            b ∈ gateEvent rate rewards C_star C_h u t j) ∧
          (∀ j : Fin p.K,
            a rate rewards C_star C_h u t b j =
              if recording.gateArm = some j then
                (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ))
              else 0) := by
  filter_upwards
    [ae_actual_recording_gate rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalRecordingFeedback.ae_pairLaw_actual_recording_feedback
        rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalInstallationCoupling.ae_pairLaw_chronological_support
        rate rewards C_star C_h u t] with b hG hN hchron
  dsimp only at hG hN hchron
  rcases hG with ⟨dG, recordingG, hrecordingG, hweightG, hgateG⟩
  rcases hN with ⟨d, consistent, output, hlocal, clockData, installed, selection,
    recording, serviced, hstart, hvector, hreconstruction, hsuccessful, hslow,
    hinSlow, hclock, hins, hanchor, hdispatch, hpreparation, hcoordinator,
    hpostChoice, hrun, hservice, hrecording, hstates, hlive, hpending, hu,
      hsigma, hclockU, hinstalledSigma, hpostFeedback⟩
  rcases hpostFeedback with ⟨hnotFrozen, hraw, hfeedback⟩
  rcases hchron with ⟨_, _, _, _, _, _, _, _, _, hparameterChron, _⟩
  have hrecord : dG.record = d.record := same_time_record_eq rate rewards C_star C_h u t
    b.2 dG.record d.record dG.record_mem dG.time_eq d.record_mem d.time_eq
  have hrecordingOption : dG.record.output.coordinator.recording =
      d.record.output.coordinator.recording :=
    congrArg (fun r : ReferenceFirstCollectionSamplerCall.RoundRecord p rate =>
      r.output.coordinator.recording) hrecord
  have hrecordingEq : recordingG = recording := by
    rw [hrecordingG, hrecording] at hrecordingOption
    exact Option.some.inj hrecordingOption
  have hselectedEq :
      LaterAssignmentStartMeasurability.selectedSamplerParameters
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
            rate u dG.record.input dG.old dG.ledger dG.saved).payload
          (CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u dG.record.input dG.old dG.ledger dG.saved) dG.core.payload_n_eq)
          dG.instruction dG.out dG.reconstruction_eq =
        LaterAssignmentStartMeasurability.selectedSamplerParameters
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
            rate u d.record.input d.old d.ledger d.saved).payload
          (CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u d.record.input d.old d.ledger d.saved) d.core.payload_n_eq)
          d.instruction d.out d.reconstruction_eq := by
    calc
      _ = renewalCallParameter rate rewards C_star C_h u t b.2 := dG.parameter_eq.symm
      _ = _ := d.parameter_eq
  have hweightGsource :
      (renewalCallParameter rate rewards C_star C_h u t b.2).2 =
        AssignmentScoreReconstruction.currentWeight dG.out := by
    calc
      _ = (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 :=
        congrArg Prod.snd hparameterChron.symm
      _ = AssignmentScoreReconstruction.currentWeight dG.out := hweightG
  have hweightG' : v rate rewards C_star C_h u t b =
      AssignmentScoreReconstruction.currentWeight dG.out := by
    change (renewalCallParameter rate rewards C_star C_h u t b.1.1).2 = _
    calc
      _ = (renewalCallParameter rate rewards C_star C_h u t b.2).2 :=
        congrArg Prod.snd hparameterChron
      _ = AssignmentScoreReconstruction.currentWeight dG.out := hweightGsource
  have hsG := (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
      dG.old _ dG.instruction dG.out dG.reconstruction_eq dG.renewal).1
  have hs := (LaterAssignmentStartMeasurability.selectedSamplerParameters_renewal
      d.old _ d.instruction d.out d.reconstruction_eq d.renewal).1
  have hweight : v rate rewards C_star C_h u t b =
      AssignmentScoreReconstruction.currentWeight d.out := by
    calc
      v rate rewards C_star C_h u t b =
          AssignmentScoreReconstruction.currentWeight dG.out := hweightG'
      _ = (LaterAssignmentStartMeasurability.selectedSamplerParameters
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
            rate u dG.record.input dG.old dG.ledger dG.saved).payload
          (CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u dG.record.input dG.old dG.ledger dG.saved) dG.core.payload_n_eq)
          dG.instruction dG.out dG.reconstruction_eq).2 := hsG.symm
      _ = (LaterAssignmentStartMeasurability.selectedSamplerParameters
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
            rate u d.record.input d.old d.ledger d.saved).payload
          (CoordinatorRoundDispatch.collectionOperationLedger
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.collectionView
              rate u d.record.input d.old d.ledger d.saved) d.core.payload_n_eq)
          d.instruction d.out d.reconstruction_eq).2 := congrArg Prod.snd hselectedEq
      _ = AssignmentScoreReconstruction.currentWeight d.out := hs
  have hraw' := hraw
  rw [← hweight] at hraw'
  have hgate : ∀ j : Fin p.K,
      recording.gateArm = some j ↔ b ∈ gateEvent rate rewards C_star C_h u t j := by
    intro j
    rw [← hrecordingEq]
    exact hgateG j
  refine ⟨d, recording, hrecording, hweight, hgate, ?_⟩
  intro j
  by_cases hg : recording.gateArm = some j
  · have hmem : b ∈ gateEvent rate rewards C_star C_h u t j := (hgate j).mp hg
    simp only [hg, if_pos]
    rw [a, Set.indicator_of_mem hmem]
    have hfloor : (recording.rawArrival : ℝ) =
        (Nat.floor (((D p : ℝ) * rate.eta.val * r rewards t j) /
          xi rate rewards C_star C_h u t b j) : ℝ) := by
      have hnat := hraw'
      rw [SnapshotRecordingKernel.recordedIncrement.eq_def, hg] at hnat
      have hcast := congrArg (fun n : ℕ => (n : ℝ)) hnat
      simpa [xi, v, r] using hcast
    calc
      q rate rewards C_star C_h u t b j =
          (Nat.floor (((D p : ℝ) * rate.eta.val * r rewards t j) /
            xi rate rewards C_star C_h u t b j) : ℝ) /
              (rate.eta.val * (D p : ℝ)) := by
        simp [q, QuantizedRecordingMoments.quantizedValue,
          QuantizedRecordingMoments.quantizedIndex]
      _ = (recording.rawArrival : ℝ) / (rate.eta.val * (D p : ℝ)) := by
        rw [← hfloor]
  · have hmem : b ∉ gateEvent rate rewards C_star C_h u t j := by
      intro hmem
      exact hg ((hgate j).mpr hmem)
    simp [a, hmem, hg]

end Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments

end
