/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalQueuePostReadout
public import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds
public import Bandits.Support.ReferenceFirstCollectionRenewalExponentialIncrement
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Actual first-renewal conditional exponential queue step

The observations below exponentiate the existing incoming and post-update
queues on the original unnormalized pair law. The first overflowing update is
retained, and the stopped branch preserves the same queue.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments
open Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments
open Bandits.Support.ReferenceFirstCollectionRenewalControlFactor
open Bandits.Support.ReferenceFirstCollectionRenewalExponentialIncrement
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix
open Bandits.Support.ReferenceFirstCollectionRenewalInstallationCoupling
open Bandits.Support.ReferenceFirstCollectionRenewalQueuePostReadout

namespace Bandits.Support.ReferenceFirstCollectionRenewalExponentialQueueStep

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" =>
  ReferenceFirstCollectionRenewalExponentialIncrement.Pair
    rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t
local notation "R" =>
  ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
    rate rewards C_star C_h u t control0
local notation "F_R" => MeasurableSpace.comap R
  (inferInstance : MeasurableSpace
    (ReferenceFirstCollectionRenewalExponentialIncrement.RetainedCoordinates p))
local notation "G" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

/-- Exponential of the actual incoming normalized queue for one arm. -/
def XMinus (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
    rate rewards C_star C_h u t control0 j b)

/-- Exponential of the literal post-update normalized queue for one arm. -/
def XPlus (j : Fin p.K) (b : B) : ℝ :=
  Real.exp (beta * ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
    rate rewards C_star C_h u t b j)

/-- The retained event indicator, on the same pair carrier and retained field. -/
def indicatorG (b : B) : ℝ := Set.indicator G (fun _ : B => (1 : ℝ)) b

private theorem beta_floor : 32 * rate.eta.val ≤ beta := by
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  rw [CanonicalRecordingRates.beta]
  calc
    32 * rate.eta.val = (32 * rate.eta.val) * 1 := by ring
    _ ≤ (32 * rate.eta.val) * (CanonicalRecordingRates.L_stab p : ℝ) :=
      mul_le_mul_of_nonneg_left hL (le_of_lt (mul_pos (by norm_num) rate.eta.property))

private theorem one_div_beta_le_Bcap :
    1 / beta ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0 := by
  have hη : 0 < rate.eta.val := rate.eta.property
  have hη32 : 0 < 32 * rate.eta.val := mul_pos (by norm_num) hη
  rw [ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap]
  change 1 / beta ≤ 1 / (32 * rate.eta.val)
  exact one_div_le_one_div_of_le hη32 (beta_floor rate)

private theorem retainedField_le :
    F_R ≤ (inferInstance : MeasurableSpace B) :=
  ReferenceFirstCollectionRenewalComplementMoments.retainedField_le
    rate rewards C_star C_h u t control0

private theorem measurableSet_G_R_ambient : MeasurableSet G := by
  have hfield :=
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
      rate rewards C_star C_h u t control0
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  rcases hfield with ⟨S, hS, hpre⟩
  have hR : Measurable R := (comap_measurable R).mono hdom le_rfl
  rw [← hpre]
  exact hS.preimage hR

/-- On the original pair law, the retained field event is exactly the
incoming no-overflow branch almost everywhere. -/
theorem ae_G_iff_incoming_noOverflow :
    ∀ᵐ b : B ∂mu,
      b ∈ G ↔
        (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2).overflow = false := by
  filter_upwards [ReferenceFirstCollectionRenewalAcceptedComplementMoments.ae_actual_strict_past_identification
    rate rewards C_star C_h u t control0]
      with b hstrict
  exact hstrict.trans
    (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming_noOverflow_iff_firstOverflow
      rate rewards C_star C_h u t b.2).symm

/-- The actual post backlog is the reflected retained-increment update, AE
simultaneously for every arm. The event uses the incoming overflow flag, so
the update that first overflows is included; an already stopped queue is
preserved. -/
theorem ae_backlogAfter_eq_reflected_increment :
    ∀ᵐ b : B ∂mu,
      ∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
            rate rewards C_star C_h u t b j =
          max (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b +
            ReferenceFirstCollectionRenewalExponentialIncrement.retainedIncrement
              rate rewards C_star C_h u t control0 j b) 0 := by
  filter_upwards [ReferenceFirstCollectionRenewalQueuePostReadout.ae_actual_postReadout_identity
      rate rewards C_star C_h u t control0,
    ae_G_iff_incoming_noOverflow rate rewards C_star C_h u t control0]
      with b _hactual hG
  intro j
  by_cases hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = false
  · have hmem : b ∈ G := hG.mpr hf
    rw [ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_noOverflow
        rate rewards C_star C_h u t b j hf,
      ReferenceFirstCollectionRenewalExponentialIncrement.retainedIncrement_eq_acceptedA_sub_four_of_mem_G
        rate rewards C_star C_h u t control0 j b hmem]
    congr 1
    dsimp [ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus,
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogBefore]
    ring
  · have htrue : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = true := by
      cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow <;> simp_all
    have hnot : b ∉ G := by
      intro hmem
      have := hG.mp hmem
      simp [htrue] at this
    rw [ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_overflow
        rate rewards C_star C_h u t b j htrue,
      ReferenceFirstCollectionRenewalExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
        rate rewards C_star C_h u t control0 j b hnot]
    have hbacknonneg :
        0 ≤ ((ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
          rate rewards C_star C_h u t b.2).registers j).2 / (rate.n : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_pos.mpr
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos).le
    simp [ReferenceFirstCollectionRenewalQueuePostReadout.backlogBefore,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus,
      max_eq_left hbacknonneg]

/-- The source queue envelopes include both the enabled update and the
absorbing stopped branch. -/
theorem backlogAfter_bounds (j : Fin p.K) (b : B) :
    0 ≤ ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ∧
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
          rate rewards C_star C_h u t b j ≤
        2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 := by
  have hnonneg : 0 ≤ ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
      rate rewards C_star C_h u t b j := by
    unfold ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
    exact div_nonneg (Nat.cast_nonneg _)
      (Nat.cast_pos.mpr
        (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos).le
  by_cases hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = false
  · have hpre := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_Bcap_of_noOverflow
      rate rewards C_star C_h u t control0 j b hf
    have harrival := ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA_bounds
      rate rewards C_star C_h u t b j
    rw [ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_noOverflow
      rate rewards C_star C_h u t b j hf]
    constructor
    · exact le_max_right _ _
    · calc
        max (ReferenceFirstCollectionRenewalQueuePostReadout.backlogBefore
            rate rewards C_star C_h u t b j +
          ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
            rate rewards C_star C_h u t j b - 4) 0 ≤
            ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b + 1 / beta := by
          apply max_le
          · dsimp [ReferenceFirstCollectionRenewalQueuePostReadout.backlogBefore,
              ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus]
            linarith [harrival.2]
          · exact add_nonneg
              (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
                rate rewards C_star C_h u t control0 j b)
              (le_of_lt (one_div_pos.mpr
                (ReferenceFirstCollectionRenewalExponentialIncrement.beta_pos rate)))
        _ ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0 +
            ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0 :=
          add_le_add hpre (one_div_beta_le_Bcap rate rewards C_star C_h u t control0)
        _ = 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0 := by ring
  · have htrue : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = true := by
      cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow <;> simp_all
    rw [ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_overflow
      rate rewards C_star C_h u t b j htrue]
    simpa [ReferenceFirstCollectionRenewalQueuePostReadout.backlogBefore,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus] using
      ⟨ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
          rate rewards C_star C_h u t control0 j b,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_two_Bcap
          rate rewards C_star C_h u t control0 j b⟩

/-- The incoming exponential has a fixed finite envelope on the full pair
carrier. -/
theorem XMinus_bounds (j : Fin p.K) (b : B) :
    1 ≤ XMinus rate rewards C_star C_h u t control0 j b ∧
      XMinus rate rewards C_star C_h u t control0 j b ≤
        Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0)) := by
  have hβ := ReferenceFirstCollectionRenewalExponentialIncrement.beta_pos rate
  have hback := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_two_Bcap
    rate rewards C_star C_h u t control0 j b
  have hback0 := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
    rate rewards C_star C_h u t control0 j b
  constructor
  · apply Real.one_le_exp_iff.mpr
    exact mul_nonneg hβ.le hback0
  · apply Real.exp_le_exp_of_le
    exact mul_le_mul_of_nonneg_left hback (le_of_lt hβ)

/-- The post-update exponential has the same fixed finite envelope, including
the first overflow update and every later preserved state. -/
theorem XPlus_bounds (j : Fin p.K) (b : B) :
    1 ≤ XPlus rate rewards C_star C_h u t j b ∧
      XPlus rate rewards C_star C_h u t j b ≤
        Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0)) := by
  have hβ := ReferenceFirstCollectionRenewalExponentialIncrement.beta_pos rate
  have hback := backlogAfter_bounds rate rewards C_star C_h u t control0 j b
  constructor
  · apply Real.one_le_exp_iff.mpr
    exact mul_nonneg hβ.le hback.1
  · apply Real.exp_le_exp_of_le
    exact mul_le_mul_of_nonneg_left hback.2 (le_of_lt hβ)

theorem measurable_XMinus (j : Fin p.K) :
    Measurable (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) := by
  have hb := ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinus
    rate rewards C_star C_h u t control0 j
  have hscaled : Measurable (fun b : B => beta *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b) :=
    (measurable_const : Measurable (fun _ : B => beta)).mul hb
  simpa [XMinus] using hscaled.exp

theorem measurable_XPlus (j : Fin p.K) :
    Measurable (fun b : B => XPlus rate rewards C_star C_h u t j b) := by
  have hmap : Measurable (fun registers : Fin p.K → ℕ × ℕ =>
      Real.exp (beta * ((registers j).2 : ℝ) /
        (rate.n : ℝ))) := measurable_of_countable _
  have hpost := ReferenceFirstCollectionRenewalQueuePostReadout.measurable_postRegisters
    rate rewards C_star C_h u t
  have h := hmap.comp hpost
  convert h using 1
  funext b
  dsimp [XPlus, ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter]
  congr 1
  ring

private theorem integrable_of_bounded_measurable {f : B → ℝ}
    (hf : Measurable f) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ b, ‖f b‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : B => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with b
  simpa [Real.norm_eq_abs, abs_of_nonneg _hC] using hbound b

/-- The incoming exponential is integrable by its deterministic queue
envelope on the finite unnormalized pair law. -/
theorem integrable_XMinus (j : Fin p.K) :
    Integrable (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_bounded_measurable rate rewards C_star C_h u t
    (measurable_XMinus rate rewards C_star C_h u t control0 j)
    (Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0)))
  · positivity
  · intro b
    have h := XMinus_bounds rate rewards C_star C_h u t control0 j b
    rw [Real.norm_of_nonneg (le_trans (by norm_num) h.1)]
    exact h.2

/-- The post-update exponential is integrable by its deterministic queue
envelope on the same finite unnormalized pair law. -/
theorem integrable_XPlus (_control0 : TimeControl p) (j : Fin p.K) :
    Integrable (fun b : B => XPlus rate rewards C_star C_h u t j b) mu := by
  apply integrable_of_bounded_measurable rate rewards C_star C_h u t
    (measurable_XPlus rate rewards C_star C_h u t j)
    (Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t _control0)))
  · positivity
  · intro b
    have h := XPlus_bounds rate rewards C_star C_h u t _control0 j b
    rw [Real.norm_of_nonneg (le_trans (by norm_num) h.1)]
    exact h.2

/-- The incoming exponential is adapted to the exact retained-control
comap field. Its representative is built from the retained incoming backlog;
only its AE equality, not pointwise adaptation of the arbitrary pair source,
is used. -/
theorem aestronglyMeasurable_XMinus (j : Fin p.K) :
    AEStronglyMeasurable[F_R]
      (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) mu := by
  let xretained : B → ℝ := fun b => Real.exp (beta *
    ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinusRetained
      rate rewards C_star C_h u t control0 j b)
  have hback := ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinusRetained
    rate rewards C_star C_h u t control0 j
  have hscaled : Measurable[F_R] (fun b : B => beta *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinusRetained
        rate rewards C_star C_h u t control0 j b) :=
    (measurable_const : Measurable[F_R] (fun _ : B => beta)).mul hback
  have hret : AEStronglyMeasurable[F_R] xretained mu := by
    have hm : Measurable[F_R] xretained := by
      simpa [xretained] using hscaled.exp
    exact hm.aestronglyMeasurable
  have heq : (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) =ᵐ[mu]
      xretained := by
    filter_upwards [ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_bMinus_eq_retained
      rate rewards C_star C_h u t control0 j] with b hb
    simp [XMinus, xretained, hb]
  exact hret.congr heq.symm

/-- The product needed by conditional pull-out is integrable from the fixed
envelopes, without an assumed factorization or conditional-expectation input. -/
theorem integrable_XMinus_mul_expRetainedIncrement (j : Fin p.K) :
    Integrable
      (fun b : B => XMinus rate rewards C_star C_h u t control0 j b *
        ReferenceFirstCollectionRenewalExponentialIncrement.expRetainedIncrement
          rate rewards C_star C_h u t control0 j b) mu := by
  have hX := XMinus_bounds rate rewards C_star C_h u t control0 j
  have hmX : AEStronglyMeasurable
      (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) mu :=
    (measurable_XMinus rate rewards C_star C_h u t control0 j).aestronglyMeasurable
  have hbound : ∀ᵐ b ∂mu,
      ‖XMinus rate rewards C_star C_h u t control0 j b‖ ≤
        Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0)) := by
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (le_trans (by norm_num) (hX b).1)]
    exact (hX b).2
  have hE := ReferenceFirstCollectionRenewalExponentialIncrement.integrable_expRetainedIncrement
    rate rewards C_star C_h u t control0 j
  exact hE.bdd_mul hmX hbound

private theorem measurable_indicatorG :
    Measurable (indicatorG rate rewards C_star C_h u t control0) := by
  have hG := measurableSet_G_R_ambient rate rewards C_star C_h u t control0
  exact measurable_const.indicator hG

private theorem integrable_indicatorG :
    Integrable (indicatorG rate rewards C_star C_h u t control0) mu := by
  change Integrable (Set.indicator G (fun _ : B => (1 : ℝ))) mu
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_G_R_ambient rate rewards C_star C_h u t control0)

private theorem exp_max_add_le (β x y : ℝ) :
    Real.exp (β * max (x + y) 0) ≤ 1 + Real.exp (β * x) * Real.exp (β * y) := by
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

/-- The one-step exponential majorant keeps the incoming cost unmasked: on
the retained event it pays one plus the incoming exponential times the
accepted increment exponential, and off that event the queue is preserved. -/
theorem ae_XPlus_le_indicatorG_add_product (j : Fin p.K) :
    (fun b : B => XPlus rate rewards C_star C_h u t j b) ≤ᵐ[mu]
      (fun b => indicatorG rate rewards C_star C_h u t control0 b +
        XMinus rate rewards C_star C_h u t control0 j b *
          ReferenceFirstCollectionRenewalExponentialIncrement.expRetainedIncrement
            rate rewards C_star C_h u t control0 j b) := by
  filter_upwards [ae_backlogAfter_eq_reflected_increment
    rate rewards C_star C_h u t control0] with b hrec
  by_cases hG : b ∈ G
  · have hinc := ReferenceFirstCollectionRenewalExponentialIncrement.retainedIncrement_eq_acceptedA_sub_four_of_mem_G
        rate rewards C_star C_h u t control0 j b hG
    have hmax := exp_max_add_le beta
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b)
      (ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
        rate rewards C_star C_h u t j b - 4)
    have harg :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b +
          ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
            rate rewards C_star C_h u t j b - 4 =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b +
          (ReferenceFirstCollectionRenewalAcceptedComplementMoments.acceptedA
            rate rewards C_star C_h u t j b - 4) := by ring
    simpa [XPlus, XMinus, indicatorG, Set.indicator, hG, hrec j, hinc, harg,
      ReferenceFirstCollectionRenewalExponentialIncrement.expRetainedIncrement] using hmax
  · have hinc := ReferenceFirstCollectionRenewalExponentialIncrement.retainedIncrement_eq_zero_of_not_mem_G
        rate rewards C_star C_h u t control0 j b hG
    have hback :
        ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
            rate rewards C_star C_h u t b j =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b := by
      rw [hrec j, hinc]
      simp [max_eq_left (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
        rate rewards C_star C_h u t control0 j b)]
    simp [XPlus, XMinus, indicatorG, Set.indicator, hG, hback, hinc,
      ReferenceFirstCollectionRenewalExponentialIncrement.expRetainedIncrement]

/-- Conditional exponential backlog step on the original finite,
unnormalized pair law. The only inputs are the three existing queue/readout
and increment producers; no separate conditional law is assumed. -/
theorem condExp_XPlus_le_XMinus_add_indicatorG (j : Fin p.K) :
    mu[(fun b : B => XPlus rate rewards C_star C_h u t j b) | F_R] ≤ᵐ[mu]
      (fun b : B => XMinus rate rewards C_star C_h u t control0 j b +
        indicatorG rate rewards C_star C_h u t control0 b) := by
  let y : B → ℝ := fun b =>
    ReferenceFirstCollectionRenewalExponentialIncrement.expRetainedIncrement
      rate rewards C_star C_h u t control0 j b
  let prod : B → ℝ := fun b => XMinus rate rewards C_star C_h u t control0 j b * y b
  let majorant : B → ℝ := fun b =>
    indicatorG rate rewards C_star C_h u t control0 b + prod b
  have hGfield : MeasurableSet[F_R] G :=
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurableSet_G_R
      rate rewards C_star C_h u t control0
  have hGint := integrable_indicatorG rate rewards C_star C_h u t control0
  have hXminus := integrable_XMinus rate rewards C_star C_h u t control0 j
  have hXplus := integrable_XPlus rate rewards C_star C_h u t control0 j
  have hy := ReferenceFirstCollectionRenewalExponentialIncrement.integrable_expRetainedIncrement
    rate rewards C_star C_h u t control0 j
  have hprod : Integrable prod mu := by
    simpa [prod, y] using integrable_XMinus_mul_expRetainedIncrement
      rate rewards C_star C_h u t control0 j
  have hmajorant : Integrable majorant mu := hGint.add hprod
  have hpoint :
      (fun b : B => XPlus rate rewards C_star C_h u t j b) ≤ᵐ[mu]
        majorant := by
    simpa [majorant, prod, y] using ae_XPlus_le_indicatorG_add_product
      rate rewards C_star C_h u t control0 j
  have hmono := condExp_mono (m := F_R) hXplus hmajorant hpoint
  have hAdd := condExp_add hGint hprod F_R
  have hOneIntegrable : Integrable (fun _ : B => (1 : ℝ)) mu := integrable_const 1
  have hMask := condExp_indicator (μ := mu) (m := F_R) hOneIntegrable hGfield
  have hConst :
      mu[(fun _ : B => (1 : ℝ)) | F_R] = (fun _ : B => (1 : ℝ)) :=
    condExp_const (μ := mu) (m := F_R)
      (m₀ := (inferInstance : MeasurableSpace B))
      (retainedField_le rate rewards C_star C_h u t control0) (1 : ℝ)
  have hIndicatorCE :
      mu[(fun b : B => indicatorG rate rewards C_star C_h u t control0 b) | F_R] =ᵐ[mu]
        (fun b : B => indicatorG rate rewards C_star C_h u t control0 b) := by
    filter_upwards [hMask] with b hb
    rw [hConst] at hb
    simpa [indicatorG] using hb
  have hPull := condExp_mul_of_aestronglyMeasurable_left
    (aestronglyMeasurable_XMinus rate rewards C_star C_h u t control0 j)
    hprod hy
  have hPullProd : mu[prod | F_R] =ᵐ[mu]
      (fun b : B => XMinus rate rewards C_star C_h u t control0 j b * mu[y | F_R] b) := by
    have hleft : prod = (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) * y := by
      funext b
      rfl
    have hright :
        (fun b : B => XMinus rate rewards C_star C_h u t control0 j b * mu[y | F_R] b) =
          (fun b : B => XMinus rate rewards C_star C_h u t control0 j b) * mu[y | F_R] := by
      funext b
      rfl
    rw [hleft, hright]
    exact hPull
  have hYce := ReferenceFirstCollectionRenewalExponentialIncrement.expRetainedIncrement_condExp_le_one
    rate rewards C_star C_h u t control0 j
  have hXnonneg : ∀ᵐ b ∂mu,
      0 ≤ XMinus rate rewards C_star C_h u t control0 j b := by
    filter_upwards [] with b
    exact le_trans (by norm_num)
      (XMinus_bounds rate rewards C_star C_h u t control0 j b).1
  filter_upwards [hmono, hAdd, hIndicatorCE, hPullProd, hYce, hXnonneg]
      with b hmono_b hAdd_b hMask_b hPull_b hYce_b hXnonneg_b
  calc
    mu[(fun x : B => XPlus rate rewards C_star C_h u t j x) | F_R] b ≤
        mu[majorant | F_R] b := hmono_b
    _ = mu[(fun x : B => indicatorG rate rewards C_star C_h u t control0 x) | F_R] b +
        mu[prod | F_R] b := hAdd_b
    _ = indicatorG rate rewards C_star C_h u t control0 b +
        XMinus rate rewards C_star C_h u t control0 j b * mu[y | F_R] b := by
      rw [hMask_b, hPull_b]
    _ = XMinus rate rewards C_star C_h u t control0 j b * mu[y | F_R] b +
        indicatorG rate rewards C_star C_h u t control0 b := by ring
    _ ≤ XMinus rate rewards C_star C_h u t control0 j b * 1 +
        indicatorG rate rewards C_star C_h u t control0 b :=
      add_le_add_left (mul_le_mul_of_nonneg_left hYce_b hXnonneg_b) _
    _ = XMinus rate rewards C_star C_h u t control0 j b +
        indicatorG rate rewards C_star C_h u t control0 b := by ring
    _ = XMinus rate rewards C_star C_h u t control0 j b +
        indicatorG rate rewards C_star C_h u t control0 b := by ring

/-- The coarser source-style one-step estimate follows from the stronger
retained-cost estimate. -/
theorem condExp_XPlus_le_one_add_XMinus (j : Fin p.K) :
    mu[(fun b : B => XPlus rate rewards C_star C_h u t j b) | F_R] ≤ᵐ[mu]
      (fun b : B => 1 + XMinus rate rewards C_star C_h u t control0 j b) := by
  have h := condExp_XPlus_le_XMinus_add_indicatorG
    rate rewards C_star C_h u t control0 j
  have hGle : ∀ b : B,
      indicatorG rate rewards C_star C_h u t control0 b ≤ 1 := by
    intro b
    by_cases hb : b ∈ G <;> simp [indicatorG, hb]
  filter_upwards [h] with b hb
  linarith [hGle b]

/-- A weighted integral form for any nonnegative integrable test function
that is measurable with respect to the same retained-control field. -/
theorem integral_mul_XPlus_le (j : Fin p.K) {H : B → ℝ}
    (hHmeas : AEStronglyMeasurable[F_R] H mu)
    (hHnonneg : 0 ≤ᵐ[mu] H) (hHint : Integrable H mu) :
    (∫ b : B, H b * XPlus rate rewards C_star C_h u t j b ∂mu) ≤
      (∫ b : B, H b * XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
        ∫ b : B, H b * indicatorG rate rewards C_star C_h u t control0 b ∂mu := by
  have hXminus_bound : ∀ᵐ b ∂mu,
      ‖XMinus rate rewards C_star C_h u t control0 j b‖ ≤
        Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0)) := by
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (le_trans (by norm_num)
      (XMinus_bounds rate rewards C_star C_h u t control0 j b).1)]
    exact (XMinus_bounds rate rewards C_star C_h u t control0 j b).2
  have hXplus_bound : ∀ᵐ b ∂mu,
      ‖XPlus rate rewards C_star C_h u t j b‖ ≤
        Real.exp (beta * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0)) := by
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (le_trans (by norm_num)
      (XPlus_bounds rate rewards C_star C_h u t control0 j b).1)]
    exact (XPlus_bounds rate rewards C_star C_h u t control0 j b).2
  have hHplus : Integrable
      (fun b : B => H b * XPlus rate rewards C_star C_h u t j b) mu :=
    hHint.mul_bdd
      (measurable_XPlus rate rewards C_star C_h u t j).aestronglyMeasurable
      hXplus_bound
  have hHminus : Integrable
      (fun b : B => H b * XMinus rate rewards C_star C_h u t control0 j b) mu :=
    hHint.mul_bdd
      (measurable_XMinus rate rewards C_star C_h u t control0 j).aestronglyMeasurable
      hXminus_bound
  have hHindicator_bound : ∀ᵐ b ∂mu,
      ‖indicatorG rate rewards C_star C_h u t control0 b‖ ≤ 1 := by
    filter_upwards [] with b
    have hnonneg : 0 ≤ indicatorG rate rewards C_star C_h u t control0 b := by
      by_cases hb : b ∈ G <;> simp [indicatorG, hb]
    have hle : indicatorG rate rewards C_star C_h u t control0 b ≤ 1 := by
      by_cases hb : b ∈ G <;> simp [indicatorG, hb]
    rw [Real.norm_of_nonneg hnonneg]
    exact hle
  have hHindicator : Integrable
      (fun b : B => H b * indicatorG rate rewards C_star C_h u t control0 b) mu :=
    hHint.mul_bdd
      (measurable_indicatorG rate rewards C_star C_h u t control0).aestronglyMeasurable
      hHindicator_bound
  have hPull := condExp_mul_of_aestronglyMeasurable_left hHmeas hHplus
    (integrable_XPlus rate rewards C_star C_h u t control0 j)
  have hdom := retainedField_le rate rewards C_star C_h u t control0
  have hCEweighted : Integrable
      (fun b : B => H b *
        mu[(fun x : B => XPlus rate rewards C_star C_h u t j x) | F_R] b) mu :=
    (integrable_condExp (μ := mu) (m := F_R) (f := fun b : B =>
      H b * XPlus rate rewards C_star C_h u t j b)).congr hPull
  have hpoint :
      (fun b : B => H b *
        mu[(fun x : B => XPlus rate rewards C_star C_h u t j x) | F_R] b) ≤ᵐ[mu]
      (fun b : B => H b * (XMinus rate rewards C_star C_h u t control0 j b +
        indicatorG rate rewards C_star C_h u t control0 b)) := by
    filter_upwards [condExp_XPlus_le_XMinus_add_indicatorG
      rate rewards C_star C_h u t control0 j, hHnonneg] with b hce hH
    exact mul_le_mul_of_nonneg_left hce hH
  have hright : Integrable
      (fun b : B => H b * (XMinus rate rewards C_star C_h u t control0 j b +
        indicatorG rate rewards C_star C_h u t control0 b)) mu := by
    have h := hHminus.add hHindicator
    exact h.congr (Filter.Eventually.of_forall fun b => by
      change H b * XMinus rate rewards C_star C_h u t control0 j b +
        H b * indicatorG rate rewards C_star C_h u t control0 b =
          H b * (XMinus rate rewards C_star C_h u t control0 j b +
            indicatorG rate rewards C_star C_h u t control0 b)
      rw [mul_add])
  calc
    (∫ b : B, H b * XPlus rate rewards C_star C_h u t j b ∂mu) =
        ∫ b : B, H b *
          mu[(fun x : B => XPlus rate rewards C_star C_h u t j x) | F_R] b ∂mu := by
      calc
        _ = ∫ b : B,
            mu[(fun x : B => H x * XPlus rate rewards C_star C_h u t j x) | F_R] b ∂mu :=
          (integral_condExp hdom).symm
        _ = _ := integral_congr_ae hPull
    _ ≤ ∫ b : B, H b *
        (XMinus rate rewards C_star C_h u t control0 j b +
          indicatorG rate rewards C_star C_h u t control0 b) ∂mu :=
      integral_mono_ae hCEweighted hright hpoint
    _ = (∫ b : B, H b * XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
        ∫ b : B, H b * indicatorG rate rewards C_star C_h u t control0 b ∂mu := by
      calc
        _ = ∫ b : B,
            (H b * XMinus rate rewards C_star C_h u t control0 j b) +
              (H b * indicatorG rate rewards C_star C_h u t control0 b) ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with b
          rw [mul_add]
        _ = _ := integral_add hHminus hHindicator

/-- Integrating the conditional step gives the retained-event cost with its
actual mass on the same unnormalized pair law. -/
theorem integral_XPlus_le_integral_XMinus_add_G (j : Fin p.K) :
    (∫ b : B, XPlus rate rewards C_star C_h u t j b ∂mu) ≤
      (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
        (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real G := by
  have h := integral_mul_XPlus_le rate rewards C_star C_h u t control0 j
    (H := fun _ : B => (1 : ℝ))
    (by exact stronglyMeasurable_const.aestronglyMeasurable :
      AEStronglyMeasurable[F_R] (fun _ : B => (1 : ℝ)) mu)
    (Filter.Eventually.of_forall fun _ => by norm_num) (integrable_const (1 : ℝ))
  have h' :
      (∫ b : B, XPlus rate rewards C_star C_h u t j b ∂mu) ≤
        (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
          ∫ b : B, Set.indicator G (fun _ : B => (1 : ℝ)) b ∂mu := by
    simpa only [one_mul, indicatorG] using h
  have hind :
      (∫ b : B, Set.indicator G (fun _ : B => (1 : ℝ)) b ∂mu) =
        (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real G := by
    rw [integral_indicator_const (1 : ℝ)
      (measurableSet_G_R_ambient rate rewards C_star C_h u t control0)]
    simp
  rw [hind] at h'
  exact h'

/-- The retained-event cost is at most the total mass of the original pair
law; no event-mass division or zero-mass exclusion is used. -/
theorem integral_XPlus_le_integral_XMinus_add_univ (j : Fin p.K) :
    (∫ b : B, XPlus rate rewards C_star C_h u t j b ∂mu) ≤
      (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
        (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real Set.univ := by
  calc
    (∫ b : B, XPlus rate rewards C_star C_h u t j b ∂mu) ≤
        (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
          (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
            rate rewards C_star C_h u t).real G :=
      integral_XPlus_le_integral_XMinus_add_G
        rate rewards C_star C_h u t control0 j
    _ = (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real G +
        (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) := by ring
    _ ≤ (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real Set.univ +
        (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) :=
      add_le_add_left
        (measureReal_mono (μ := ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t) (Set.subset_univ G) (by finiteness))
        (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu)
    _ = (∫ b : B, XMinus rate rewards C_star C_h u t control0 j b ∂mu) +
        (ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
          rate rewards C_star C_h u t).real Set.univ := by ring

end Bandits.Support.ReferenceFirstCollectionRenewalExponentialQueueStep

end
