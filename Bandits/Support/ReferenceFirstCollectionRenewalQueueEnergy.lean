/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalQueuePostReadout
public import Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# First-renewal actual weighted queue energy

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:93-188,245-318`,
`sources/zip4/manuscript/05_binary_transport.tex:352-431`, and
`sources/zip4/manuscript/06_interruptions.tex:399-426`.

The post energy reads the integer registers of the existing accepted queue
step. Its same-call, same-recording actual characterization is inherited from
the public post-readout identity on the original finite unnormalized pair law.
Incoming overflow disables the next update; an update that first overflows is
retained.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix
open Bandits.Support.ReferenceFirstCollectionRenewalQueuePostReadout
open Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds

namespace Bandits.Support.ReferenceFirstCollectionRenewalQueueEnergy

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
variable (control0 : ContinuousLearningRows.TimeControl p)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" =>
  ReferenceFirstCollectionRenewalAcceptedComplementMoments.Pair
    rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t
local notation "qp" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "G" =>
  ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
    rate rewards C_star C_h u t control0
local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

/-- The post-update `m`-element inclusion marginal of the actual score
registers. -/
def thetaPlus (b : B) (j : Fin p.K) : ℝ :=
  ProductSetLaw.theta p.m
    (fun i => ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
      rate rewards C_star C_h u t b i) j

/-- The post-update weighted quadratic energy on the unchanged pair carrier. -/
def VPlus (b : B) : ℝ :=
  ∑ j : Fin p.K, thetaPlus rate rewards C_star C_h u t b j *
    ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
      rate rewards C_star C_h u t b j ^ 2

private theorem beta_floor :
    32 * rate.eta.val ≤ CanonicalRecordingRates.beta p rate.eta.val := by
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  rw [CanonicalRecordingRates.beta]
  nlinarith [rate.eta.property]

private theorem beta_pos :
    0 < CanonicalRecordingRates.beta p rate.eta.val :=
  lt_of_lt_of_le (mul_pos (by norm_num) rate.eta.property) (beta_floor rate)

private theorem arrival_le_Bcap (b : B) (j : Fin p.K) :
    acceptedA rate rewards C_star C_h u t j b ≤
      ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
        rate rewards C_star C_h u t control0 := by
  have ha := acceptedA_bounds rate rewards C_star C_h u t b j
  have hrecip :
      1 / CanonicalRecordingRates.beta p rate.eta.val ≤
        1 / (32 * rate.eta.val) :=
    one_div_le_one_div_of_le (mul_pos (by norm_num) rate.eta.property)
      (beta_floor rate)
  simpa [ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap] using
    ha.2.trans hrecip

/-- Every post backlog is nonnegative and obeys the stopped queue's global
two-cap envelope. -/
theorem backlogAfter_bounds (b : B) (j : Fin p.K) :
    0 ≤ ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ∧
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ≤
          2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 := by
  let bplus := ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
    rate rewards C_star C_h u t b j
  let bminus := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
    rate rewards C_star C_h u t control0 j b
  have hn : 0 < (rate.n : ℝ) :=
    Nat.cast_pos.mpr (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
  have hbplus0 : 0 ≤ bplus := by
    dsimp [bplus, ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter]
    exact div_nonneg (Nat.cast_nonneg _ ) hn.le
  constructor
  · exact hbplus0
  · by_cases hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow = true
    · have hpres := ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_overflow
        rate rewards C_star C_h u t b j hf
      have hbound := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_two_Bcap
        rate rewards C_star C_h u t control0 j b
      simpa [bplus, bminus] using hpres ▸ hbound
    · have hf' : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow = false := by
        cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow <;> simp_all
      have hrec := ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_noOverflow
        rate rewards C_star C_h u t b j hf'
      have hbefore :=
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_Bcap_of_noOverflow
          rate rewards C_star C_h u t control0 j b hf'
      have ha := arrival_le_Bcap rate rewards C_star C_h u t control0 b j
      have hsum : bminus + acceptedA rate rewards C_star C_h u t j b ≤
          2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 := by linarith
      have hmax : max (bminus + acceptedA rate rewards C_star C_h u t j b - 4) 0 ≤
          bminus + acceptedA rate rewards C_star C_h u t j b := by
        apply max_le
        · linarith
        · exact add_nonneg
            (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
              rate rewards C_star C_h u t control0 j b)
            (acceptedA_bounds rate rewards C_star C_h u t b j).1
      simpa [bplus, bminus] using hrec ▸ hmax.trans hsum

/-- The post score weights stay positive, so their full `m`-element
inclusion marginals retain the original total mass. -/
theorem thetaPlus_bounds (b : B) (j : Fin p.K) :
    0 ≤ thetaPlus rate rewards C_star C_h u t b j ∧
      thetaPlus rate rewards C_star C_h u t b j ≤ 1 := by
  unfold thetaPlus
  apply And.intro
  · exact (ProductSetLaw.theta_pos
      (fun i => ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        rate rewards C_star C_h u t b i) j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (fun i => by
        unfold ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        positivity)).le
  · exact (ProductSetLaw.theta_lt_one
      (fun i => ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        rate rewards C_star C_h u t b i) j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (fun i => by
        unfold ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        positivity)).le

private theorem Bcap_nonneg :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0 := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
  exact le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) rate.eta.property))

theorem sum_thetaPlus (b : B) :
    (∑ j : Fin p.K, thetaPlus rate rewards C_star C_h u t b j) =
      (p.m : ℝ) := by
  unfold thetaPlus
  apply ProductSetLaw.sum_theta_eq_card
  · exact Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)
  · exact p.m_lt_K
  · intro j
    unfold ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
    positivity

/-- The post energy is bounded by the full `m`-element marginal mass and the
stopped two-cap backlog envelope. -/
theorem VPlus_bounds (b : B) :
    0 ≤ VPlus rate rewards C_star C_h u t b ∧
      VPlus rate rewards C_star C_h u t b ≤
        (p.m : ℝ) *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0) ^ 2 := by
  have hcap : 0 ≤ 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0 := mul_nonneg (by norm_num)
        (Bcap_nonneg rate rewards C_star C_h u t control0)
  constructor
  · unfold VPlus
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (thetaPlus_bounds rate rewards C_star C_h u t b j).1
      (sq_nonneg _)
  · calc
      VPlus rate rewards C_star C_h u t b ≤
          ∑ j : Fin p.K, thetaPlus rate rewards C_star C_h u t b j *
            (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0) ^ 2 := by
        unfold VPlus
        apply Finset.sum_le_sum
        intro j hj
        have hb := backlogAfter_bounds rate rewards C_star C_h u t control0 b j
        have ht := thetaPlus_bounds rate rewards C_star C_h u t b j
        have hsq :
            ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
              rate rewards C_star C_h u t b j ^ 2 ≤
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0) ^ 2 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hb.2)
            (add_nonneg hcap hb.1)]
        exact mul_le_mul_of_nonneg_left hsq ht.1
      _ = (∑ j : Fin p.K,
            thetaPlus rate rewards C_star C_h u t b j) *
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
                rate rewards C_star C_h u t control0) ^ 2 := by
        rw [Finset.sum_mul]
      _ = (p.m : ℝ) *
            (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
              rate rewards C_star C_h u t control0) ^ 2 := by
        rw [sum_thetaPlus]

private theorem measurable_postRegisters :
    Measurable (ReferenceFirstCollectionRenewalQueuePostReadout.postRegisters
      rate rewards C_star C_h u t) := by
  exact (measurable_fst.comp
    (ReferenceFirstCollectionRenewalQueuePostReadout.measurable_postReadout
      rate rewards C_star C_h u t))

private theorem measurable_backlogAfter (j : Fin p.K) :
    Measurable (fun b : B =>
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j) := by
  have hmap : Measurable (fun registers : Fin p.K → ℕ × ℕ =>
      (registers j).2 / (rate.n : ℝ)) := measurable_of_countable _
  have hcomp := hmap.comp (measurable_postRegisters rate rewards C_star C_h u t)
  convert hcomp using 1
  funext b
  rfl

theorem measurable_thetaPlus (j : Fin p.K) :
    Measurable (fun b : B =>
      thetaPlus rate rewards C_star C_h u t b j) := by
  have hmap : Measurable (fun registers : Fin p.K → ℕ × ℕ =>
      ProductSetLaw.theta p.m (fun i =>
        (1 + 1 / (D p : ℝ)) ^ (registers i).1) j) := measurable_of_countable _
  have hcomp := hmap.comp (measurable_postRegisters rate rewards C_star C_h u t)
  convert hcomp using 1
  funext b
  rfl

theorem measurable_VPlus :
    Measurable (fun b : B => VPlus rate rewards C_star C_h u t b) := by
  unfold VPlus
  apply Finset.measurable_fun_sum
  intro j hj
  exact (measurable_thetaPlus rate rewards C_star C_h u t j).mul
    ((measurable_backlogAfter rate rewards C_star C_h u t j).pow_const 2)

theorem measurable_energyDifference (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (fun b : B => VPlus rate rewards C_star C_h u t b -
      ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
        rate rewards C_star C_h u t control0 b) :=
  (measurable_VPlus rate rewards C_star C_h u t).sub
    (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_VMinus
      rate rewards C_star C_h u t control0)

private theorem integrable_of_norm_le_const {f : B → ℝ} (hf : Measurable f)
    (C : ℝ) (hbound : ∀ b, ‖f b‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : B => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with b
  simpa using hbound b

theorem integrable_VPlus (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (fun b : B => VPlus rate rewards C_star C_h u t b) mu := by
  apply integrable_of_norm_le_const rate rewards C_star C_h u t
    (measurable_VPlus rate rewards C_star C_h u t)
    ((p.m : ℝ) * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0) ^ 2)
  intro b
  have hb := VPlus_bounds rate rewards C_star C_h u t control0 b
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

theorem integrable_energyDifference :
    Integrable (fun b : B => VPlus rate rewards C_star C_h u t b -
      ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
        rate rewards C_star C_h u t control0 b) mu := by
  exact integrable_VPlus rate rewards C_star C_h u t control0 |>.sub
    (ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_VMinus
      rate rewards C_star C_h u t control0)

theorem ae_before_readouts_eq_retained :
    ∀ᵐ b : B ∂mu,
      (∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinusRetained
          rate rewards C_star C_h u t control0 j b) ∧
      (∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
          rate rewards C_star C_h u t control0 j b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinusRetained
          rate rewards C_star C_h u t control0 j b) ∧
      (∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinusRetained
          rate rewards C_star C_h u t control0 j b) ∧
      ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
        rate rewards C_star C_h u t control0 b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinusRetained
          rate rewards C_star C_h u t control0 b := by
  have hreadouts : ∀ᵐ b : B ∂mu, ∀ j : Fin p.K,
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinusRetained
          rate rewards C_star C_h u t control0 j b) ∧
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
          rate rewards C_star C_h u t control0 j b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinusRetained
          rate rewards C_star C_h u t control0 j b) ∧
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinusRetained
          rate rewards C_star C_h u t control0 j b := by
    rw [ae_all_iff]
    intro j
    filter_upwards [
      ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_bMinus_eq_retained
        rate rewards C_star C_h u t control0 j,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_wMinus_eq_retained
        rate rewards C_star C_h u t control0 j,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_thetaMinus_eq_retained
        rate rewards C_star C_h u t control0 j] with b hb hweight htheta
    exact ⟨hb, hweight, htheta⟩
  filter_upwards [hreadouts,
    ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_VMinus_eq_retained
      rate rewards C_star C_h u t control0] with b hreadouts henergy
  exact ⟨fun j => (hreadouts j).1, fun j => (hreadouts j).2.1,
    fun j => (hreadouts j).2.2, henergy⟩

theorem ae_before_weight_eq_v_on_G :
    ∀ᵐ b : B ∂mu,
      b ∈ G → ∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b j =
          ReferenceFirstCollectionRenewalComplementMoments.v
            rate rewards C_star C_h u t b j := by
  filter_upwards [ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_wMinus_eq_renewalAnchor
    rate rewards C_star C_h u t control0] with b hb
  intro hG j
  have hw := hb hG j
  change ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
      rate rewards C_star C_h u t control0 j b = _ at hw
  calc
    ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
        rate rewards C_star C_h u t b j =
      ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 j b := by
      rw [ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore_eq_scoreWeight]
      rfl
    _ = _ := hw

theorem ae_sum_thetaMinus_div_actualRenewalRate_le_R :
    ∀ᵐ b : B ∂mu,
      b ∈ G →
        (∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b /
          ReferenceFirstCollectionRenewalComplementMoments.xi
            rate rewards C_star C_h u t b j) ≤ CanonicalRecordingRates.R p :=
  ReferenceFirstCollectionRenewalIncomingQueueBounds.ae_sum_thetaMinus_div_actualRenewalRate_le_R
    rate rewards C_star C_h u t control0

private theorem exp_four_eta_bounds :
    Real.exp (4 * rate.eta.val) ≤ 1 + 8 * rate.eta.val := by
  have heta0 : 0 ≤ rate.eta.val := le_of_lt rate.eta.property
  have hx0 : 0 ≤ 4 * rate.eta.val := mul_nonneg (by norm_num) heta0
  have hsmall := CanonicalQueueProcess.four_mul_eta_le_one p
    rate.eta.property rate.sourceCap
  have hexp := RecordedPotentialStep.exp_le_one_add_add_sq
    hx0 hsmall
  have hsquare : (4 * rate.eta.val) ^ 2 ≤ 4 * rate.eta.val := by
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 4 * rate.eta.val)]
  nlinarith

private theorem score_weight_bounds_of_actual_identity
    (b : B) (d : ReferenceFirstCollectionRenewalAcceptedComplementMoments.ActualCall
      rate rewards C_star C_h u t b)
    (recording : CoordinatorRecordingOperation.Output p)
    (hrec : ∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalQueuePostReadout.queueRecord
        rate rewards C_star C_h u t b j =
        RecordedQueueRun.acceptedRecord qp
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t b.2)
          (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
            rate rewards C_star C_h u t b d recording) j)
    (hpost : ReferenceFirstCollectionRenewalQueuePostReadout.postReadout
      rate rewards C_star C_h u t b =
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.step qp
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t b.2)
          (ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
            rate rewards C_star C_h u t b d recording)))
    (j : Fin p.K) :
    ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
        rate rewards C_star C_h u t b j ≤
      ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        rate rewards C_star C_h u t b j ∧
    ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        rate rewards C_star C_h u t b j ≤
      Real.exp (4 * rate.eta.val) *
        ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b j := by
  let state := ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t b.2
  let cell := ReferenceFirstCollectionRenewalAcceptedComplementMoments.actualNumericalCell
    rate rewards C_star C_h u t b d recording
  have hregs : ReferenceFirstCollectionRenewalQueuePostReadout.postRegisters
      rate rewards C_star C_h u t b = (RecordedQueueRun.step qp state cell).registers :=
    congrArg Prod.fst hpost
  have hafter : ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
      rate rewards C_star C_h u t b j = RecordedQueueRun.scoreWeight qp
        (RecordedQueueRun.step qp state cell) j := by
    have hscore := congrArg (fun regs : Fin p.K → ℕ × ℕ => (regs j).1) hregs
    unfold ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
      RecordedQueueRun.scoreWeight ScoreWeights.scoreWeight
    rw [hscore, ReferenceFirstLaunchNumericalCell.queueParameters]
  have hbefore : ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
      rate rewards C_star C_h u t b j = RecordedQueueRun.scoreWeight qp state j :=
    ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore_eq_scoreWeight
      rate rewards C_star C_h u t b j
  have hservice :
      ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
          rate rewards C_star C_h u t b j =
        RecordedPotentialStep.servedEstimate qp state cell j := by
    unfold ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
      ReferenceFirstCollectionRenewalQueuePostReadout.integerService
      RecordedPotentialStep.servedEstimate
    dsimp [state, cell]
    rw [hrec j]
    rfl
  have hratio :
      ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b j /
        ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b j =
        Real.exp (RecordedPotentialStep.potentialLambda qp *
          ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
            rate rewards C_star C_h u t b j) := by
    rw [hafter, hbefore, hservice]
    exact RecordedPotentialStep.step_scoreWeight_ratio_exp qp state cell j
  have hbpos : 0 < ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
      rate rewards C_star C_h u t b j := by
    rw [hbefore]
    exact RecordedPotentialStep.scoreWeight_pos qp state j
  have hserviceBounds := ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService_bounds
    rate rewards C_star C_h u t b j
  have hlambdaPos := RecordedPotentialStep.potentialLambda_pos qp
  have hlambdaLe := RecordedPotentialStep.potentialLambda_le_eta qp
  have hlambdaLe' : RecordedPotentialStep.potentialLambda qp ≤ rate.eta.val := by
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hlambdaLe
  have hexpArg :
      RecordedPotentialStep.potentialLambda qp *
          ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
            rate rewards C_star C_h u t b j ≤ 4 * rate.eta.val := by
    calc
      _ ≤ RecordedPotentialStep.potentialLambda qp * 4 :=
        mul_le_mul_of_nonneg_left hserviceBounds.2 hlambdaPos.le
      _ = 4 * RecordedPotentialStep.potentialLambda qp := by ring
      _ ≤ 4 * rate.eta.val := by
        nlinarith [hlambdaLe']
  have hratioUpper := calc
      ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b j /
        ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b j =
          Real.exp (RecordedPotentialStep.potentialLambda qp *
            ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
              rate rewards C_star C_h u t b j) := hratio
      _ ≤ Real.exp (4 * rate.eta.val) := Real.exp_le_exp.mpr hexpArg
  have hexpLower : 1 ≤ Real.exp (RecordedPotentialStep.potentialLambda qp *
      ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
        rate rewards C_star C_h u t b j) := by
    have hlinear := Real.add_one_le_exp
      (RecordedPotentialStep.potentialLambda qp *
        ReferenceFirstCollectionRenewalQueuePostReadout.normalizedService
          rate rewards C_star C_h u t b j)
    linarith [mul_nonneg hlambdaPos.le hserviceBounds.1]
  have hratioLower : 1 ≤
      ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b j /
        ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b j := by
    rw [hratio]
    exact hexpLower
  constructor
  · nlinarith [((le_div_iff₀ hbpos).mp hratioLower)]
  · apply (div_le_iff₀ hbpos).mp hratioUpper

private theorem theta_weight_bounds_of_actual_identity
    (b : B)
    (hweight : ∀ i : Fin p.K,
      ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b i ≤
        ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b i ∧
      ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b i ≤
        Real.exp (4 * rate.eta.val) *
          ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
            rate rewards C_star C_h u t b i)
    (j : Fin p.K) :
    thetaPlus rate rewards C_star C_h u t b j ≤
        Real.exp (4 * rate.eta.val) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b ∧
      thetaPlus rate rewards C_star C_h u t b j ≤
        (1 + 8 * rate.eta.val) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b := by
  let v := fun i : Fin p.K =>
    ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
      rate rewards C_star C_h u t b i
  let w := fun i : Fin p.K =>
    ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
      rate rewards C_star C_h u t b i
  let c := w j / v j
  let mid := Function.update w j (v j)
  have hvpos : ∀ i, 0 < v i := by
    intro i
    dsimp [v]
    unfold ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
    positivity
  have hwpos : ∀ i, 0 < w i := by
    intro i
    dsimp [w]
    unfold ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
    positivity
  have hc1 : 1 ≤ c := by
    rw [le_div_iff₀ (hvpos j)]
    simpa [c, v, w] using (hweight j).1
  have hc2 : c ≤ Real.exp (4 * rate.eta.val) := by
    rw [div_le_iff₀ (hvpos j)]
    simpa [c, v, w] using (hweight j).2
  have hmidpos : ∀ i, 0 < mid i := by
    intro i
    by_cases hi : i = j
    · subst i
      simp [mid, hvpos]
    · simp [mid, hi, hwpos]
  have hmidown : v j = mid j := by simp [mid]
  have hmidother : ∀ i, i ≠ j → v i ≤ mid i := by
    intro i hij
    simpa [mid, hij] using (hweight i).1
  have hother := ProductMarginalStability.theta_antitone_of_other_coord_le
    v mid j p.two_le_m p.m_lt_K hvpos hmidpos hmidown hmidother
  have hownScale : c * v j = w j := by
    dsimp [c]
    field_simp [ne_of_gt (hvpos j)]
  have hupdate : Function.update mid j (c * v j) = w := by
    funext i
    by_cases hi : i = j
    · subst i
      simp [hownScale, mid]
    · simp [Function.update, hi, mid]
  have hscaledRaw := ProductMarginalStability.theta_update_le
    mid j c (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
    hmidpos hc1
  have hscaled :
      ProductSetLaw.theta p.m (Function.update mid j (c * v j)) j ≤
        c * ProductSetLaw.theta p.m mid j := by
    simpa only [hmidown] using hscaledRaw
  have htheta0 :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
      rate rewards C_star C_h u t control0 j b
  have htheta :
      ProductSetLaw.theta p.m w j ≤
        Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v j := by
    calc
      ProductSetLaw.theta p.m w j =
          ProductSetLaw.theta p.m (Function.update mid j (c * v j)) j := by
        rw [← hupdate]
      _ ≤ c * ProductSetLaw.theta p.m mid j := hscaled
      _ ≤ c * ProductSetLaw.theta p.m v j :=
        mul_le_mul_of_nonneg_left hother (by positivity [hc1])
      _ ≤ Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v j :=
        mul_le_mul_of_nonneg_right hc2 htheta0.1
  have htheta2 :
      ProductSetLaw.theta p.m w j ≤
        (1 + 8 * rate.eta.val) * ProductSetLaw.theta p.m v j := by
    exact htheta.trans (mul_le_mul_of_nonneg_right (exp_four_eta_bounds rate)
      htheta0.1)
  have hpostTheta : thetaPlus rate rewards C_star C_h u t b j =
      ProductSetLaw.theta p.m w j := rfl
  have hbeforeTheta :
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b =
      ProductSetLaw.theta p.m v j := by
    unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
    dsimp [v]
    rfl
  constructor
  · rw [hpostTheta, hbeforeTheta]
    exact htheta
  · rw [hpostTheta, hbeforeTheta]
    exact htheta2

/-- The source-capped actual update controls every post score weight and its
full `m`-element inclusion marginal on the same-witness event. -/
theorem ae_post_weight_and_marginal_bounds :
    ∀ᵐ b : B ∂mu, ∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
          rate rewards C_star C_h u t b j ≤
        ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b j ∧
      ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
          rate rewards C_star C_h u t b j ≤
        Real.exp (4 * rate.eta.val) *
          ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore
            rate rewards C_star C_h u t b j ∧
      thetaPlus rate rewards C_star C_h u t b j ≤
        Real.exp (4 * rate.eta.val) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b ∧
      thetaPlus rate rewards C_star C_h u t b j ≤
        (1 + 8 * rate.eta.val) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b := by
  filter_upwards [ReferenceFirstCollectionRenewalQueuePostReadout.ae_actual_postReadout_identity
    rate rewards C_star C_h u t control0] with b hidentity
  rcases hidentity with ⟨d, recording, _, _, _, _, _, _, _, _, _, hrec, hpost⟩
  have hscore (j : Fin p.K) :=
    score_weight_bounds_of_actual_identity rate rewards C_star C_h u t
      b d recording hrec hpost j
  intro j
  refine ⟨(hscore j).1, (hscore j).2, ?_⟩
  exact theta_weight_bounds_of_actual_identity rate rewards C_star C_h u t control0
    b (fun i => hscore i) j

/-- On the original pair law, the retained current-anchor event is exactly
the strict-past condition, and hence exactly absence of incoming overflow. -/
theorem ae_G_R_iff_noIncomingOverflow :
    ∀ᵐ b : B ∂mu,
      b ∈ G ↔ (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).overflow = false := by
  filter_upwards [
    ReferenceFirstCollectionRenewalAcceptedComplementMoments.ae_actual_strict_past_identification
      rate rewards C_star C_h u t control0,
    ReferenceFirstCollectionRenewalQueuePostReadout.ae_actual_postReadout_identity
      rate rewards C_star C_h u t control0] with b hG hidentity
  rcases hidentity with ⟨_, _, _, _, _, _, _, hstrict, _, _, _, _⟩
  exact (hG.trans hstrict.symm)

/-- Pointwise on an enabled incoming state, the first update obeys both queue
quadratic inequalities. -/
theorem backlog_energy_step_bounds (b : B) (j : Fin p.K)
    (hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = false) :
    ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ^ 2 -
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b ^ 2 ≤
        2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b *
            (acceptedA rate rewards C_star C_h u t j b - 4) +
          acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 ∧
    ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ^ 2 ≤
      2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
        rate rewards C_star C_h u t control0 *
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b +
          acceptedA rate rewards C_star C_h u t j b) := by
  let bplus := ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
    rate rewards C_star C_h u t b j
  let bminus := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
    rate rewards C_star C_h u t control0 j b
  let a := acceptedA rate rewards C_star C_h u t j b
  have hrec := ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_noOverflow
    rate rewards C_star C_h u t b j hf
  have hbefore : ReferenceFirstCollectionRenewalQueuePostReadout.backlogBefore
      rate rewards C_star C_h u t b j =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b := rfl
  rw [hbefore] at hrec
  have hrec' : bplus = max (bminus + a - 4) 0 := by
    simpa [bplus, bminus, a] using hrec
  have ha := acceptedA_bounds rate rewards C_star C_h u t b j
  have hb0 := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
    rate rewards C_star C_h u t control0 j b
  have hbplus := backlogAfter_bounds rate rewards C_star C_h u t control0 b j
  have hbefore :=
    ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_Bcap_of_noOverflow
      rate rewards C_star C_h u t control0 j b hf
  have hsum := arrival_le_Bcap rate rewards C_star C_h u t control0 b j
  have hmaxsq : (max (bminus + a - 4) 0) ^ 2 ≤ (bminus + a - 4) ^ 2 := by
    by_cases hy : 0 ≤ bminus + a - 4
    · simp [max_eq_left hy]
    · have hy' : bminus + a - 4 ≤ 0 := le_of_not_ge hy
      rw [max_eq_right hy']
      simpa using sq_nonneg (bminus + a - 4)
  have henergy : bplus ^ 2 - bminus ^ 2 ≤
      2 * bminus * (a - 4) + a ^ 2 + 16 := by
    rw [hrec']
    nlinarith [hmaxsq]
  have hpostle : bplus ≤ bminus + a := by
    rw [hrec']
    apply max_le
    · linarith
    · linarith [hb0, ha.1]
  have hquad : bplus ^ 2 ≤
      2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
        rate rewards C_star C_h u t control0 * (bminus + a) := by
    have hcap := mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (Bcap_nonneg rate rewards C_star C_h u t control0)
    have hmul := mul_le_mul_of_nonneg_left hpostle hcap
    nlinarith [mul_nonneg (sub_nonneg.mpr hbplus.2)
      (add_nonneg hcap hbplus.1)]
  exact ⟨henergy, by simpa [bplus, bminus, a] using hquad⟩

/-- When the incoming overflow flag is set, the queue update is disabled and
the post weighted energy is exactly the incoming one. -/
theorem VPlus_eq_VMinus_of_overflow (b : B) (hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t b.2).overflow = true) :
    VPlus rate rewards C_star C_h u t b =
      ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
        rate rewards C_star C_h u t control0 b := by
  unfold VPlus ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
  apply Finset.sum_congr rfl
  intro j hj
  have hback : ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
      rate rewards C_star C_h u t b j =
    ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
      rate rewards C_star C_h u t control0 j b := by
    rw [ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter_of_overflow
      rate rewards C_star C_h u t b j hf]
    rfl
  have hweightVec :
      (fun i : Fin p.K => ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter
        rate rewards C_star C_h u t b i) =
      (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.wMinus
        rate rewards C_star C_h u t control0 i b) := by
    funext i
    rw [ReferenceFirstCollectionRenewalQueuePostReadout.weightAfter_of_overflow
      rate rewards C_star C_h u t b i hf,
      ReferenceFirstCollectionRenewalQueuePostReadout.weightBefore_eq_scoreWeight]
    rfl
  have htheta : thetaPlus rate rewards C_star C_h u t b j =
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b := by
    unfold thetaPlus ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
    rw [hweightVec]
  rw [htheta, hback]

private theorem weighted_energy_step_of_bounds (b : B)
    (htheta : ∀ j : Fin p.K,
      thetaPlus rate rewards C_star C_h u t b j ≤
        (1 + 8 * rate.eta.val) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b)
    (hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
      rate rewards C_star C_h u t b.2).overflow = false) :
    VPlus rate rewards C_star C_h u t b -
      ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
        rate rewards C_star C_h u t control0 b ≤
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b *
              (acceptedA rate rewards C_star C_h u t j b - 4) +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
            8 * rate.eta.val *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2) := by
  have hterm (j : Fin p.K) :
      thetaPlus rate rewards C_star C_h u t b j *
          ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
            rate rewards C_star C_h u t b j ^ 2 -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
            ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b ^ 2 ≤
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b *
              (acceptedA rate rewards C_star C_h u t j b - 4) +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
            8 * rate.eta.val *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2) := by
    have htheta_j := htheta j
    have hb := backlog_energy_step_bounds rate rewards C_star C_h u t control0 b j hf
    have hmul := mul_le_mul_of_nonneg_right htheta_j
      (sq_nonneg (ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j))
    have htheta0 :=
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
        rate rewards C_star C_h u t control0 j b
    have hfirst :
        thetaPlus rate rewards C_star C_h u t b j *
            ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
              rate rewards C_star C_h u t b j ^ 2 -
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2 ≤
          8 * rate.eta.val *
            ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
            ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
              rate rewards C_star C_h u t b j ^ 2 := by
      nlinarith [hmul]
    have hsecond := mul_le_mul_of_nonneg_left hb.1 htheta0.1
    calc
      _ =
          (thetaPlus rate rewards C_star C_h u t b j *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2 -
            ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
                ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                  rate rewards C_star C_h u t b j ^ 2) +
          (ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
              (ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2 -
               ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                 rate rewards C_star C_h u t control0 j b ^ 2)) := by ring
      _ ≤ 8 * rate.eta.val *
            ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
            ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
              rate rewards C_star C_h u t b j ^ 2 +
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                  rate rewards C_star C_h u t control0 j b *
                  (acceptedA rate rewards C_star C_h u t j b - 4) +
                acceptedA rate rewards C_star C_h u t j b ^ 2 + 16) :=
          add_le_add hfirst hsecond
      _ = _ := by ring
  calc
    _ = ∑ j : Fin p.K,
        (thetaPlus rate rewards C_star C_h u t b j *
            ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
              rate rewards C_star C_h u t b j ^ 2 -
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
            rate rewards C_star C_h u t control0 j b *
              ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b ^ 2) := by
      unfold VPlus ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
      rw [Finset.sum_sub_distrib]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => hterm j)

private theorem reduced_term_bound (b : B) (j : Fin p.K) (hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow = false) :
    2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b *
        (acceptedA rate rewards C_star C_h u t j b - 4) +
      acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
      8 * rate.eta.val *
        ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
          rate rewards C_star C_h u t b j ^ 2 ≤
    (-15 / 2 : ℝ) *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b +
      (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b + 1 / 2) *
        acceptedA rate rewards C_star C_h u t j b +
      acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 := by
  have hb := backlog_energy_step_bounds rate rewards C_star C_h u t control0 b j hf
  have heta := rate.eta.property
  have hbc : 8 * rate.eta.val *
      (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
        rate rewards C_star C_h u t control0) = (1 / 2 : ℝ) := by
    unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
    field_simp [ne_of_gt heta]
    ring
  have hquad := mul_le_mul_of_nonneg_left hb.2
    (by positivity : 0 ≤ 8 * rate.eta.val)
  have hquad' :
      8 * rate.eta.val *
        ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
          rate rewards C_star C_h u t b j ^ 2 ≤
      (1 / 2 : ℝ) *
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b +
         acceptedA rate rewards C_star C_h u t j b) := by
    calc
      _ ≤ 8 * rate.eta.val *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
            rate rewards C_star C_h u t control0 *
            (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b +
             acceptedA rate rewards C_star C_h u t j b)) := hquad
      _ = _ := by rw [← mul_assoc, hbc]
  calc
    _ ≤ 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b *
          (acceptedA rate rewards C_star C_h u t j b - 4) +
        acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
        (1 / 2 : ℝ) *
          (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b +
           acceptedA rate rewards C_star C_h u t j b) := by
      nlinarith [hquad']
    _ = _ := by ring

/-- The detailed actual quadratic step, with the entire retained current-
anchor event masking its cost. Outside that event the update is disabled. -/
theorem ae_weighted_energy_step_detailed :
    ∀ᵐ b : B ∂mu,
      VPlus rate rewards C_star C_h u t b -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
          rate rewards C_star C_h u t control0 b ≤
        Set.indicator G (fun b =>
          ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
              (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                  rate rewards C_star C_h u t control0 j b *
                  (acceptedA rate rewards C_star C_h u t j b - 4) +
                acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
                8 * rate.eta.val *
                  ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                    rate rewards C_star C_h u t b j ^ 2)) b := by
  filter_upwards [ae_G_R_iff_noIncomingOverflow rate rewards C_star C_h u t control0,
    ae_post_weight_and_marginal_bounds rate rewards C_star C_h u t control0]
    with b hG hweights
  by_cases hg : b ∈ G
  · have hf := hG.mp hg
    have henergy := weighted_energy_step_of_bounds rate rewards C_star C_h u t
      control0 b (fun j => (hweights j).2.2.2) hf
    simpa [Set.indicator, hg] using henergy
  · have hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow = true := by
      have hnot : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow ≠ false := by
        intro hfalse
        exact hg (hG.mpr hfalse)
      cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow <;> simp_all
    have hzero := VPlus_eq_VMinus_of_overflow rate rewards C_star C_h u t control0 b hf
    simp [Set.indicator, hg, hzero]

/-- The usual renewal drift form, retaining exact rational constants and
masking the complete energy cost by the same `G_R` event. -/
theorem ae_weighted_energy_step :
    ∀ᵐ b : B ∂mu,
      VPlus rate rewards C_star C_h u t b -
        ReferenceFirstCollectionRenewalIncomingQueueBounds.VMinus
          rate rewards C_star C_h u t control0 b ≤
        Set.indicator G (fun b =>
          ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
              rate rewards C_star C_h u t control0 j b *
              ((-15 / 2 : ℝ) *
                  ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                    rate rewards C_star C_h u t control0 j b +
                (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                    rate rewards C_star C_h u t control0 j b + 1 / 2) *
                  acceptedA rate rewards C_star C_h u t j b +
                acceptedA rate rewards C_star C_h u t j b ^ 2 + 16)) b := by
  filter_upwards [ae_G_R_iff_noIncomingOverflow rate rewards C_star C_h u t control0,
    ae_post_weight_and_marginal_bounds rate rewards C_star C_h u t control0]
    with b hG hweights
  by_cases hg : b ∈ G
  · have hf := hG.mp hg
    have henergy := weighted_energy_step_of_bounds rate rewards C_star C_h u t
      control0 b (fun j => (hweights j).2.2.2) hf
    have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin p.K)))
      (fun j hj => mul_le_mul_of_nonneg_left
        (reduced_term_bound rate rewards C_star C_h u t control0 b j hf)
        (ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
          rate rewards C_star C_h u t control0 j b).1)
    have htotal := henergy.trans hsum
    simpa [Set.indicator, hg] using htotal
  · have hf : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow = true := by
      have hnot : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow ≠ false := by
        intro hfalse
        exact hg (hG.mpr hfalse)
      cases h : (ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow <;> simp_all
    have hzero := VPlus_eq_VMinus_of_overflow rate rewards C_star C_h u t control0 b hf
    simp [Set.indicator, hg, hzero]

private theorem measurable_bMinus_times (j : Fin p.K) :
    Measurable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b) :=
  (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinus
    rate rewards C_star C_h u t control0 j).mul
    (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinus
      rate rewards C_star C_h u t control0 j)

theorem integrable_thetaMinus_mul_bMinus (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_norm_le_const rate rewards C_star C_h u t
    (measurable_bMinus_times rate rewards C_star C_h u t control0 j)
    (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0)
  intro b
  have ht := ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
    rate rewards C_star C_h u t control0 j b
  have hb := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_two_Bcap
    rate rewards C_star C_h u t control0 j b
  have hb0 := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
    rate rewards C_star C_h u t control0 j b
  rw [Real.norm_of_nonneg (mul_nonneg ht.1 hb0)]
  calc
    _ ≤ 1 * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0) :=
      mul_le_mul ht.2 hb hb0 (by norm_num)
    _ = _ := by ring

theorem integrable_thetaMinus_mul_bMinus_mul_acceptedA (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b *
      acceptedA rate rewards C_star C_h u t j b) mu := by
  have hmeas := (measurable_bMinus_times rate rewards C_star C_h u t control0 j).mul
    (measurable_acceptedA rate rewards C_star C_h u t j)
  apply integrable_of_norm_le_const rate rewards C_star C_h u t hmeas
    (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0 /
      CanonicalRecordingRates.beta p rate.eta.val)
  intro b
  have hbase := ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_le_two_Bcap
    rate rewards C_star C_h u t control0 j b
  have hpair := ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
    rate rewards C_star C_h u t control0 j b
  have ha := acceptedA_bounds rate rewards C_star C_h u t b j
  have hbound :
      0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b :=
    mul_nonneg hpair.1
      (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
        rate rewards C_star C_h u t control0 j b)
  have hproduct :
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b ≤
        2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 := by
    calc
      _ ≤ 1 * (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0) :=
        mul_le_mul hpair.2 hbase
          (ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus_nonneg
            rate rewards C_star C_h u t control0 j b) (by norm_num)
      _ = _ := by ring
  change ‖ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
      rate rewards C_star C_h u t control0 j b *
      ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b *
      acceptedA rate rewards C_star C_h u t j b‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg hbound ha.1)]
  calc
    _ ≤ (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0) *
        (1 / CanonicalRecordingRates.beta p rate.eta.val) := by
      exact mul_le_mul hproduct ha.2 ha.1
        (mul_nonneg (by norm_num) (Bcap_nonneg rate rewards C_star C_h u t control0))
    _ = 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0 /
        CanonicalRecordingRates.beta p rate.eta.val := by ring

theorem integrable_thetaMinus_mul_acceptedA (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      acceptedA rate rewards C_star C_h u t j b) mu := by
  have hmeas := (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinus
      rate rewards C_star C_h u t control0 j).mul
    (measurable_acceptedA rate rewards C_star C_h u t j)
  apply integrable_of_norm_le_const rate rewards C_star C_h u t hmeas
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
  intro b
  have ht := ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
    rate rewards C_star C_h u t control0 j b
  have ha := acceptedA_bounds rate rewards C_star C_h u t b j
  change ‖ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
      rate rewards C_star C_h u t control0 j b *
      acceptedA rate rewards C_star C_h u t j b‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg ht.1 ha.1)]
  calc
    _ ≤ 1 * (1 / CanonicalRecordingRates.beta p rate.eta.val) :=
      mul_le_mul ht.2 ha.2 ha.1 (by norm_num)
    _ = _ := by ring

theorem integrable_thetaMinus_mul_acceptedA_sq (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      acceptedA rate rewards C_star C_h u t j b ^ 2) mu := by
  have hmeas := (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinus
      rate rewards C_star C_h u t control0 j).mul
    ((measurable_acceptedA rate rewards C_star C_h u t j).pow_const 2)
  apply integrable_of_norm_le_const rate rewards C_star C_h u t hmeas
    (1 / CanonicalRecordingRates.beta p rate.eta.val ^ 2)
  intro b
  have ht := ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
    rate rewards C_star C_h u t control0 j b
  have ha := acceptedA_bounds rate rewards C_star C_h u t b j
  change ‖ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
      rate rewards C_star C_h u t control0 j b *
      acceptedA rate rewards C_star C_h u t j b ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg ht.1 (sq_nonneg _))]
  have hsq :
      acceptedA rate rewards C_star C_h u t j b ^ 2 ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 :=
    (sq_le_sq₀ ha.1 (by positivity [beta_pos rate])).2 ha.2
  calc
    _ ≤ 1 * (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 :=
      mul_le_mul ht.2 hsq (sq_nonneg _) (by positivity [beta_pos rate])
    _ = _ := by ring

theorem integrable_thetaMinus_mul_backlogAfter_sq (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ^ 2) mu := by
  have hmeas := (ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinus
      rate rewards C_star C_h u t control0 j).mul
    ((measurable_backlogAfter rate rewards C_star C_h u t j).pow_const 2)
  apply integrable_of_norm_le_const rate rewards C_star C_h u t hmeas
    ((2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
      rate rewards C_star C_h u t control0) ^ 2)
  intro b
  have ht := ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus_bounds
    rate rewards C_star C_h u t control0 j b
  have hb := backlogAfter_bounds rate rewards C_star C_h u t control0 b j
  change ‖ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
      rate rewards C_star C_h u t control0 j b *
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ^ 2‖ ≤ _
  rw [Real.norm_of_nonneg (mul_nonneg ht.1 (sq_nonneg _))]
  have hsq :
      ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
        rate rewards C_star C_h u t b j ^ 2 ≤
        (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0) ^ 2 := by
    have hcap : 0 ≤ 2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
        rate rewards C_star C_h u t control0 :=
      mul_nonneg (by norm_num) (Bcap_nonneg rate rewards C_star C_h u t control0)
    nlinarith [mul_nonneg (sub_nonneg.mpr hb.2) (add_nonneg hcap hb.1)]
  calc
    _ ≤ 1 *
        (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.Bcap
          rate rewards C_star C_h u t control0) ^ 2 :=
      mul_le_mul ht.2 hsq (sq_nonneg _) (by norm_num)
    _ = _ := by ring

private theorem measurable_weightedDetailedRhs :
    Measurable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b *
              (acceptedA rate rewards C_star C_h u t j b - 4) +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
            8 * rate.eta.val *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2)) := by
  apply Finset.measurable_fun_sum
  intro j hj
  have hm := ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinus
    rate rewards C_star C_h u t control0 j
  have hb := ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinus
    rate rewards C_star C_h u t control0 j
  have ha := measurable_acceptedA rate rewards C_star C_h u t j
  have hp := measurable_backlogAfter rate rewards C_star C_h u t j
  have hfirst : Measurable (fun b : B =>
      2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b *
        (acceptedA rate rewards C_star C_h u t j b - 4)) :=
    (measurable_const.mul hb).mul (ha.sub_const 4)
  have hquad : Measurable (fun b : B =>
      8 * rate.eta.val *
        ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
          rate rewards C_star C_h u t b j ^ 2) :=
    measurable_const.mul (hp.pow_const 2)
  have hinside := (((hfirst.add (ha.pow_const 2)).add_const 16).add hquad)
  exact hm.mul hinside

private theorem measurable_weightedReducedRhs :
    Measurable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          ((-15 / 2 : ℝ) *
              ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b +
            (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b + 1 / 2) *
              acceptedA rate rewards C_star C_h u t j b +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16)) := by
  apply Finset.measurable_fun_sum
  intro j hj
  have hm := ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_thetaMinus
    rate rewards C_star C_h u t control0 j
  have hb := ReferenceFirstCollectionRenewalIncomingQueueBounds.measurable_bMinus
    rate rewards C_star C_h u t control0 j
  have ha := measurable_acceptedA rate rewards C_star C_h u t j
  have hlinear : Measurable (fun b : B =>
      (-15 / 2 : ℝ) *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b) :=
    measurable_const.mul hb
  have hfactor' : Measurable (fun b : B =>
      2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
        rate rewards C_star C_h u t control0 j b + (1 / 2 : ℝ)) :=
    (measurable_const.mul hb).add_const (1 / 2 : ℝ)
  have hquad := ha.pow_const 2
  exact hm.mul (((hlinear.add (hfactor'.mul ha)).add hquad).add_const 16)

private theorem integrable_weightedDetailedTerm (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
          rate rewards C_star C_h u t control0 j b *
          (acceptedA rate rewards C_star C_h u t j b - 4) +
        acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
        8 * rate.eta.val *
          ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
            rate rewards C_star C_h u t b j ^ 2)) mu := by
  have htheta := ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_thetaMinus
    rate rewards C_star C_h u t control0 j
  have htb := integrable_thetaMinus_mul_bMinus rate rewards C_star C_h u t control0 j
  have htba := integrable_thetaMinus_mul_bMinus_mul_acceptedA
    rate rewards C_star C_h u t control0 j
  have hta2 := integrable_thetaMinus_mul_acceptedA_sq
    rate rewards C_star C_h u t control0 j
  have htbp2 := integrable_thetaMinus_mul_backlogAfter_sq
    rate rewards C_star C_h u t control0 j
  have hsum1 := (htba.const_mul (2 : ℝ)).add (htb.const_mul (-8 : ℝ))
  have hsum2 := hsum1.add hta2
  have hsum3 := hsum2.add (htheta.const_mul (16 : ℝ))
  have hsum := hsum3.add (htbp2.const_mul (8 * rate.eta.val))
  refine hsum.congr ?_
  filter_upwards [] with b
  dsimp
  ring

private theorem integrable_weightedReducedTerm (j : Fin p.K) :
    Integrable (fun b : B =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
        rate rewards C_star C_h u t control0 j b *
      ((-15 / 2 : ℝ) *
          ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b +
        (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
            rate rewards C_star C_h u t control0 j b + 1 / 2) *
          acceptedA rate rewards C_star C_h u t j b +
        acceptedA rate rewards C_star C_h u t j b ^ 2 + 16)) mu := by
  have htheta := ReferenceFirstCollectionRenewalIncomingQueueBounds.integrable_thetaMinus
    rate rewards C_star C_h u t control0 j
  have htb := integrable_thetaMinus_mul_bMinus rate rewards C_star C_h u t control0 j
  have htba := integrable_thetaMinus_mul_bMinus_mul_acceptedA
    rate rewards C_star C_h u t control0 j
  have hta := integrable_thetaMinus_mul_acceptedA rate rewards C_star C_h u t control0 j
  have hta2 := integrable_thetaMinus_mul_acceptedA_sq
    rate rewards C_star C_h u t control0 j
  have hsum1 := (htb.const_mul (-15 / 2 : ℝ)).add (htba.const_mul (2 : ℝ))
  have hsum2 := hsum1.add (hta.const_mul (1 / 2 : ℝ))
  have hsum3 := hsum2.add hta2
  have hsum := hsum3.add (htheta.const_mul (16 : ℝ))
  refine hsum.congr ?_
  filter_upwards [] with b
  dsimp
  ring

private theorem integrable_weightedDetailedSum :
    Integrable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b *
              (acceptedA rate rewards C_star C_h u t j b - 4) +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
            8 * rate.eta.val *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2)) mu := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (Finset.univ : Finset (Fin p.K))
      (fun j hj => integrable_weightedDetailedTerm rate rewards C_star C_h u t control0 j))

private theorem integrable_weightedReducedSum :
    Integrable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          ((-15 / 2 : ℝ) *
              ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b +
            (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b + 1 / 2) *
              acceptedA rate rewards C_star C_h u t j b +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16)) mu := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum (Finset.univ : Finset (Fin p.K))
      (fun j hj => integrable_weightedReducedTerm rate rewards C_star C_h u t control0 j))

/-- Both finite weighted expressions used by the conditional drift consumer
are integrable on the same finite, unnormalized pair law. -/
theorem integrable_weighted_energy_step_sums :
    Integrable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
              rate rewards C_star C_h u t control0 j b *
              (acceptedA rate rewards C_star C_h u t j b - 4) +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16 +
            8 * rate.eta.val *
              ReferenceFirstCollectionRenewalQueuePostReadout.backlogAfter
                rate rewards C_star C_h u t b j ^ 2)) mu ∧
    Integrable (fun b : B =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaMinus
          rate rewards C_star C_h u t control0 j b *
          ((-15 / 2 : ℝ) *
              ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b +
            (2 * ReferenceFirstCollectionRenewalIncomingQueueBounds.bMinus
                rate rewards C_star C_h u t control0 j b + 1 / 2) *
              acceptedA rate rewards C_star C_h u t j b +
            acceptedA rate rewards C_star C_h u t j b ^ 2 + 16)) mu := by
  exact ⟨integrable_weightedDetailedSum rate rewards C_star C_h u t control0,
    integrable_weightedReducedSum rate rewards C_star C_h u t control0⟩

end Bandits.Support.ReferenceFirstCollectionRenewalQueueEnergy

end
