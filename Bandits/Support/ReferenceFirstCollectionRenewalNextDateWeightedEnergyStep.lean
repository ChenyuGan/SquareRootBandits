/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep
public import Bandits.Support.ReferenceFirstCollectionRenewalConditionalWeightedDrift

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Actual first next-date weighted queue energy

This module follows the same unnormalized first-renewal source through its
actual optional date `t + 1`. The post energy observes the existing optional
physical cell; absence retains the incoming registers and creates no queue
input. The strict future-date drift is a separate statement.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)

abbrev Source :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.Source
    rate rewards C_star C_h u t

local notation "Z" => Source rate rewards C_star C_h u t
local notation "ν" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "Fq" =>
  ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
local notation "beta" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Bcap" => 1 / (32 * rate.eta.val)

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalLawFinite : IsFiniteMeasure ν :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite
    rate rewards C_star C_h u t

def currentRegisters (z : Z) : Fin p.K → ℕ × ℕ :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
    rate rewards C_star C_h u t z).registers

def nextRegisters (hq : t.val + 1 < p.T) (z : Z) : Fin p.K → ℕ × ℕ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none => currentRegisters rate rewards C_star C_h u t z
  | some c =>
      (RecordedQueueRun.step
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) c).registers

def weightFromRegisters (A : Fin p.K → ℕ × ℕ) (j : Fin p.K) : ℝ :=
  (1 + 1 / (D p : ℝ)) ^ (A j).1

def thetaFromRegisters (A : Fin p.K → ℕ × ℕ) (j : Fin p.K) : ℝ :=
  ProductSetLaw.theta p.m (weightFromRegisters A) j

def backlogFromRegisters (A : Fin p.K → ℕ × ℕ) (j : Fin p.K) : ℝ :=
  ((A j).2 : ℝ) /
    ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)

def energyFromRegisters (A : Fin p.K → ℕ × ℕ) : ℝ :=
  ∑ j : Fin p.K, thetaFromRegisters A j *
    (backlogFromRegisters rate A j) ^ 2

def backlogSumFromRegisters (A : Fin p.K → ℕ × ℕ) : ℝ :=
  ∑ j : Fin p.K, thetaFromRegisters A j * backlogFromRegisters rate A j

def preWeight (z : Z) (j : Fin p.K) : ℝ :=
  weightFromRegisters (currentRegisters rate rewards C_star C_h u t z) j

def preTheta (z : Z) (j : Fin p.K) : ℝ :=
  thetaFromRegisters (currentRegisters rate rewards C_star C_h u t z) j

def preBacklog (z : Z) (j : Fin p.K) : ℝ :=
  backlogFromRegisters rate (currentRegisters rate rewards C_star C_h u t z) j

def postTheta (hq : t.val + 1 < p.T) (z : Z) (j : Fin p.K) : ℝ :=
  thetaFromRegisters (nextRegisters rate rewards C_star C_h u t hq z) j

def postBacklog (hq : t.val + 1 < p.T) (z : Z) (j : Fin p.K) : ℝ :=
  backlogFromRegisters rate (nextRegisters rate rewards C_star C_h u t hq z) j

def Vminus (z : Z) : ℝ :=
  energyFromRegisters rate (currentRegisters rate rewards C_star C_h u t z)

def Vplus (hq : t.val + 1 < p.T) (z : Z) : ℝ :=
  energyFromRegisters rate (nextRegisters rate rewards C_star C_h u t hq z)

def Bminus (z : Z) : ℝ :=
  backlogSumFromRegisters rate (currentRegisters rate rewards C_star C_h u t z)

def retainedNextDate (hq : t.val + 1 < p.T) : Set Z :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
    rate rewards C_star C_h u t hq

def G (hq : t.val + 1 < p.T) (z : Z) : Prop :=
  z ∈ retainedNextDate rate rewards C_star C_h u t hq

def priorCost (hq : t.val + 1 < p.T) (z : Z) : ℝ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | some (true, xi) =>
      ∑ j : Fin p.K,
        thetaFromRegisters (p := p) (currentRegisters rate rewards C_star C_h u t z) j /
          xi j
  | _ => 0

private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

private theorem integrable_of_measurable_norm_le_const {f : Z → ℝ}
    (hf : Measurable f) (C : ℝ) (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f ν := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  exact hbound z

private theorem measurable_thetaVector_from_registers :
    Measurable (fun A : Fin p.K → ℕ × ℕ =>
      fun j : Fin p.K => thetaFromRegisters (p := p) A j) := by
  exact measurable_of_countable _

private theorem measurable_weightVector_from_registers :
    Measurable (fun A : Fin p.K → ℕ × ℕ =>
      fun j : Fin p.K => weightFromRegisters (p := p) A j) := by
  exact measurable_of_countable _

private theorem weightFromRegisters_pos (A : Fin p.K → ℕ × ℕ) (j : Fin p.K) :
    0 < weightFromRegisters (p := p) A j := by
  unfold weightFromRegisters
  exact pow_pos (by positivity) _

theorem thetaFromRegisters_nonneg (A : Fin p.K → ℕ × ℕ) (j : Fin p.K) :
    0 ≤ thetaFromRegisters (p := p) A j :=
  (ProductSetLaw.theta_pos (weightFromRegisters (p := p) A) j
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
    (weightFromRegisters_pos (p := p) A)).le

theorem thetaFromRegisters_le_one (A : Fin p.K → ℕ × ℕ) (j : Fin p.K) :
    thetaFromRegisters (p := p) A j ≤ 1 :=
  (ProductSetLaw.theta_lt_one (weightFromRegisters (p := p) A) j
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
    (weightFromRegisters_pos (p := p) A)).le

theorem sum_thetaFromRegisters (A : Fin p.K → ℕ × ℕ) :
    (∑ j : Fin p.K, thetaFromRegisters (p := p) A j) = (p.m : ℝ) :=
  ProductSetLaw.sum_theta_eq_card (weightFromRegisters (p := p) A)
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
    (weightFromRegisters_pos (p := p) A)

theorem energyFromRegisters_nonneg (A : Fin p.K → ℕ × ℕ) :
    0 ≤ energyFromRegisters rate A := by
  unfold energyFromRegisters
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (thetaFromRegisters_nonneg (p := p) A j)
    (sq_nonneg (backlogFromRegisters rate A j))

theorem energyFromRegisters_le_of_backlog_bound
    (A : Fin p.K → ℕ × ℕ) (C : ℝ)
    (hback : ∀ j : Fin p.K,
      0 ≤ backlogFromRegisters rate A j ∧ backlogFromRegisters rate A j ≤ C) :
    energyFromRegisters rate A ≤ (p.m : ℝ) * C ^ 2 := by
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin p.K)))
    (fun j hj => by
      have hC : 0 ≤ C := le_trans (hback j).1 (hback j).2
      have hsq : backlogFromRegisters rate A j ^ 2 ≤ C ^ 2 :=
        (sq_le_sq₀ (hback j).1 hC).2 (hback j).2
      exact mul_le_mul_of_nonneg_left hsq
        (thetaFromRegisters_nonneg (p := p) A j))
  unfold energyFromRegisters at hsum ⊢
  calc
    (∑ j : Fin p.K, thetaFromRegisters (p := p) A j *
        backlogFromRegisters rate A j ^ 2) ≤
      ∑ j : Fin p.K, thetaFromRegisters (p := p) A j * C ^ 2 := hsum
    _ = (∑ j : Fin p.K, thetaFromRegisters (p := p) A j) * C ^ 2 := by
      rw [Finset.sum_mul]
    _ = (p.m : ℝ) * C ^ 2 := by rw [sum_thetaFromRegisters]

theorem energyFromRegisters_bounded_nonneg
    (A : Fin p.K → ℕ × ℕ) (C : ℝ) (_hC : 0 ≤ C)
    (hback : ∀ j : Fin p.K,
      0 ≤ backlogFromRegisters rate A j ∧ backlogFromRegisters rate A j ≤ C) :
    0 ≤ energyFromRegisters rate A ∧
      energyFromRegisters rate A ≤ (p.m : ℝ) * C ^ 2 :=
  ⟨energyFromRegisters_nonneg rate A,
    energyFromRegisters_le_of_backlog_bound rate A C hback⟩

theorem nextRegisters_backlog_eq (hq : t.val + 1 < p.T) (z : Z)
    (j : Fin p.K) :
    postBacklog rate rewards C_star C_h u t hq z j =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogAfter
        rate rewards C_star C_h u t hq j z := by
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none =>
      simp [postBacklog, nextRegisters,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogAfter,
        backlogFromRegisters, currentRegisters, hc,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore]
  | some c =>
      simp [postBacklog, nextRegisters,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogAfter,
        backlogFromRegisters, hc]

theorem Vminus_eq_sum (z : Z) :
    Vminus rate rewards C_star C_h u t z =
      ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j *
        preBacklog rate rewards C_star C_h u t z j ^ 2 := by
  rfl

theorem Vplus_eq_sum (hq : t.val + 1 < p.T) (z : Z) :
    Vplus rate rewards C_star C_h u t hq z =
      ∑ j : Fin p.K, postTheta rate rewards C_star C_h u t hq z j *
        postBacklog rate rewards C_star C_h u t hq z j ^ 2 := by
  rfl

theorem measurable_currentRegisters :
    Measurable[Fq] (currentRegisters rate rewards C_star C_h u t) := by
  have hread :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.measurable_incomingReadout
      rate rewards C_star C_h u t control0
  have hreg : Measurable[Fq] (fun z : Z =>
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z).1) := measurable_fst.comp hread
  have heq : currentRegisters rate rewards C_star C_h u t =
      (fun z : Z =>
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z).1) := by
    funext z
    dsimp [currentRegisters]
    rw [← _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.incomingReadout_eq_currentState
      rate rewards C_star C_h u t z]
    rfl
  rw [heq]
  exact hreg

theorem measurable_preWeight (j : Fin p.K) :
    Measurable[Fq] (preWeight rate rewards C_star C_h u t · j) := by
  have hvec := (measurable_weightVector_from_registers (p := p)).comp
    (measurable_currentRegisters rate rewards C_star C_h u t control0)
  have hcoord := (measurable_pi_apply j).comp hvec
  convert hcoord using 1
  funext z
  rfl

theorem measurable_preTheta (j : Fin p.K) :
    Measurable[Fq] (preTheta rate rewards C_star C_h u t · j) := by
  have hvec := (measurable_thetaVector_from_registers (p := p)).comp
    (measurable_currentRegisters rate rewards C_star C_h u t control0)
  have hcoord := (measurable_pi_apply j).comp hvec
  convert hcoord using 1
  funext z
  rfl

theorem measurable_preBacklog (j : Fin p.K) :
    Measurable[Fq] (preBacklog rate rewards C_star C_h u t · j) := by
  change Measurable[Fq] (fun z : Z =>
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
      rate rewards C_star C_h u t j z)
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.measurable_backlogBefore
    rate rewards C_star C_h u t control0 j

theorem measurableSet_G (hq : t.val + 1 < p.T) : MeasurableSet[Fq]
    {z : Z | G rate rewards C_star C_h u t hq z} := by
  simpa [G, retainedNextDate] using
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.measurableSet_retainedNextDate
      rate rewards C_star C_h u t control0 hq)

private theorem currentOverflow_eq_prior (z : Z) :
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
      rate rewards C_star C_h u t z).overflow =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
        rate rewards C_star C_h u t z := by
  change (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
      rate rewards C_star C_h u t z).overflow =
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t z).2.1
  have hread :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
      rate rewards C_star C_h u t z
  exact congrArg Prod.fst (congrArg Prod.snd hread)

private def naturalizedNextScalar (hq : t.val + 1 < p.T)
    (z : Z) (j : Fin p.K) : ℕ :=
  Nat.floor (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextArrival
    rate rewards C_star C_h u t hq j z *
      ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))

private theorem nextRegisters_eq_queueTransition_of_G
    (hq : t.val + 1 < p.T) (z : Z) (hg : G rate rewards C_star C_h u t hq z)
    (j : Fin p.K) :
    nextRegisters rate rewards C_star C_h u t hq z j =
      QueueReplay.transition
        (4 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
        (currentRegisters rate rewards C_star C_h u t z j)
        (true, naturalizedNextScalar rate rewards C_star C_h u t hq z j) := by
  have hret :=
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
      rate rewards C_star C_h u t hq z).mp hg
  obtain ⟨⟨xi, hparams⟩, hclear⟩ := hret
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none =>
      simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
        hc] at hparams
  | some c =>
      have hpresent :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
          rate rewards C_star C_h u t hq z c hc
      have hpair : (c.enabled, c.rate) = (true, xi) :=
        Option.some.inj (hpresent.symm.trans hparams)
      have hEnabled : c.enabled = true := congrArg Prod.fst hpair
      have hstate :
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z).overflow = false := by
        rw [currentOverflow_eq_prior rate rewards C_star C_h u t z]
        exact hclear
      have hclear' :
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
            rate rewards C_star C_h u t z).2.1 = false := by
        simpa [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow]
          using hclear
      have hrun :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.actual_nextScalar_present_run
          rate rewards C_star C_h u t hq j z c hc
      rcases hrun with ⟨hscalar, haccepted, _, _⟩
      have haccepted' :
          RecordedQueueRun.acceptedRecord
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
                rate rewards C_star C_h u t z) c j =
            (true, RecordedQueueRun.quantizedArrival
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              c j) := by
        rw [hclear', hEnabled] at haccepted
        simpa using haccepted
      have hraw :
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextArrival
              rate rewards C_star C_h u t hq j z =
            (RecordedQueueRun.quantizedArrival
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              c j : ℝ) /
              ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) := by
        change _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar
          rate rewards C_star C_h u t hq j z = _
        rw [hscalar]
        simp [RecordedRoundMoments.rawEstimate, RecordedQueueRun.acceptedArrival,
          haccepted']
      have hnpos :
          (0 : ℝ) <
            ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) :=
        Nat.cast_pos.mpr
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos
      have hfloor : naturalizedNextScalar rate rewards C_star C_h u t hq z j =
          RecordedQueueRun.quantizedArrival
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            c j := by
        unfold naturalizedNextScalar
        rw [hraw, div_mul_cancel₀ _ hnpos.ne']
        exact Nat.floor_natCast _
      have hstep :
          (RecordedQueueRun.step
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c).registers j =
            QueueReplay.transition
              (4 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
              ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
                rate rewards C_star C_h u t z).registers j)
              (true, RecordedQueueRun.quantizedArrival
                (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
                c j) := by
        change QueueReplay.transition
            (4 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
            ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z).registers j)
            (RecordedQueueRun.acceptedRecord
              (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
                rate rewards C_star C_h u t z) c j) = _
        rw [haccepted']
      simp [nextRegisters, currentRegisters, hc, hstep, hfloor]

private theorem nextRegisters_eq_current_of_not_G
    (hq : t.val + 1 < p.T) (z : Z) (hnot : ¬ G rate rewards C_star C_h u t hq z)
    (j : Fin p.K) :
    nextRegisters rate rewards C_star C_h u t hq z j = currentRegisters rate rewards C_star C_h u t z j := by
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none => simp [nextRegisters, currentRegisters, hc]
  | some c =>
      have hparams :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
          rate rewards C_star C_h u t hq z c hc
      by_cases hclear :
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
            rate rewards C_star C_h u t z = false
      · have hdisabled : c.enabled = false := by
          cases hcEnabled : c.enabled with
          | false => rfl
          | true =>
              have hmem : G rate rewards C_star C_h u t hq z := by
                change z ∈ retainedNextDate rate rewards C_star C_h u t hq
                apply (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
                  rate rewards C_star C_h u t hq z).mpr
                exact ⟨⟨c.rate, by simp [hparams, hcEnabled]⟩, hclear⟩
              exact (hnot hmem).elim
        have hpres := RecordedQueueRun.step_disabled_preserves
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c hdisabled j
        simpa [nextRegisters, currentRegisters, hc] using hpres.1
      · have hoverflow :
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z).overflow = true := by
          rw [currentOverflow_eq_prior rate rewards C_star C_h u t z]
          cases h : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
              rate rewards C_star C_h u t z <;> simp_all
        have hpres := RecordedQueueRun.step_after_overflow_preserves
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c hoverflow j
        simpa [nextRegisters, currentRegisters, hc] using hpres.1

private theorem measurable_naturalizedNextScalar (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (j : Fin p.K) : Measurable (naturalizedNextScalar rate rewards C_star C_h u t hq · j) := by
  unfold naturalizedNextScalar
  exact Nat.measurable_floor.comp
    ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.measurable_nextArrival
      rate rewards C_star C_h u t control0 hq j).mul_const
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))

private theorem measurable_currentRegisters_ambient :
    Measurable (currentRegisters rate rewards C_star C_h u t) := by
  have hreg : Measurable (fun z : Z =>
      fun j : Fin p.K =>
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z).1 j) := by
    apply measurable_pi_iff.mpr
    intro j
    exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.measurable_wholePostReadout_register
      rate rewards C_star C_h u t j
  have heq : currentRegisters rate rewards C_star C_h u t = fun z : Z =>
      fun j : Fin p.K =>
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z).1 j := by
    funext z
    funext j
    change ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
      rate rewards C_star C_h u t z).registers j) = _
    have hread :=
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
        rate rewards C_star C_h u t z
    exact congrArg (fun r : Fin p.K → ℕ × ℕ => r j) (congrArg Prod.fst hread)
  rw [heq]
  exact hreg

private theorem nextRegisters_eq_ite (hq : t.val + 1 < p.T) (z : Z) :
    nextRegisters rate rewards C_star C_h u t hq z =
      if G rate rewards C_star C_h u t hq z then
        fun j => QueueReplay.transition
          (4 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
          (currentRegisters rate rewards C_star C_h u t z j)
          (true, naturalizedNextScalar rate rewards C_star C_h u t hq z j)
      else currentRegisters rate rewards C_star C_h u t z := by
  split_ifs with hg
  · funext j
    exact nextRegisters_eq_queueTransition_of_G rate rewards C_star C_h u t hq z hg j
  · funext j
    exact nextRegisters_eq_current_of_not_G rate rewards C_star C_h u t hq z hg j

private theorem measurable_queueTransition {α : Type*} [MeasurableSpace α]
    (capacity : ℕ) (f : α → ℕ × ℕ) (g : α → ℕ)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z => QueueReplay.transition capacity (f z) (true, g z)) := by
  have hpure : Measurable (fun x : (ℕ × ℕ) × ℕ =>
      QueueReplay.transition capacity x.1 (true, x.2)) := measurable_of_countable _
  exact hpure.comp (hf.prodMk hg)

theorem measurable_nextRegisters (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    Measurable (nextRegisters rate rewards C_star C_h u t hq) := by
  have hcurrent := measurable_currentRegisters_ambient rate rewards C_star C_h u t
  have htransition : Measurable (fun z : Z => fun j : Fin p.K =>
      QueueReplay.transition
        (4 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
        (currentRegisters rate rewards C_star C_h u t z j)
        (true, naturalizedNextScalar rate rewards C_star C_h u t hq z j)) := by
    apply measurable_pi_iff.mpr
    intro j
    exact measurable_queueTransition _ _ _
      ((measurable_pi_apply j).comp hcurrent)
      (measurable_naturalizedNextScalar rate rewards C_star C_h u t control0 hq j)
  have hG : MeasurableSet {z : Z | G rate rewards C_star C_h u t hq z} :=
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) _
      (measurableSet_G rate rewards C_star C_h u t control0 hq)
  have heq : nextRegisters rate rewards C_star C_h u t hq =
      (fun z => if G rate rewards C_star C_h u t hq z then
        fun j => QueueReplay.transition
          (4 * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n)
          (currentRegisters rate rewards C_star C_h u t z j)
          (true, naturalizedNextScalar rate rewards C_star C_h u t hq z j)
      else currentRegisters rate rewards C_star C_h u t z) :=
    funext (nextRegisters_eq_ite rate rewards C_star C_h u t hq)
  rw [heq]
  exact Measurable.ite hG htransition hcurrent

theorem measurable_Vplus (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    Measurable (Vplus rate rewards C_star C_h u t hq) := by
  have hpure : Measurable (energyFromRegisters rate : (Fin p.K → ℕ × ℕ) → ℝ) :=
    measurable_of_countable _
  exact hpure.comp (measurable_nextRegisters rate rewards C_star C_h u t control0 hq)

private theorem measurable_optionRateEnabled (hq : t.val + 1 < p.T) :
    Measurable[Fq] (fun z : Z =>
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq).elim false Prod.fst) := by
  have hp := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_nextParameters
    rate rewards C_star C_h u t control0 hq
  exact (measurable_option_elim Prod.fst measurable_fst false).comp hp

private theorem measurable_optionRates (hq : t.val + 1 < p.T) :
    Measurable[Fq] (fun z : Z =>
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq).elim (fun _ : Fin p.K => 0) Prod.snd) := by
  have hp := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_nextParameters
    rate rewards C_star C_h u t control0 hq
  exact (measurable_option_elim Prod.snd measurable_snd
    (fun _ : Fin p.K => (0 : ℝ))).comp hp

theorem measurable_priorCost (hq : t.val + 1 < p.T) :
    Measurable[Fq] (priorCost rate rewards C_star C_h u t hq) := by
  let enabled : Z → Bool := fun z =>
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq).elim false Prod.fst
  let xi : Z → Fin p.K → ℝ := fun z =>
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq).elim (fun _ : Fin p.K => 0) Prod.snd
  have he : Measurable[Fq] enabled := measurable_optionRateEnabled rate rewards C_star C_h u t control0 hq
  have hx : Measurable[Fq] xi := measurable_optionRates rate rewards C_star C_h u t control0 hq
  have hsum : Measurable[Fq] (fun z : Z =>
      ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j / xi z j) := by
    apply Finset.measurable_fun_sum
    intro j hj
    exact (measurable_preTheta rate rewards C_star C_h u t control0 j).div
      ((measurable_pi_apply j).comp hx)
  have hformula : priorCost rate rewards C_star C_h u t hq = fun z =>
      if enabled z then
        ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j / xi z j
      else 0 := by
    funext z
    cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq with
    | none => simp [priorCost, enabled, hp]
    | some pair =>
        cases pair with
        | mk b rates =>
            cases b <;> simp [priorCost, enabled, xi, preTheta, hp]
  rw [hformula]
  exact Measurable.ite (he (measurableSet_singleton true)) hsum measurable_const

private theorem priorRate_beta_le (hq : t.val + 1 < p.T) (z : Z)
    (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (true, xi))
    (j : Fin p.K) : beta ≤ xi j := by
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none => simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
      hc] at hp
  | some c =>
      have hparams :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
          rate rewards C_star C_h u t hq z c hc
      have hxi : c.rate = xi := (Prod.mk.inj
        (Option.some.inj (hparams.symm.trans hp))).2
      have hcanonical :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical
          rate rewards C_star C_h u t z hq
      rw [hc] at hcanonical
      obtain ⟨view, _, _, hrateCanonical⟩ := hcanonical
      calc
        beta ≤ CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor j :=
          CanonicalRecordingRates.beta_le_xi p rate.eta.property view.payload.anchor j
        _ = c.rate j := (hrateCanonical j).symm
        _ = xi j := congrFun hxi j

theorem priorCost_bounds (hq : t.val + 1 < p.T) (z : Z) :
    0 ≤ priorCost rate rewards C_star C_h u t hq z ∧
      priorCost rate rewards C_star C_h u t hq z ≤ (p.m : ℝ) / beta := by
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hzero : 0 ≤ (p.m : ℝ) / beta :=
    div_nonneg (Nat.cast_nonneg _) hbeta.le
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none =>
      rw [priorCost, hp]
      exact ⟨le_rfl, hzero⟩
  | some params =>
      rcases params with ⟨enabled, xi⟩
      cases enabled
      · rw [priorCost, hp]
        exact ⟨le_rfl, hzero⟩
      · have hp' : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
            rate rewards C_star C_h u t z hq = some (true, xi) := by
          simpa using hp
        have hsum_nonneg : 0 ≤ ∑ j : Fin p.K,
            preTheta rate rewards C_star C_h u t z j / xi j := by
          apply Finset.sum_nonneg
          intro j hj
          exact div_nonneg
            (thetaFromRegisters_nonneg (p := p)
              (currentRegisters rate rewards C_star C_h u t z) j)
            (le_of_lt (lt_of_lt_of_le hbeta
              (priorRate_beta_le rate rewards C_star C_h u t hq z xi hp' j)))
        have hsum_le : (∑ j : Fin p.K,
            preTheta rate rewards C_star C_h u t z j / xi j) ≤ (p.m : ℝ) / beta := by
          calc
            _ ≤ ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j / beta :=
              Finset.sum_le_sum (fun j hj =>
                div_le_div_of_nonneg_left
                  (thetaFromRegisters_nonneg (p := p)
                    (currentRegisters rate rewards C_star C_h u t z) j)
                  hbeta (priorRate_beta_le rate rewards C_star C_h u t hq z xi hp' j))
            _ = (∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j) / beta := by
              rw [← Finset.sum_div]
            _ = (p.m : ℝ) / beta := by
              have hsum : (∑ j : Fin p.K,
                  preTheta rate rewards C_star C_h u t z j) = (p.m : ℝ) := by
                change (∑ j : Fin p.K,
                  thetaFromRegisters (p := p)
                    (currentRegisters rate rewards C_star C_h u t z) j) = (p.m : ℝ)
                exact sum_thetaFromRegisters (p := p)
                  (currentRegisters rate rewards C_star C_h u t z)
              rw [hsum]
        rw [priorCost, hp]
        exact ⟨hsum_nonneg, hsum_le⟩

theorem measurable_priorCost_ambient (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable (priorCost rate rewards C_star C_h u t hq) := by
  have hf := measurable_priorCost rate rewards C_star C_h u t control0 hq
  exact hf.mono
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl

theorem priorCost_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    Integrable (priorCost rate rewards C_star C_h u t hq) ν := by
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_priorCost_ambient rate rewards C_star C_h u t control0 hq)
    ((p.m : ℝ) / beta)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (priorCost_bounds rate rewards C_star C_h u t hq z).1]
  exact (priorCost_bounds rate rewards C_star C_h u t hq z).2

theorem measurable_backlogSum :
    Measurable[Fq] (fun z : Z =>
      backlogSumFromRegisters rate (currentRegisters rate rewards C_star C_h u t z)) := by
  change Measurable[Fq] (fun z : Z =>
    ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j *
      preBacklog rate rewards C_star C_h u t z j)
  apply Finset.measurable_fun_sum
  intro j hj
  exact (measurable_preTheta rate rewards C_star C_h u t control0 j).mul
    (measurable_preBacklog rate rewards C_star C_h u t control0 j)

theorem measurable_Bminus : Measurable[Fq] (Bminus rate rewards C_star C_h u t) := by
  change Measurable[Fq] (fun z : Z =>
    backlogSumFromRegisters rate (currentRegisters rate rewards C_star C_h u t z))
  exact measurable_backlogSum rate rewards C_star C_h u t control0

theorem preBacklog_bounds (z : Z) (j : Fin p.K) :
    0 ≤ preBacklog rate rewards C_star C_h u t z j ∧
      preBacklog rate rewards C_star C_h u t z j ≤ 2 * Bcap := by
  change 0 ≤
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
        rate rewards C_star C_h u t j z ∧
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
        rate rewards C_star C_h u t j z ≤ 2 * Bcap
  simpa using
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore_bounds
      rate rewards C_star C_h u t j z)

theorem preBacklog_le_Bcap_of_G (hq : t.val + 1 < p.T) (z : Z)
    (hg : G rate rewards C_star C_h u t hq z) (j : Fin p.K) :
    preBacklog rate rewards C_star C_h u t z j ≤ Bcap := by
  obtain ⟨⟨xi, hparams⟩, hclear⟩ :=
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
      rate rewards C_star C_h u t hq z).mp hg
  have hfalse :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
        rate rewards C_star C_h u t z).overflow = false := by
    rw [currentOverflow_eq_prior rate rewards C_star C_h u t z]
    exact hclear
  have htake :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z).take
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z).length =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z := by
    apply List.take_of_length_le
    exact le_rfl
  have hfalse' :
      (RecordedQueueRun.run
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z).take
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
            rate rewards C_star C_h u t z).length)).overflow = false := by
    rw [htake]
    change (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
      rate rewards C_star C_h u t z).overflow = false
    exact hfalse
  have hrun := _root_.Bandits.Support.StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
    (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z).length j hfalse'
  rw [htake] at hrun
  have hbound :
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
        rate rewards C_star C_h u t j z ≤ (rate.eta.val)⁻¹ * (32 : ℝ)⁻¹ := by
    simpa [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells,
      _root_.Bandits.Support.StoppedQueueBound.normalizedBacklog,
      _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters] using hrun
  have heta : 0 < rate.eta.val := rate.eta.property
  have hcapEq : (rate.eta.val)⁻¹ * (32 : ℝ)⁻¹ = Bcap := by
    field_simp [ne_of_gt heta]
  change _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
    rate rewards C_star C_h u t j z ≤ Bcap
  exact hbound.trans_eq hcapEq

theorem Vminus_bounds (z : Z) :
    0 ≤ Vminus rate rewards C_star C_h u t z ∧
      Vminus rate rewards C_star C_h u t z ≤
        4 * (p.m : ℝ) * Bcap ^ 2 := by
  have hback : ∀ j : Fin p.K,
      0 ≤ backlogFromRegisters rate (currentRegisters rate rewards C_star C_h u t z) j ∧
        backlogFromRegisters rate (currentRegisters rate rewards C_star C_h u t z) j ≤ 2 * Bcap := by
    intro j
    exact preBacklog_bounds rate rewards C_star C_h u t z j
  have hEta : 0 < rate.eta.val := rate.eta.property
  have hcap : 0 ≤ 2 * Bcap := by
    positivity
  have henergy := energyFromRegisters_bounded_nonneg rate
    (currentRegisters rate rewards C_star C_h u t z) (2 * Bcap) hcap hback
  constructor
  · simpa [Vminus] using henergy.1
  · change energyFromRegisters rate (currentRegisters rate rewards C_star C_h u t z) ≤ _
    nlinarith [henergy.2]

theorem Vplus_bounds (hq : t.val + 1 < p.T) (z : Z) :
    0 ≤ Vplus rate rewards C_star C_h u t hq z ∧
      Vplus rate rewards C_star C_h u t hq z ≤
        (p.m : ℝ) * (2 * Bcap + 1 / beta) ^ 2 := by
  have hback : ∀ j : Fin p.K,
      0 ≤ backlogFromRegisters rate (nextRegisters rate rewards C_star C_h u t hq z) j ∧
        backlogFromRegisters rate (nextRegisters rate rewards C_star C_h u t hq z) j ≤
          2 * Bcap + 1 / beta := by
    intro j
    change 0 ≤ postBacklog rate rewards C_star C_h u t hq z j ∧
      postBacklog rate rewards C_star C_h u t hq z j ≤ 2 * Bcap + 1 / beta
    rw [nextRegisters_backlog_eq rate rewards C_star C_h u t hq z j]
    simpa using
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogAfter_bounds
        rate rewards C_star C_h u t hq j z)
  have hcap : 0 ≤ 2 * Bcap + 1 / beta := by
    have hb : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
    have heta : 0 < rate.eta.val := rate.eta.property
    positivity
  have henergy := energyFromRegisters_bounded_nonneg rate
    (nextRegisters rate rewards C_star C_h u t hq z) (2 * Bcap + 1 / beta) hcap hback
  constructor
  · simpa [Vplus] using henergy.1
  · simpa [Vplus] using henergy.2

theorem Vplus_integrable (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    Integrable (Vplus rate rewards C_star C_h u t hq) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_Vplus rate rewards C_star C_h u t control0 hq)
    ((p.m : ℝ) * (2 * Bcap + 1 / beta) ^ 2)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (Vplus_bounds rate rewards C_star C_h u t hq z).1]
  exact (Vplus_bounds rate rewards C_star C_h u t hq z).2

theorem postBacklog_le_two_Bcap_of_G (hq : t.val + 1 < p.T) (z : Z)
    (hg : G rate rewards C_star C_h u t hq z) (j : Fin p.K) :
    postBacklog rate rewards C_star C_h u t hq z j ≤ 2 * Bcap := by
  rw [nextRegisters_backlog_eq rate rewards C_star C_h u t hq z j,
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogAfter_eq_reflected]
  rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextIncrement,
    ite_eq_left (by simpa [G, retainedNextDate] using hg)]
  have hpre := preBacklog_le_Bcap_of_G rate rewards C_star C_h u t hq z hg j
  have harr :=
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextArrival_bounds
      rate rewards C_star C_h u t hq j z).2
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hden : 0 < 32 * rate.eta.val :=
    mul_pos (by norm_num) rate.eta.property
  have hfactor : 32 * rate.eta.val ≤ beta := by
    have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
      exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
    calc
      32 * rate.eta.val = 32 * rate.eta.val * 1 := by ring
      _ ≤ 32 * rate.eta.val * (CanonicalRecordingRates.L_stab p : ℝ) :=
        mul_le_mul_of_nonneg_left hL (by positivity)
      _ = beta := by rfl
  have harr' : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextArrival
      rate rewards C_star C_h u t hq j z ≤ Bcap := by
    calc
      _ ≤ 1 / beta := harr
      _ ≤ 1 / (32 * rate.eta.val) := one_div_le_one_div_of_le hden hfactor
  have hpre' :
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
        rate rewards C_star C_h u t j z ≤ Bcap := by
    change _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogBefore
      rate rewards C_star C_h u t j z ≤ Bcap at hpre
    exact hpre
  have heta : 0 < rate.eta.val := rate.eta.property
  have hcap : 0 ≤ 2 * Bcap := by positivity
  rw [max_le_iff]
  constructor <;> linarith

theorem Bminus_bounds (z : Z) :
    0 ≤ Bminus rate rewards C_star C_h u t z ∧
      Bminus rate rewards C_star C_h u t z ≤ (p.m : ℝ) * (2 * Bcap) := by
  have hterms : ∀ j : Fin p.K,
      0 ≤ preTheta rate rewards C_star C_h u t z j *
          preBacklog rate rewards C_star C_h u t z j ∧
        preTheta rate rewards C_star C_h u t z j *
            preBacklog rate rewards C_star C_h u t z j ≤
          preTheta rate rewards C_star C_h u t z j * (2 * Bcap) := by
    intro j
    have hθ : 0 ≤ preTheta rate rewards C_star C_h u t z j ∧
        preTheta rate rewards C_star C_h u t z j ≤ 1 := ⟨thetaFromRegisters_nonneg (p := p)
      (currentRegisters rate rewards C_star C_h u t z) j,
      thetaFromRegisters_le_one (p := p)
        (currentRegisters rate rewards C_star C_h u t z) j⟩
    have hb := preBacklog_bounds rate rewards C_star C_h u t z j
    exact ⟨mul_nonneg hθ.1 hb.1, mul_le_mul_of_nonneg_left hb.2 hθ.1⟩
  constructor
  · change 0 ≤ ∑ j : Fin p.K,
      preTheta rate rewards C_star C_h u t z j * preBacklog rate rewards C_star C_h u t z j
    exact Finset.sum_nonneg (fun j hj => (hterms j).1)
  · change (∑ j : Fin p.K,
        preTheta rate rewards C_star C_h u t z j * preBacklog rate rewards C_star C_h u t z j) ≤ _
    calc
      _ ≤ ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j * (2 * Bcap) :=
        Finset.sum_le_sum (fun j hj => (hterms j).2)
      _ = (∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j) * (2 * Bcap) := by
        rw [Finset.sum_mul]
      _ = (p.m : ℝ) * (2 * Bcap) := by
        change (∑ j : Fin p.K,
          thetaFromRegisters (p := p) (currentRegisters rate rewards C_star C_h u t z) j) * _ = _
        rw [sum_thetaFromRegisters]

theorem measurable_Bminus_ambient (control0 : TimeControl p) :
    Measurable (Bminus rate rewards C_star C_h u t) := by
  have hf := measurable_Bminus rate rewards C_star C_h u t control0
  exact hf.mono
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl

theorem Bminus_integrable (control0 : TimeControl p) :
    Integrable (Bminus rate rewards C_star C_h u t) ν := by
  have heta : 0 < rate.eta.val := rate.eta.property
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_Bminus_ambient rate rewards C_star C_h u t control0)
    ((p.m : ℝ) * (2 * Bcap))
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (Bminus_bounds rate rewards C_star C_h u t z).1]
  exact (Bminus_bounds rate rewards C_star C_h u t z).2

theorem measurable_Vminus_field :
    Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] (Vminus rate rewards C_star C_h u t) := by
  change Measurable[Fq] (fun z : Z =>
    ∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j *
      preBacklog rate rewards C_star C_h u t z j ^ 2)
  apply Finset.measurable_fun_sum
  intro j hj
  exact (measurable_preTheta rate rewards C_star C_h u t control0 j).mul
    ((measurable_preBacklog rate rewards C_star C_h u t control0 j).pow_const 2)

theorem measurable_Vminus (control0 : TimeControl p) :
    Measurable (Vminus rate rewards C_star C_h u t) := by
  have hf := measurable_Vminus_field rate rewards C_star C_h u t control0
  exact hf.mono
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl

theorem Vminus_integrable (control0 : TimeControl p) :
    Integrable (Vminus rate rewards C_star C_h u t) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_Vminus rate rewards C_star C_h u t control0)
    (4 * (p.m : ℝ) * Bcap ^ 2)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (Vminus_bounds rate rewards C_star C_h u t z).1]
  exact (Vminus_bounds rate rewards C_star C_h u t z).2

theorem thetaFromRegisters_sum (A : Fin p.K → ℕ × ℕ) :
    (∑ j : Fin p.K, thetaFromRegisters (p := p) A j) = (p.m : ℝ) :=
  sum_thetaFromRegisters (p := p) A

theorem preTheta_sum (z : Z) :
    (∑ j : Fin p.K, preTheta rate rewards C_star C_h u t z j) = (p.m : ℝ) :=
  sum_thetaFromRegisters (p := p) (currentRegisters rate rewards C_star C_h u t z)

theorem postTheta_sum (hq : t.val + 1 < p.T) (z : Z) :
    (∑ j : Fin p.K, postTheta rate rewards C_star C_h u t hq z j) = (p.m : ℝ) :=
  sum_thetaFromRegisters (p := p) (nextRegisters rate rewards C_star C_h u t hq z)

theorem preTheta_bounds (z : Z) (j : Fin p.K) :
    0 ≤ preTheta rate rewards C_star C_h u t z j ∧
      preTheta rate rewards C_star C_h u t z j ≤ 1 := by
  exact ⟨thetaFromRegisters_nonneg (p := p) _ j,
    thetaFromRegisters_le_one (p := p) _ j⟩

theorem postTheta_bounds (hq : t.val + 1 < p.T) (z : Z) (j : Fin p.K) :
    0 ≤ postTheta rate rewards C_star C_h u t hq z j ∧
      postTheta rate rewards C_star C_h u t hq z j ≤ 1 := by
  exact ⟨thetaFromRegisters_nonneg (p := p) _ j,
    thetaFromRegisters_le_one (p := p) _ j⟩


/-! Exact one-cell aliases preserve the same producer run and its terminal
boundary branch. -/

theorem currentRegisters_eq_wholePostReadout (z : Z) :
    currentRegisters rate rewards C_star C_h u t z =
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z).1 :=
  congrArg Prod.fst
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
      rate rewards C_star C_h u t z)

abbrev actual_nextRun_acceptedRecord (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (j : Fin p.K) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_acceptedRecord
    rate rewards C_star C_h u t z c j

abbrev actual_nextRun_fullPrefix (z : Z) (c : RecordedQueueRun.RoundInput p.K) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.actual_nextRun_fullPrefix
    rate rewards C_star C_h u t z c

abbrev actual_nextRun_acceptedHistories (z : Z)
    (c : RecordedQueueRun.RoundInput p.K) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.actual_nextRun_acceptedHistories
    rate rewards C_star C_h u t z c

abbrev actual_nextScalar_present_run (hq : t.val + 1 < p.T) (j : Fin p.K)
    (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.actual_nextScalar_present_run
    rate rewards C_star C_h u t hq j z c hc

abbrev actual_nextDate_physical_prefix (z : Z) (hq : t.val + 1 < p.T) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.actual_nextDate_physical_prefix
    rate rewards C_star C_h u t z hq

abbrev terminal_physical_prefix (z : Z) (ht : t.val + 1 = p.T) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.terminal_physical_prefix
    rate rewards C_star C_h u t z ht

theorem Vplus_none (hq : t.val + 1 < p.T) (z : Z)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = none) :
    Vplus rate rewards C_star C_h u t hq z = Vminus rate rewards C_star C_h u t z := by
  change energyFromRegisters rate (nextRegisters rate rewards C_star C_h u t hq z) =
    energyFromRegisters rate (currentRegisters rate rewards C_star C_h u t z)
  simp [nextRegisters, hc]

theorem nextRegisters_none (hq : t.val + 1 < p.T) (z : Z)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = none) :
    nextRegisters rate rewards C_star C_h u t hq z =
      currentRegisters rate rewards C_star C_h u t z := by
  simp [nextRegisters, hc]

theorem Vplus_some (hq : t.val + 1 < p.T) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :
    Vplus rate rewards C_star C_h u t hq z = energyFromRegisters rate
      (RecordedQueueRun.step
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) c).registers := by
  change energyFromRegisters rate (nextRegisters rate rewards C_star C_h u t hq z) =
    energyFromRegisters rate
      (RecordedQueueRun.step
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) c).registers
  simp [nextRegisters, hc]

theorem nextRegisters_some (hq : t.val + 1 < p.T) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :
    nextRegisters rate rewards C_star C_h u t hq z =
      (RecordedQueueRun.step
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) c).registers := by
  simp [nextRegisters, hc]

theorem nextRegisters_preserved_of_not_G (hq : t.val + 1 < p.T) (z : Z)
    (hnot : ¬ G rate rewards C_star C_h u t hq z) :
    nextRegisters rate rewards C_star C_h u t hq z =
      currentRegisters rate rewards C_star C_h u t z := by
  funext j
  exact nextRegisters_eq_current_of_not_G rate rewards C_star C_h u t hq z hnot j

theorem Vplus_eq_Vminus_of_not_G (hq : t.val + 1 < p.T) (z : Z)
    (hnot : ¬ G rate rewards C_star C_h u t hq z) :
    Vplus rate rewards C_star C_h u t hq z =
      Vminus rate rewards C_star C_h u t z := by
  unfold Vplus Vminus
  rw [nextRegisters_preserved_of_not_G rate rewards C_star C_h u t hq z hnot]

local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "θ" => preTheta rate rewards C_star C_h u t
local notation "b" => preBacklog rate rewards C_star C_h u t
local notation "a" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextArrival
  rate rewards C_star C_h u t

private theorem step_scoreWeight_bounds (state : RecordedQueueRun.RunState p.K)
    (cell : RecordedQueueRun.RoundInput p.K) (j : Fin p.K) :
    RecordedQueueRun.scoreWeight Q state j ≤ RecordedQueueRun.scoreWeight Q
        (RecordedQueueRun.step Q state cell) j ∧
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) j ≤
        Real.exp (4 * rate.eta.val) * RecordedQueueRun.scoreWeight Q state j := by
  have hs0 := RecordedPotentialStep.servedEstimate_nonneg Q state cell j
  have hs4 := RecordedPotentialStep.servedEstimate_le_four Q state cell j
  have hl0 := (RecordedPotentialStep.potentialLambda_pos Q).le
  have hl : RecordedPotentialStep.potentialLambda Q ≤ rate.eta.val :=
    RecordedPotentialStep.potentialLambda_le_eta Q
  have hx : RecordedPotentialStep.potentialLambda Q *
      RecordedPotentialStep.servedEstimate Q state cell j ≤ 4 * rate.eta.val := by
    calc
      _ ≤ RecordedPotentialStep.potentialLambda Q * 4 := mul_le_mul_of_nonneg_left hs4 hl0
      _ ≤ 4 * rate.eta.val := by nlinarith only [hl]
  rw [RecordedPotentialStep.step_scoreWeight_eq_mul_exp]
  have hw := (RecordedPotentialStep.scoreWeight_pos Q state j).le
  constructor
  · exact le_mul_of_one_le_right hw (Real.one_le_exp (mul_nonneg hl0 hs0))
  · calc
      _ ≤ RecordedQueueRun.scoreWeight Q state j * Real.exp (4 * rate.eta.val) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hx) hw
      _ = _ := mul_comm _ _

private theorem theta_growth_of_weights (v w : Fin p.K → ℝ)
    (hv : ∀ j, 0 < v j) (hw : ∀ j, 0 < w j)
    (hb : ∀ j, v j ≤ w j ∧ w j ≤ Real.exp (4 * rate.eta.val) * v j)
    (j : Fin p.K) :
    ProductSetLaw.theta p.m w j ≤ Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v j := by
  let mid := Function.update w j (v j)
  let c := w j / v j
  have hmid : ∀ i, 0 < mid i := by
    intro i
    by_cases hi : i = j <;> simp [mid, hi, hv, hw]
  have hown : v j = mid j := by simp [mid]
  have hother : ∀ i, i ≠ j → v i ≤ mid i := by
    intro i hi
    simpa [mid, hi] using (hb i).1
  have hmono := ProductMarginalStability.theta_antitone_of_other_coord_le v mid j
    p.two_le_m p.m_lt_K hv hmid hown hother
  have hc : 1 ≤ c := (le_div_iff₀ (hv j)).mpr (by simpa using (hb j).1)
  have hc' : c ≤ Real.exp (4 * rate.eta.val) := (div_le_iff₀ (hv j)).mpr (hb j).2
  have hprod : c * v j = w j := div_mul_cancel₀ _ (hv j).ne'
  have hup : Function.update mid j (c * v j) = w := by
    funext i
    by_cases hi : i = j <;> simp [mid, hi, hprod]
  have hscale := ProductMarginalStability.theta_update_le mid j c
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hmid hc
  rw [← hown, hup] at hscale
  calc
    _ ≤ c * ProductSetLaw.theta p.m mid j := hscale
    _ ≤ c * ProductSetLaw.theta p.m v j := mul_le_mul_of_nonneg_left hmono (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right hc'
      (ProductSetLaw.theta_pos v j (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K hv).le

theorem postTheta_growth (hq : t.val + 1 < p.T) (z : Z) (j : Fin p.K) :
    postTheta rate rewards C_star C_h u t hq z j ≤
        Real.exp (4 * rate.eta.val) * θ z j ∧
      postTheta rate rewards C_star C_h u t hq z j ≤ (1 + 8 * rate.eta.val) * θ z j := by
  have hweights : ∀ i, weightFromRegisters (p := p)
      (currentRegisters rate rewards C_star C_h u t z) i ≤
        weightFromRegisters (nextRegisters rate rewards C_star C_h u t hq z) i ∧
      weightFromRegisters (nextRegisters rate rewards C_star C_h u t hq z) i ≤
        Real.exp (4 * rate.eta.val) *
          weightFromRegisters (currentRegisters rate rewards C_star C_h u t z) i := by
    intro i
    cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq with
    | none =>
        rw [nextRegisters_none rate rewards C_star C_h u t hq z hc]
        exact ⟨le_rfl, le_mul_of_one_le_left (weightFromRegisters_pos _ i).le
          (Real.one_le_exp (mul_nonneg (by norm_num) rate.eta.property.le))⟩
    | some cell =>
        rw [nextRegisters_some rate rewards C_star C_h u t hq z cell hc]
        exact step_scoreWeight_bounds rate
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) cell i
  have hg := theta_growth_of_weights rate _ _
    (weightFromRegisters_pos _) (weightFromRegisters_pos _) hweights j
  have hx0 : 0 ≤ 4 * rate.eta.val := mul_nonneg (by norm_num) rate.eta.property.le
  have hx1 := CanonicalQueueProcess.four_mul_eta_le_one p rate.eta.property rate.sourceCap
  have he := RecordedPotentialStep.exp_le_one_add_add_sq hx0 hx1
  have hexp : Real.exp (4 * rate.eta.val) ≤ 1 + 8 * rate.eta.val := by nlinarith
  exact ⟨hg, hg.trans (mul_le_mul_of_nonneg_right hexp (preTheta_bounds rate rewards C_star C_h u t z j).1)⟩

private theorem reflected_quadratic_bound (η cap x y z : ℝ)
    (hη : 0 ≤ η) (hcap : 8 * η * (2 * cap) = 1 / 2)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : z = max (x + y - 4) 0)
    (hzcap : z ≤ 2 * cap) :
    z ^ 2 - x ^ 2 + 8 * η * z ^ 2 ≤
      (-15 / 2 : ℝ) * x + (2 * x + 1 / 2) * y + y ^ 2 + 16 := by
  have hz0 : 0 ≤ z := hz ▸ le_max_right _ _
  have hsum : z ≤ x + y := by rw [hz]; exact max_le (by linarith) (add_nonneg hx hy)
  have hsq : z ^ 2 ≤ (x + y - 4) ^ 2 := by
    rw [hz]
    by_cases h : 0 ≤ x + y - 4
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h), zero_pow (by decide : 2 ≠ 0)]
      exact sq_nonneg (x + y - 4)
  have hquad : z ^ 2 ≤ 2 * cap * (x + y) := by
    simpa only [pow_two] using mul_le_mul hzcap hsum hz0 (hz0.trans hzcap)
  have hquad' := mul_le_mul_of_nonneg_left hquad (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hη)
  rw [← mul_assoc, hcap] at hquad'
  nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hy]

def reducedEnergyArm (hq : t.val + 1 < p.T) (j : Fin p.K) (z : Z) : ℝ :=
  θ z j * ((-15 / 2 : ℝ) * b z j + (2 * b z j + 1 / 2) * a hq j z + (a hq j z) ^ 2 + 16)

theorem weighted_energy_step (hq : t.val + 1 < p.T) (z : Z) :
    Vplus rate rewards C_star C_h u t hq z - Vminus rate rewards C_star C_h u t z ≤
      {z : Z | G rate rewards C_star C_h u t hq z}.indicator
        (fun z => ∑ j, reducedEnergyArm rate rewards C_star C_h u t hq j z) z := by
  by_cases hg : G rate rewards C_star C_h u t hq z
  · rw [Set.indicator_of_mem (s := {z : Z | G rate rewards C_star C_h u t hq z}) hg]
    rw [Vplus_eq_sum, Vminus_eq_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have href : postBacklog rate rewards C_star C_h u t hq z j = max (b z j + a hq j z - 4) 0 := by
      rw [nextRegisters_backlog_eq,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.backlogAfter_eq_reflected,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextIncrement,
        ite_eq_left (by simpa [G, retainedNextDate] using hg)]
      change max (b z j + (a hq j z - 4)) 0 = _
      congr 1
      ring
    have hcap : 8 * rate.eta.val * (2 * Bcap) = (1 / 2 : ℝ) := by
      field_simp [rate.eta.property.ne']; ring
    have hquad := reflected_quadratic_bound rate.eta.val Bcap (b z j) (a hq j z)
      (postBacklog rate rewards C_star C_h u t hq z j) rate.eta.property.le hcap
      (preBacklog_bounds rate rewards C_star C_h u t z j).1
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.nextArrival_bounds
        rate rewards C_star C_h u t hq j z).1 href
      (postBacklog_le_two_Bcap_of_G rate rewards C_star C_h u t hq z hg j)
    have hmarg := mul_le_mul_of_nonneg_right
      (postTheta_growth rate rewards C_star C_h u t hq z j).2
      (sq_nonneg (postBacklog rate rewards C_star C_h u t hq z j))
    have hmul := mul_le_mul_of_nonneg_left hquad (preTheta_bounds rate rewards C_star C_h u t z j).1
    dsimp only [reducedEnergyArm]
    nlinarith only [hmarg, hmul]
  · rw [Set.indicator_of_notMem (s := {z : Z | G rate rewards C_star C_h u t hq z}) hg, Vplus_eq_Vminus_of_not_G rate rewards C_star C_h u t hq z hg]
    exact sub_self _ |>.le

local notation "M1" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne
  rate rewards C_star C_h u t
local notation "M2" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentTwo
  rate rewards C_star C_h u t
local notation "Gset" hq => Set.ofPred (fun z : Z => G rate rewards C_star C_h u t hq z)

private theorem arm_condExp (hq : t.val + 1 < p.T) (j : Fin p.K) :
    Integrable (reducedEnergyArm rate rewards C_star C_h u t hq j) ν ∧
    ν[reducedEnergyArm rate rewards C_star C_h u t hq j | Fq] =ᵐ[ν]
      fun z => θ z j * ((-15 / 2 : ℝ) * b z j +
        (2 * b z j + 1 / 2) * M1 hq j z + M2 hq j z + 16) := by
  let θj : Z → ℝ := fun z => θ z j
  let bj : Z → ℝ := fun z => b z j
  let coeff : Z → ℝ := fun z => θj z * (2 * bj z + 1 / 2)
  let base : Z → ℝ := fun z => (-15 / 2 : ℝ) * (θj z * bj z) + 16 * θj z
  have hle := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hθ : Measurable[Fq] θj := measurable_preTheta rate rewards C_star C_h u t control0 j
  have hb : Measurable[Fq] bj := measurable_preBacklog rate rewards C_star C_h u t control0 j
  have hc : Measurable[Fq] coeff := hθ.mul ((measurable_const.mul hb).add measurable_const)
  have hbase : Measurable[Fq] base := (measurable_const.mul (hθ.mul hb)).add (measurable_const.mul hθ)
  have hθbound : ∀ᵐ z ∂ν, ‖θj z‖ ≤ 1 := ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (preTheta_bounds rate rewards C_star C_h u t z j).1]
    exact (preTheta_bounds rate rewards C_star C_h u t z j).2
  have hcbound : ∀ᵐ z ∂ν, ‖coeff z‖ ≤ 4 * Bcap + 1 / 2 := ae_of_all _ fun z => by
    have ht := preTheta_bounds rate rewards C_star C_h u t z j
    have hback := preBacklog_bounds rate rewards C_star C_h u t z j
    have hcoef0 : 0 ≤ 2 * bj z + 1 / 2 := by dsimp [bj]; linarith only [hback.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.1 hcoef0)]
    exact (mul_le_mul_of_nonneg_right ht.2 hcoef0).trans (by dsimp [bj]; linarith only [hback.2])
  have hθint : Integrable θj ν :=
    (integrable_const (1 : ℝ)).mono' (hθ.mono hle le_rfl).aestronglyMeasurable hθbound
  have hbint : Integrable bj ν := by
    apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
      (hb.mono hle le_rfl) (2 * Bcap)
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (preBacklog_bounds rate rewards C_star C_h u t z j).1]
    exact (preBacklog_bounds rate rewards C_star C_h u t z j).2
  have htb := hbint.bdd_mul (hθ.mono hle le_rfl).aestronglyMeasurable hθbound
  have hbaseInt : Integrable base ν := (htb.const_mul (-15 / 2 : ℝ)).add (hθint.const_mul 16)
  have ha := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_integrable
    rate rewards C_star C_h u t control0 hq j
  have ha2 := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_sq_integrable
    rate rewards C_star C_h u t control0 hq j
  have hca : Integrable (coeff * a hq j) ν := ha.bdd_mul (hc.mono hle le_rfl).aestronglyMeasurable hcbound
  have hta2 : Integrable (θj * fun z => (a hq j z) ^ 2) ν :=
    ha2.bdd_mul (hθ.mono hle le_rfl).aestronglyMeasurable hθbound
  have hshape : reducedEnergyArm rate rewards C_star C_h u t hq j =
      (coeff * a hq j + θj * (fun z => (a hq j z) ^ 2)) + base := by
    funext z
    dsimp [reducedEnergyArm, coeff, base, θj, bj]
    ring
  constructor
  · rw [hshape]; exact (hca.add hta2).add hbaseInt
  · rw [hshape]
    have hpull := condExp_mul_of_stronglyMeasurable_left hc.stronglyMeasurable hca ha
    have hpull2 := condExp_mul_of_stronglyMeasurable_left hθ.stronglyMeasurable hta2 ha2
    have hbaseCE := condExp_of_stronglyMeasurable hle hbase.stronglyMeasurable hbaseInt
    have hm1 := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_condExp
      rate rewards C_star C_h u t control0 hq j
    have hm2 := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_sq_condExp
      rate rewards C_star C_h u t control0 hq j
    filter_upwards [condExp_add (hca.add hta2) hbaseInt Fq, condExp_add hca hta2 Fq,
      hpull, hpull2, hm1, hm2] with z hsum hsum' hp hp2 hm1 hm2
    simp only [Pi.add_apply] at hsum hsum'
    rw [hsum, hsum', hp, hp2, hbaseCE]
    change coeff z * ν[a hq j | Fq] z + θj z * ν[(fun z => (a hq j z) ^ 2) | Fq] z + base z = _
    change ν[a hq j | Fq] z = M1 hq j z at hm1
    change ν[(fun z => (a hq j z) ^ 2) | Fq] z = M2 hq j z at hm2
    rw [hm1, hm2]
    dsimp [coeff, base, θj, bj]
    ring

theorem conditionalWeightedEnergyDrift (hq : t.val + 1 < p.T) :
    ν[(fun z => Vplus rate rewards C_star C_h u t hq z - Vminus rate rewards C_star C_h u t z) | Fq] ≤ᵐ[ν]
      (Gset hq).indicator (fun z => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
        priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m) := by
  have hle := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG := measurableSet_G rate rewards C_star C_h u t control0 hq
  have hsumInt : Integrable (fun z => ∑ j, reducedEnergyArm rate rewards C_star C_h u t hq j z) ν :=
    integrable_finsetSum _ (fun j _ => (arm_condExp rate rewards C_star C_h u t control0 hq j).1)
  have hmono := condExp_mono (m := Fq)
    ((Vplus_integrable rate rewards C_star C_h u t control0 hq).sub
      (Vminus_integrable rate rewards C_star C_h u t control0))
    (hsumInt.indicator (hle _ hG))
    (ae_of_all _ (weighted_energy_step rate rewards C_star C_h u t hq))
  have hmask := condExp_indicator hsumInt hG
  have hsumCE := condExp_finsetSum (s := Finset.univ) (fun j _ =>
    (arm_condExp rate rewards C_star C_h u t control0 hq j).1) Fq
  have hsumfun : (fun z => ∑ j, reducedEnergyArm rate rewards C_star C_h u t hq j z) =
      ∑ j, reducedEnergyArm rate rewards C_star C_h u t hq j := by
    funext z
    simp only [Finset.sum_apply]
  have hchange := condExp_congr_ae (m := Fq) (ae_of_all ν (congrFun hsumfun))
  have harms := ae_all_iff.mpr (fun j => (arm_condExp rate rewards C_star C_h u t control0 hq j).2)
  filter_upwards [hmono, hmask, hsumCE, harms, hchange] with z hmono hmask hsumCE harms hchange
  rw [hmask] at hmono
  by_cases hg : G rate rewards C_star C_h u t hq z
  · rw [Set.indicator_of_mem (s := Gset hq) hg] at hmono ⊢
    obtain ⟨⟨xi, hp⟩, hover⟩ :=
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
        rate rewards C_star C_h u t hq z).mp hg
    have hterms (j : Fin p.K) : θ z j * ((-15 / 2 : ℝ) * b z j +
        (2 * b z j + 1 / 2) * M1 hq j z + M2 hq j z + 16) ≤
        -(11 / 2 : ℝ) * (θ z j * b z j) + θ z j / xi j + (33 / 2 : ℝ) * θ z j := by
      have hm1 := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne_retained_bounds
        rate rewards C_star C_h u t hq j z xi hp hover
      have hm2 := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentTwo_retained_bounds
        rate rewards C_star C_h u t hq j z xi hp hover
      have ht := (preTheta_bounds rate rewards C_star C_h u t z j).1
      have hb := (preBacklog_bounds rate rewards C_star C_h u t z j).1
      have hm := mul_le_mul_of_nonneg_left (hm1.2.1.trans hm1.2.2)
        (mul_nonneg ht (by linarith only [hb] : 0 ≤ 2 * b z j + 1 / 2))
      have hm' := mul_le_mul_of_nonneg_left hm2.2.2 ht
      simp only [div_eq_mul_inv, one_mul] at hm' ⊢
      nlinarith only [hm, hm']
    calc
      _ ≤ ν[(fun z => ∑ j, reducedEnergyArm rate rewards C_star C_h u t hq j z) | Fq] z := hmono
      _ = ∑ j, θ z j * ((-15 / 2 : ℝ) * b z j +
          (2 * b z j + 1 / 2) * M1 hq j z + M2 hq j z + 16) := by
        rw [hchange, hsumCE]
        simp only [Finset.sum_apply]
        exact Finset.sum_congr rfl (fun j _ => harms j)
      _ ≤ ∑ j, (-(11 / 2 : ℝ) * (θ z j * b z j) + θ z j / xi j + (33 / 2 : ℝ) * θ z j) :=
        Finset.sum_le_sum (fun j _ => hterms j)
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          preTheta_sum]
        change -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
          (∑ j, θ z j / xi j) + (33 / 2 : ℝ) * p.m = _
        simp only [priorCost, hp, preTheta]
  · rw [Set.indicator_of_notMem (s := Gset hq) hg] at hmono ⊢
    exact hmono

theorem weightedEnergyAccounting (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) * ∫ z, (Gset hq).indicator (Bminus rate rewards C_star C_h u t) z ∂ν ≤
      (∫ z, (Gset hq).indicator (fun z => priorCost rate rewards C_star C_h u t hq z +
        (33 / 2 : ℝ) * p.m) z ∂ν) +
      (∫ z, Vminus rate rewards C_star C_h u t z ∂ν) -
      ∫ z, Vplus rate rewards C_star C_h u t hq z ∂ν := by
  have hle := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG := hle _ (measurableSet_G rate rewards C_star C_h u t control0 hq)
  have hi := Vminus_integrable rate rewards C_star C_h u t control0
  have ho := Vplus_integrable rate rewards C_star C_h u t control0 hq
  have hb := (Bminus_integrable rate rewards C_star C_h u t control0).indicator hG
  have hc : Integrable ((Gset hq).indicator (fun z =>
      priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m)) ν :=
    ((priorCost_integrable rate rewards C_star C_h u t control0 hq).add
      (integrable_const ((33 / 2 : ℝ) * p.m))).indicator hG
  have hshape : (Gset hq).indicator (fun z => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
      priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m) =
      (fun z => -(11 / 2 : ℝ) * (Gset hq).indicator (Bminus rate rewards C_star C_h u t) z +
        (Gset hq).indicator (fun z => priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m) z) := by
    funext z
    by_cases hg : z ∈ Gset hq
    · simp only [Set.indicator_of_mem hg]; ring
    · simp only [Set.indicator_of_notMem hg, mul_zero, add_zero]
  have hrhs : Integrable ((Gset hq).indicator (fun z => -(11 / 2 : ℝ) * Bminus rate rewards C_star C_h u t z +
      priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m)) ν := by
    rw [hshape]
    exact (hb.const_mul (-(11 / 2 : ℝ))).add hc
  have h := integral_mono_ae integrable_condExp hrhs
    (conditionalWeightedEnergyDrift rate rewards C_star C_h u t control0 hq)
  rw [integral_condExp hle, integral_sub ho hi, hshape] at h
  dsimp only at h
  rw [integral_add (hb.const_mul (-(11 / 2 : ℝ))) hc, integral_const_mul] at h
  linarith only [h]

theorem weightedEnergyAccounting_beta (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) * ∫ z, (Gset hq).indicator (Bminus rate rewards C_star C_h u t) z ∂ν ≤
      (∫ z, (Gset hq).indicator (fun _ : Z => (p.m : ℝ) / beta + (33 / 2 : ℝ) * p.m) z ∂ν) +
      (∫ z, Vminus rate rewards C_star C_h u t z ∂ν) -
      ∫ z, Vplus rate rewards C_star C_h u t hq z ∂ν := by
  have hle := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG := hle _ (measurableSet_G rate rewards C_star C_h u t control0 hq)
  have hc : Integrable ((Gset hq).indicator (fun z =>
      priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m)) ν :=
    ((priorCost_integrable rate rewards C_star C_h u t control0 hq).add
      (integrable_const ((33 / 2 : ℝ) * p.m))).indicator hG
  have hk := (integrable_const ((p.m : ℝ) / beta + (33 / 2 : ℝ) * p.m) (μ := ν)).indicator hG
  have hcost := integral_mono_ae hc hk (ae_of_all ν fun z => by
    by_cases hg : z ∈ Gset hq
    · simp only [Set.indicator_of_mem hg]
      exact add_le_add (priorCost_bounds rate rewards C_star C_h u t hq z).2 le_rfl
    · simp only [Set.indicator_of_notMem hg, le_refl])
  linarith only [weightedEnergyAccounting rate rewards C_star C_h u t control0 hq, hcost]

end Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep

end
