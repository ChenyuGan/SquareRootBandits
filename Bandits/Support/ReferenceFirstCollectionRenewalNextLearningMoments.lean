/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# First-renewal next-date rounded learning moments

This module isolates the actual calendar date immediately following the first
renewal call. All observations use the existing unnormalized renewal source and
the optional cell already installed by its physical prefix.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextLearningMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)

abbrev Source :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Source
    rate rewards C_star C_h u t

local notation "Z" => Source rate rewards C_star C_h u t
local notation "ν" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "Fq" =>
  ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
local notation "G" =>
  ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
    rate rewards C_star C_h u t
local notation "θ" =>
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta
    rate rewards C_star C_h u t
local notation "a" =>
  ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar
    rate rewards C_star C_h u t
local notation "m₁" =>
  ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne
    rate rewards C_star C_h u t
local notation "r" =>
  ReferenceFirstCollectionRenewalNextRecordingMoments.rewardAt rewards t

local instance renewalLawFinite : IsFiniteMeasure ν :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite
    rate rewards C_star C_h u t

def arrivalObservation (hq : t.val + 1 < p.T) (z : Z) : ℝ :=
  (G hq).indicator (fun z => ∑ j : Fin p.K, θ z j * a hq j z) z

def comparatorObservation (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  (G hq).indicator
    (fun z => (∑ j ∈ S.1, a hq j z) -
      ∑ j : Fin p.K, θ z j * a hq j z) z

def roundedRewardGap (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  (G hq).indicator
    (fun z => (∑ j ∈ S.1, r hq j) -
      ∑ j : Fin p.K, θ z j * r hq j) z

/-- Natural-date selector for the immediate next-date arrival observation.
At the horizon boundary it returns zero without constructing a `Fin p.T`. -/
def naturalArrivalObservation (z : Z) : ℝ :=
  if hq : t.val + 1 < p.T then
    arrivalObservation rate rewards C_star C_h u t hq z else 0

/-- Natural-date selector for the immediate next-date comparator observation. -/
def naturalComparatorObservation
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  if hq : t.val + 1 < p.T then
    comparatorObservation rate rewards C_star C_h u t hq S z else 0

/-- Natural-date selector for the immediate next-date rounded reward gap. -/
def naturalRoundedRewardGap
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  if hq : t.val + 1 < p.T then
    roundedRewardGap rate rewards C_star C_h u t hq S z else 0

/-- Natural-date indicator of the retained next-date gate. -/
def naturalRetainedIndicator (z : Z) : ℝ :=
  if hq : t.val + 1 < p.T then
    (G hq).indicator (fun _ : Z => (1 : ℝ)) z else 0

/-- The same actual source prefix, including both the continuing and cutoff
constructors of its first next-date cell. -/
abbrev actual_nextDate_physical_prefix (z : Z)
    (hq : t.val + 1 < p.T) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.actual_nextDate_physical_prefix
    rate rewards C_star C_h u t z hq

/-- Incoming registers are the original whole-call post-readout registers. -/
abbrev currentRegisters_eq_wholePostReadout (z : Z) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.currentRegisters_eq_wholePostReadout
    rate rewards C_star C_h u t z

/-- A present q-cell scalar is its accepted raw arrival divided by the
queue denominator, with its actual accepted-record and full-prefix recursion. -/
abbrev actual_nextScalar_present_run (hq : t.val + 1 < p.T)
    (j : Fin p.K) (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.actual_nextScalar_present_run
    rate rewards C_star C_h u t hq j z c hc

/-- The scalar observations read the present optional cell appended to the
same inherited original run. In particular the accepted first detecting
update is retained by the run recursion. -/
theorem observations_eq_actual_present_cell (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :
    (arrivalObservation rate rewards C_star C_h u t hq z =
      (if z ∈ G hq then
        ∑ j : Fin p.K, θ z j *
          RecordedRoundMoments.rawEstimate
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c j
      else 0)) ∧
    (comparatorObservation rate rewards C_star C_h u t hq S z =
      (if z ∈ G hq then
        (∑ j ∈ S.1, RecordedRoundMoments.rawEstimate
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c j) -
        ∑ j : Fin p.K, θ z j *
          RecordedRoundMoments.rawEstimate
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c j
      else 0)) ∧
    (roundedRewardGap rate rewards C_star C_h u t hq S z =
      (if z ∈ G hq then
        (∑ j ∈ S.1, r hq j) - ∑ j : Fin p.K, θ z j * r hq j
      else 0)) := by
  have hraw (j : Fin p.K) :=
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.actual_nextScalar_present_run
      rate rewards C_star C_h u t hq j z c hc).1
  constructor
  · by_cases hg : z ∈ G hq
    · simp [arrivalObservation, hg, hraw]
    · simp [arrivalObservation, hg]
  · constructor
    · by_cases hg : z ∈ G hq
      · simp [comparatorObservation, hg, hraw]
      · simp [comparatorObservation, hg]
    · by_cases hg : z ∈ G hq
      · simp [roundedRewardGap, hg]
      · simp [roundedRewardGap, hg]

/-- On the retained gate, the actual next parameters are the same enabled
cell rate vector and the pre-date overflow flag is clear. -/
theorem retained_nextCell_data (hq : t.val + 1 < p.T) (z : Z)
    (hz : z ∈ G hq) :
    ∃ c xi,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = some c ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq = some (true, xi) ∧
      c.enabled = true ∧ c.rate = xi ∧
      ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
        rate rewards C_star C_h u t z = false := by
  rcases (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
      rate rewards C_star C_h u t hq z).1 hz with ⟨⟨xi, hparam⟩, hoverflow⟩
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none =>
      simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
        hc] at hparam
  | some c =>
      have hpresent := ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
        rate rewards C_star C_h u t hq z c hc
      have hpair : (c.enabled, c.rate) = (true, xi) :=
        Option.some.inj (hpresent.symm.trans hparam)
      exact ⟨c, xi, rfl, hparam, congrArg Prod.fst hpair,
        congrArg Prod.snd hpair, hoverflow⟩


private def gatedThetaScalar (hq : t.val + 1 < p.T)
    (j : Fin p.K) (z : Z) : ℝ :=
  (G hq).indicator (fun z => θ z j) z * a hq j z

private def gatedScalar (hq : t.val + 1 < p.T)
    (j : Fin p.K) (z : Z) : ℝ :=
  (G hq).indicator (fun _ : Z => (1 : ℝ)) z * a hq j z

private theorem integrable_of_measurable_norm_le_const
    {f : Z → ℝ} (hf : Measurable f) (C : ℝ)
    (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

private theorem preTheta_measurable (control0 : TimeControl p) (j : Fin p.K) :
    Measurable (θ · j) :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurable_preTheta
    rate rewards C_star C_h u t control0 j).mono
    (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl

private theorem nextScalar_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (j : Fin p.K) : Measurable (a hq j) :=
  ReferenceFirstCollectionRenewalNextRecordingMoments.measurable_nextScalar
    rate rewards C_star C_h u t control0 hq j

private theorem nextScalar_nonneg (hq : t.val + 1 < p.T)
    (j : Fin p.K) (z : Z) : 0 ≤ a hq j z :=
  (ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_bounds
    rate rewards C_star C_h u t hq j z).1

private theorem nextScalar_le_invBeta (hq : t.val + 1 < p.T)
    (j : Fin p.K) (z : Z) :
    a hq j z ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
  (ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_bounds
    rate rewards C_star C_h u t hq j z).2

private theorem preTheta_bounds (j : Fin p.K) (z : Z) :
    0 ≤ θ z j ∧ θ z j ≤ 1 :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta_bounds
    rate rewards C_star C_h u t z j

private theorem retained_measurable (hq : t.val + 1 < p.T) :
    MeasurableSet[Fq] (G hq) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
    rate rewards C_star C_h u t control0 hq

private theorem retained_measurable_ambient (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) : MeasurableSet (G hq) :=
  (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0) (G hq)
    (retained_measurable rate rewards C_star C_h u t control0 hq)

private theorem arrivalInner_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable (fun z : Z => ∑ j : Fin p.K, θ z j * a hq j z) := by
  apply Finset.measurable_sum Finset.univ
  intro j hj
  exact (preTheta_measurable rate rewards C_star C_h u t control0 j).mul
    (nextScalar_measurable rate rewards C_star C_h u t control0 hq j)

private theorem selectedArrival_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (fun z : Z => ∑ j ∈ S.1, a hq j z) := by
  apply Finset.measurable_sum S.1
  intro j hj
  exact nextScalar_measurable rate rewards C_star C_h u t control0 hq j

private theorem rewardGapInner_measurable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (fun z : Z =>
      (∑ j ∈ S.1, r hq j) - ∑ j : Fin p.K, θ z j * r hq j) := by
  apply measurable_const.sub
  apply Finset.measurable_sum Finset.univ
  intro j hj
  exact (preTheta_measurable rate rewards C_star C_h u t control0 j).mul
    measurable_const

theorem measurable_arrivalObservation (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    Measurable (arrivalObservation rate rewards C_star C_h u t hq) :=
  (arrivalInner_measurable rate rewards C_star C_h u t control0 hq).indicator
    (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)

theorem measurable_comparatorObservation (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (comparatorObservation rate rewards C_star C_h u t hq S) := by
  have hinner :=
    (selectedArrival_measurable rate rewards C_star C_h u t control0 hq S).sub
      (arrivalInner_measurable rate rewards C_star C_h u t control0 hq)
  exact hinner.indicator
    (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)

theorem measurable_roundedRewardGap (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (roundedRewardGap rate rewards C_star C_h u t hq S) :=
  (rewardGapInner_measurable rate rewards C_star C_h u t control0 hq S).indicator
    (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)

private theorem arrivalInner_bounds (hq : t.val + 1 < p.T) (z : Z) :
    0 ≤ (∑ j : Fin p.K, θ z j * a hq j z) ∧
      (∑ j : Fin p.K, θ z j * a hq j z) ≤
        (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (preTheta_bounds rate rewards C_star C_h u t j z).1
      (nextScalar_nonneg rate rewards C_star C_h u t hq j z)
  · calc
      (∑ j : Fin p.K, θ z j * a hq j z) ≤
          ∑ j : Fin p.K, (1 : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
        apply Finset.sum_le_sum
        intro j hj
        have hθ := (preTheta_bounds rate rewards C_star C_h u t j z).2
        have ha := nextScalar_le_invBeta rate rewards C_star C_h u t hq j z
        have ha0 := nextScalar_nonneg rate rewards C_star C_h u t hq j z
        nlinarith
      _ = (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
        simp [div_eq_mul_inv, Finset.sum_const, Finset.card_univ]

private theorem selectedArrival_bounds (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    0 ≤ (∑ j ∈ S.1, a hq j z) ∧
      (∑ j ∈ S.1, a hq j z) ≤
        (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact nextScalar_nonneg rate rewards C_star C_h u t hq j z
  · calc
      (∑ j ∈ S.1, a hq j z) ≤
          ∑ j ∈ S.1, (1 : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
        apply Finset.sum_le_sum
        intro j hj
        exact nextScalar_le_invBeta rate rewards C_star C_h u t hq j z
      _ = (S.1.card : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
        simp [div_eq_mul_inv, Finset.sum_const]
      _ ≤ (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
        have hcard : (S.1.card : ℝ) ≤ (p.K : ℝ) := by
          have hcardNat : S.1.card ≤ p.K := by
            simpa using Finset.card_le_univ S.1
          exact_mod_cast hcardNat
        exact div_le_div_of_nonneg_right hcard
          (CanonicalRecordingRates.beta_pos p rate.eta.property).le

private theorem rewardAt_bounds (hq : t.val + 1 < p.T) (j : Fin p.K) :
    0 ≤ r hq j ∧ r hq j ≤ 1 := by
  have hD : 0 < (D p : ℝ) := by exact_mod_cast D_pos p
  have hv0 : (0 : ℝ) ≤ (rewards ⟨t.val + 1, hq⟩ j).val :=
    Nat.cast_nonneg _
  have hvD : ((rewards ⟨t.val + 1, hq⟩ j).val : ℝ) ≤ (D p : ℝ) := by
    have hn : (rewards ⟨t.val + 1, hq⟩ j).val ≤ D p :=
      Nat.le_of_lt_succ (rewards ⟨t.val + 1, hq⟩ j).isLt
    exact_mod_cast hn
  constructor
  · exact div_nonneg hv0 hD.le
  · change ((rewards ⟨t.val + 1, hq⟩ j).val : ℝ) / (D p : ℝ) ≤ 1
    exact (div_le_iff₀ hD).2 (by simpa using hvD)

private theorem rewardGapInner_bounds (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    |(∑ j ∈ S.1, r hq j) - ∑ j : Fin p.K, θ z j * r hq j| ≤ (p.m : ℝ) := by
  have hr (j : Fin p.K) :=
    rewardAt_bounds rewards t hq j
  have hsumS0 : 0 ≤ ∑ j ∈ S.1, r hq j := by
    apply Finset.sum_nonneg
    intro j hj
    exact (hr j).1
  have hsumSm : (∑ j ∈ S.1, r hq j) ≤ (p.m : ℝ) := by
    have hcard : S.1.card = p.m :=
      (Finset.mem_powersetCard.mp S.2).2
    calc
      (∑ j ∈ S.1, r hq j) ≤ ∑ j ∈ S.1, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hr j).2
      _ = (p.m : ℝ) := by simp [hcard]
  have hsumθ0 : 0 ≤ ∑ j : Fin p.K, θ z j * r hq j := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (preTheta_bounds rate rewards C_star C_h u t j z).1 (hr j).1
  have hsumθm : (∑ j : Fin p.K, θ z j * r hq j) ≤ (p.m : ℝ) := by
    calc
      (∑ j : Fin p.K, θ z j * r hq j) ≤ ∑ j : Fin p.K, θ z j := by
        apply Finset.sum_le_sum
        intro j hj
        nlinarith [preTheta_bounds rate rewards C_star C_h u t j z, hr j]
      _ = (p.m : ℝ) :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta_sum
          rate rewards C_star C_h u t z
  rw [abs_le]
  constructor <;> nlinarith

theorem integrable_arrivalObservation (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    Integrable (arrivalObservation rate rewards C_star C_h u t hq) ν := by
  apply integrable_of_measurable_norm_le_const
    rate rewards C_star C_h u t
    (measurable_arrivalObservation rate rewards C_star C_h u t control0 hq)
    ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val)
  intro z
  rw [Real.norm_eq_abs]
  by_cases hz : z ∈ G hq
  · simp [arrivalObservation, hz, abs_of_nonneg
      (arrivalInner_bounds rate rewards C_star C_h u t hq z).1]
    exact (arrivalInner_bounds rate rewards C_star C_h u t hq z).2
  · simp [arrivalObservation, hz]
    positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]

theorem integrable_comparatorObservation (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (comparatorObservation rate rewards C_star C_h u t hq S) ν := by
  apply integrable_of_measurable_norm_le_const
    rate rewards C_star C_h u t
    (measurable_comparatorObservation rate rewards C_star C_h u t control0 hq S)
    (2 * ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val))
  intro z
  rw [Real.norm_eq_abs]
  by_cases hz : z ∈ G hq
  · simp only [comparatorObservation, Set.indicator_of_mem hz]
    have hs := selectedArrival_bounds rate rewards C_star C_h u t hq S z
    have ha := arrivalInner_bounds rate rewards C_star C_h u t hq z
    calc
      |(∑ j ∈ S.1, a hq j z) -
          ∑ j : Fin p.K, θ z j * a hq j z| ≤
        |∑ j ∈ S.1, a hq j z| +
          |∑ j : Fin p.K, θ z j * a hq j z| :=
          abs_sub _ _
      _ ≤ (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val +
          (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
            rw [abs_of_nonneg hs.1, abs_of_nonneg ha.1]
            nlinarith
      _ = 2 * ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val) := by
        ring
  · simp [comparatorObservation, hz]
    positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]

theorem integrable_roundedRewardGap (control0 : TimeControl p)
    (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (roundedRewardGap rate rewards C_star C_h u t hq S) ν := by
  apply integrable_of_measurable_norm_le_const
    rate rewards C_star C_h u t
    (measurable_roundedRewardGap rate rewards C_star C_h u t control0 hq S)
    (p.m : ℝ)
  intro z
  rw [Real.norm_eq_abs]
  by_cases hz : z ∈ G hq
  · simp only [roundedRewardGap, Set.indicator_of_mem hz]
    exact rewardGapInner_bounds rate rewards C_star C_h u t hq S z
  · simp [roundedRewardGap, hz]

private theorem integrable_gatedThetaScalar (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (j : Fin p.K) :
    Integrable (gatedThetaScalar rate rewards C_star C_h u t hq j) ν := by
  have hθ : Measurable[
      ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] (θ · j) :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurable_preTheta
      rate rewards C_star C_h u t control0 j
  have hgate := hθ.indicator
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
      rate rewards C_star C_h u t control0 hq)
  have hgate' := hgate.mono
    (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl
  have hmeas : Measurable (gatedThetaScalar rate rewards C_star C_h u t hq j) :=
    hgate'.mul (nextScalar_measurable rate rewards C_star C_h u t control0 hq j)
  have hbound (z : Z) :
      ‖gatedThetaScalar rate rewards C_star C_h u t hq j z‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    by_cases hz : z ∈ G hq
    · rw [gatedThetaScalar, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg
          (preTheta_bounds rate rewards C_star C_h u t j z).1
          (nextScalar_nonneg rate rewards C_star C_h u t hq j z))]
      calc
        θ z j * a hq j z ≤ 1 * a hq j z :=
          mul_le_mul_of_nonneg_right
            (preTheta_bounds rate rewards C_star C_h u t j z).2
            (nextScalar_nonneg rate rewards C_star C_h u t hq j z)
        _ = a hq j z := one_mul _
        _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
          nextScalar_le_invBeta rate rewards C_star C_h u t hq j z
    · simp [gatedThetaScalar, hz]
      positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]
  exact integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    hmeas (1 / CanonicalRecordingRates.beta p rate.eta.val) hbound

private theorem integrable_gatedScalar (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (j : Fin p.K) :
    Integrable (gatedScalar rate rewards C_star C_h u t hq j) ν := by
  have hgate : Measurable[
      ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0]
      ((G hq).indicator (fun _ : Z => (1 : ℝ))) :=
    measurable_const.indicator
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
        rate rewards C_star C_h u t control0 hq)
  have hgate' := hgate.mono
    (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl
  have hmeas : Measurable (gatedScalar rate rewards C_star C_h u t hq j) :=
    hgate'.mul (nextScalar_measurable rate rewards C_star C_h u t control0 hq j)
  have hbound (z : Z) :
      ‖gatedScalar rate rewards C_star C_h u t hq j z‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    by_cases hz : z ∈ G hq
    · rw [gatedScalar, Set.indicator_of_mem hz, one_mul, Real.norm_eq_abs,
        abs_of_nonneg (nextScalar_nonneg rate rewards C_star C_h u t hq j z)]
      exact nextScalar_le_invBeta rate rewards C_star C_h u t hq j z
    · simp [gatedScalar, hz]
      positivity [CanonicalRecordingRates.beta_pos p rate.eta.property]
  exact integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    hmeas (1 / CanonicalRecordingRates.beta p rate.eta.val) hbound

private theorem condExp_gatedThetaScalar
    (hq : t.val + 1 < p.T) (j : Fin p.K) :
    ν[(gatedThetaScalar rate rewards C_star C_h u t hq j) | Fq] =ᵐ[ν]
      fun z => (G hq).indicator (fun z => θ z j) z * m₁ hq j z := by
  have hθ : Measurable[Fq] (θ · j) :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurable_preTheta
      rate rewards C_star C_h u t control0 j
  let f : Z → ℝ := (G hq).indicator (fun z => θ z j)
  have hf : Measurable[Fq] f := hθ.indicator
    (retained_measurable rate rewards C_star C_h u t control0 hq)
  have hpull := condExp_mul_of_stronglyMeasurable_left hf.stronglyMeasurable
    (integrable_gatedThetaScalar rate rewards C_star C_h u t control0 hq j)
    (ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_integrable
      rate rewards C_star C_h u t control0 hq j)
  have hscalar := ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_condExp
    rate rewards C_star C_h u t control0 hq j
  change ν[(fun z => f z * a hq j z) | Fq] =ᵐ[ν]
    fun z => f z * m₁ hq j z
  calc
    _ =ᵐ[ν] fun z => f z * ν[(a hq j) | Fq] z := hpull
    _ =ᵐ[ν] fun z => f z * m₁ hq j z := by
      filter_upwards [hscalar] with z hz
      exact congrArg (fun x : ℝ => f z * x) hz

private theorem condExp_gatedScalar
    (hq : t.val + 1 < p.T) (j : Fin p.K) :
    ν[(gatedScalar rate rewards C_star C_h u t hq j) | Fq] =ᵐ[ν]
      fun z => (G hq).indicator (fun _ : Z => (1 : ℝ)) z * m₁ hq j z := by
  have hf : Measurable[Fq]
      ((G hq).indicator (fun _ : Z => (1 : ℝ))) :=
    measurable_const.indicator
      (retained_measurable rate rewards C_star C_h u t control0 hq)
  have hpull := condExp_mul_of_stronglyMeasurable_left hf.stronglyMeasurable
    (integrable_gatedScalar rate rewards C_star C_h u t control0 hq j)
    (ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_integrable
      rate rewards C_star C_h u t control0 hq j)
  have hscalar := ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_condExp
    rate rewards C_star C_h u t control0 hq j
  change ν[(fun z => (G hq).indicator (fun _ : Z => (1 : ℝ)) z *
      a hq j z) | Fq] =ᵐ[ν]
    fun z => (G hq).indicator (fun _ : Z => (1 : ℝ)) z * m₁ hq j z
  calc
    _ =ᵐ[ν] fun z =>
        (G hq).indicator (fun _ : Z => (1 : ℝ)) z * ν[(a hq j) | Fq] z := hpull
    _ =ᵐ[ν] fun z =>
        (G hq).indicator (fun _ : Z => (1 : ℝ)) z * m₁ hq j z := by
      filter_upwards [hscalar] with z hz
      exact congrArg
        (fun x : ℝ => (G hq).indicator (fun _ : Z => (1 : ℝ)) z * x) hz

private theorem arrivalObservation_sum_gatedThetaScalar
    (hq : t.val + 1 < p.T) :
    arrivalObservation rate rewards C_star C_h u t hq =
      fun z => ∑ j : Fin p.K, gatedThetaScalar rate rewards C_star C_h u t hq j z := by
  funext z
  by_cases hz : z ∈ G hq
  · simp [arrivalObservation, gatedThetaScalar, hz]
  · simp [arrivalObservation, gatedThetaScalar, hz]

theorem arrivalObservation_condExp_eq (hq : t.val + 1 < p.T) :
    ν[(arrivalObservation rate rewards C_star C_h u t hq) | Fq] =ᵐ[ν]
      fun z => (G hq).indicator
        (fun z => ∑ j : Fin p.K, θ z j * m₁ hq j z) z := by
  have hdecomp := arrivalObservation_sum_gatedThetaScalar
    rate rewards C_star C_h u t hq
  have hterms := condExp_finsetSum
    (μ := ν) (s := Finset.univ)
    (f := fun j z => gatedThetaScalar rate rewards C_star C_h u t hq j z)
    (fun j hj => integrable_gatedThetaScalar
      rate rewards C_star C_h u t control0 hq j) Fq
  have hsumIntegrable :
      Integrable (fun z => ∑ j : Fin p.K,
        gatedThetaScalar rate rewards C_star C_h u t hq j z) ν :=
    (integrable_arrivalObservation rate rewards C_star C_h u t control0 hq).congr
      (Filter.Eventually.of_forall (fun z => congrFun hdecomp z))
  have htermEq : ∀ j : Fin p.K,
      ν[(gatedThetaScalar rate rewards C_star C_h u t hq j) | Fq] =ᵐ[ν]
        fun z => (G hq).indicator (fun z => θ z j) z * m₁ hq j z :=
    fun j => condExp_gatedThetaScalar rate rewards C_star C_h u t control0 hq j
  have hterms' :
      ν[(fun z => ∑ j : Fin p.K,
        gatedThetaScalar rate rewards C_star C_h u t hq j z) | Fq] =ᵐ[ν]
      fun z => ∑ j : Fin p.K,
        ν[(gatedThetaScalar rate rewards C_star C_h u t hq j) | Fq] z := by
    simpa only [Finset.sum_fn] using hterms
  have hsumEq :
      (fun z => ∑ j : Fin p.K,
        ν[(gatedThetaScalar rate rewards C_star C_h u t hq j) | Fq] z) =ᵐ[ν]
      fun z => (G hq).indicator
        (fun z => ∑ j : Fin p.K, θ z j * m₁ hq j z) z := by
    filter_upwards [ae_all_iff.2 htermEq] with z hz
    by_cases hg : z ∈ G hq
    · simp [hg, fun j => hz j]
    · simp [hg, fun j => hz j]
  calc
    _ =ᵐ[ν] ν[(fun z => ∑ j : Fin p.K,
        gatedThetaScalar rate rewards C_star C_h u t hq j z) | Fq] :=
      condExp_congr_ae
        (Filter.Eventually.of_forall (fun z => congrFun hdecomp z))
    _ =ᵐ[ν] fun z => ∑ j : Fin p.K,
        ν[(gatedThetaScalar rate rewards C_star C_h u t hq j) | Fq] z := hterms'
    _ =ᵐ[ν] fun z => (G hq).indicator
        (fun z => ∑ j : Fin p.K, θ z j * m₁ hq j z) z := hsumEq

theorem conditionalObservations_measurable (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (ν[(arrivalObservation rate rewards C_star C_h u t hq) | Fq]) ∧
      Measurable (ν[(comparatorObservation rate rewards C_star C_h u t hq S) | Fq]) ∧
      Measurable (ν[(roundedRewardGap rate rewards C_star C_h u t hq S) | Fq]) := by
  have hfield :=
    ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0
  refine ⟨(stronglyMeasurable_condExp (μ := ν) (m := Fq)
      (f := arrivalObservation rate rewards C_star C_h u t hq)).measurable.mono hfield le_rfl,
    (stronglyMeasurable_condExp (μ := ν) (m := Fq)
      (f := comparatorObservation rate rewards C_star C_h u t hq S)).measurable.mono hfield le_rfl,
    (stronglyMeasurable_condExp (μ := ν) (m := Fq)
      (f := roundedRewardGap rate rewards C_star C_h u t hq S)).measurable.mono hfield le_rfl⟩

theorem conditionalObservations_integrable (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (ν[(arrivalObservation rate rewards C_star C_h u t hq) | Fq]) ν ∧
      Integrable (ν[(comparatorObservation rate rewards C_star C_h u t hq S) | Fq]) ν ∧
      Integrable (ν[(roundedRewardGap rate rewards C_star C_h u t hq S) | Fq]) ν :=
  ⟨integrable_condExp, integrable_condExp, integrable_condExp⟩

private theorem arrivalMomentInner_bounds_of_retained
    (hq : t.val + 1 < p.T) (z : Z) (hz : z ∈ G hq) :
    0 ≤ (∑ j : Fin p.K, θ z j * m₁ hq j z) ∧
      (∑ j : Fin p.K, θ z j * m₁ hq j z) ≤ (p.m : ℝ) := by
  rcases retained_nextCell_data rate rewards C_star C_h u t hq z hz with
    ⟨c, xi, hc, hp, hEnabled, hRate, hoverflow⟩
  have hxi :=
    ReferenceFirstCollectionRenewalNextRecordingLaw.nextParameters_bounds
      rate rewards C_star C_h u t z hq true xi hp
  have hmom (j : Fin p.K) :=
    ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne_retained_bounds
      rate rewards C_star C_h u t hq j z xi hp hoverflow
  constructor
  · apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (preTheta_bounds rate rewards C_star C_h u t j z).1
      (ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne_nonneg
        rate rewards C_star C_h u t hq j z)
  · calc
      (∑ j : Fin p.K, θ z j * m₁ hq j z) ≤ ∑ j : Fin p.K, θ z j := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left
            ((hmom j).2.1.trans (hmom j).2.2)
            (preTheta_bounds rate rewards C_star C_h u t j z).1)
      _ = (p.m : ℝ) :=
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta_sum
          rate rewards C_star C_h u t z

private def gatedSelectedSum (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) : ℝ :=
  ∑ j ∈ S.1, gatedScalar rate rewards C_star C_h u t hq j z

private theorem integrable_gatedSelectedSum (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (gatedSelectedSum rate rewards C_star C_h u t hq S) ν := by
  exact integrable_finsetSum S.1 fun j hj =>
    integrable_gatedScalar rate rewards C_star C_h u t control0 hq j

private theorem gatedSelectedSum_condExp_eq (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ν[(gatedSelectedSum rate rewards C_star C_h u t hq S) | Fq] =ᵐ[ν]
      fun z => (G hq).indicator (fun z => ∑ j ∈ S.1, m₁ hq j z) z := by
  have hsum := condExp_finsetSum (μ := ν) (s := S.1)
    (f := fun j z => gatedScalar rate rewards C_star C_h u t hq j z)
    (fun j hj => integrable_gatedScalar
      rate rewards C_star C_h u t control0 hq j) Fq
  have harg : gatedSelectedSum rate rewards C_star C_h u t hq S =
      ∑ j ∈ S.1, (fun z => gatedScalar rate rewards C_star C_h u t hq j z) := by
    funext z
    simp [gatedSelectedSum, Finset.sum_apply]
  have hsumArg :
      ν[gatedSelectedSum rate rewards C_star C_h u t hq S | Fq] =ᵐ[ν]
        ν[∑ j ∈ S.1,
          (fun z => gatedScalar rate rewards C_star C_h u t hq j z) | Fq] :=
    condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun harg z)
  have hterms : ∀ᵐ z ∂ν, ∀ j ∈ S.1,
      ν[gatedScalar rate rewards C_star C_h u t hq j | Fq] z =
        (G hq).indicator (fun _ : Z => (1 : ℝ)) z * m₁ hq j z := by
    apply S.1.eventually_all.mpr
    intro j hj
    exact condExp_gatedScalar rate rewards C_star C_h u t control0 hq j
  have hce : ν[gatedSelectedSum rate rewards C_star C_h u t hq S | Fq] =ᵐ[ν]
      fun z => (G hq).indicator (fun z => ∑ j ∈ S.1, m₁ hq j z) z := by
    have hsum' := hsumArg.trans hsum
    filter_upwards [hsum', hterms] with z hz htermsz
    simp only [Finset.sum_apply] at hz
    rw [hz]
    by_cases hg : z ∈ G hq
    · calc
        (∑ j ∈ S.1, ν[gatedScalar rate rewards C_star C_h u t hq j | Fq] z) =
            ∑ j ∈ S.1, m₁ hq j z := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [htermsz j hj]
              simp [hg]
        _ = (G hq).indicator (fun z => ∑ j ∈ S.1, m₁ hq j z) z := by
          simp [hg]
    · calc
        (∑ j ∈ S.1, ν[gatedScalar rate rewards C_star C_h u t hq j | Fq] z) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            rw [htermsz j hj]
            simp [hg]
        _ = (G hq).indicator (fun z => ∑ j ∈ S.1, m₁ hq j z) z := by
          simp [hg]
  exact hce

theorem comparatorObservation_condExp_eq (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ν[(comparatorObservation rate rewards C_star C_h u t hq S) | Fq] =ᵐ[ν]
      fun z => (G hq).indicator
        (fun z => (∑ j ∈ S.1, m₁ hq j z) -
          ∑ j : Fin p.K, θ z j * m₁ hq j z) z := by
  have hdecomp : comparatorObservation rate rewards C_star C_h u t hq S =
      fun z => gatedSelectedSum rate rewards C_star C_h u t hq S z -
        arrivalObservation rate rewards C_star C_h u t hq z := by
    funext z
    by_cases hg : z ∈ G hq
    · simp [comparatorObservation, arrivalObservation, gatedSelectedSum,
        gatedScalar, hg]
    · simp [comparatorObservation, arrivalObservation, gatedSelectedSum,
        gatedScalar, hg]
  have hleftInt := integrable_gatedSelectedSum
    rate rewards C_star C_h u t control0 hq S
  have hrightInt := integrable_arrivalObservation
    rate rewards C_star C_h u t control0 hq
  have hsub := condExp_sub hleftInt hrightInt Fq
  have hleftCE := gatedSelectedSum_condExp_eq
    rate rewards C_star C_h u t control0 hq S
  have hrightCE := arrivalObservation_condExp_eq
    rate rewards C_star C_h u t control0 hq
  have hdecompCE := condExp_congr_ae (μ := ν) (m := Fq)
    (Filter.Eventually.of_forall fun z => congrFun hdecomp z)
  filter_upwards [hdecompCE, hsub, hleftCE, hrightCE] with z hdecompz hsubz hleftz hrightz
  calc
    ν[comparatorObservation rate rewards C_star C_h u t hq S | Fq] z =
        ν[(fun z => gatedSelectedSum rate rewards C_star C_h u t hq S z -
          arrivalObservation rate rewards C_star C_h u t hq z) | Fq] z := hdecompz
    _ = ν[gatedSelectedSum rate rewards C_star C_h u t hq S | Fq] z -
        ν[arrivalObservation rate rewards C_star C_h u t hq | Fq] z := hsubz
    _ = (G hq).indicator
        (fun z => (∑ j ∈ S.1, m₁ hq j z) -
          ∑ j : Fin p.K, θ z j * m₁ hq j z) z := by
      by_cases hg : z ∈ G hq
      · simp only [Set.indicator_of_mem hg] at hleftz hrightz
        rw [hleftz, hrightz]
        simp [hg]
      · simp [hg] at hleftz hrightz
        rw [hleftz, hrightz]
        simp [hg]

private theorem retainedRoundedBias_bound
    (hq : t.val + 1 < p.T) (S : ProductSetLaw.ProductSet p.K p.m)
    (z : Z) (hz : z ∈ G hq) :
    (∑ j ∈ S.1, r hq j) - ∑ j : Fin p.K, θ z j * r hq j ≤
      (∑ j ∈ S.1, m₁ hq j z) -
        ∑ j : Fin p.K, θ z j * m₁ hq j z +
        (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ)) := by
  rcases retained_nextCell_data rate rewards C_star C_h u t hq z hz with
    ⟨c, xi, hc, hp, hEnabled, hRate, hoverflow⟩
  have hxi := ReferenceFirstCollectionRenewalNextRecordingLaw.nextParameters_bounds
    rate rewards C_star C_h u t z hq true xi hp
  have hmom (j : Fin p.K) :=
    ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne_retained_bounds
      rate rewards C_star C_h u t hq j z xi hp hoverflow
  have hxi_le_one (j : Fin p.K) : xi j ≤ 1 :=
    (Finset.single_le_sum (fun k _ => hxi.1 k) (Finset.mem_univ j)).trans hxi.2
  have hsumXi : (∑ j ∈ S.1, xi j) ≤ (p.m : ℝ) := by
    calc
      (∑ j ∈ S.1, xi j) ≤ ∑ j ∈ S.1, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hxi_le_one j
      _ = (p.m : ℝ) := by
        simp [(Finset.mem_powersetCard.mp S.2).2]
  have hden : 0 < rate.eta.val * (D p : ℝ) :=
    mul_pos rate.eta.property (by exact_mod_cast D_pos p)
  have hfloor :
      (∑ j ∈ S.1, (r hq j - m₁ hq j z)) ≤
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
    calc
      (∑ j ∈ S.1, (r hq j - m₁ hq j z)) ≤
          ∑ j ∈ S.1, xi j / (rate.eta.val * (D p : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have hround : r hq j - xi j /
            (rate.eta.val * (D p : ℝ)) ≤ m₁ hq j z := by
          simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using (hmom j).1
        linarith
      _ = (∑ j ∈ S.1, xi j) / (rate.eta.val * (D p : ℝ)) := by
        rw [Finset.sum_div]
      _ ≤ (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) :=
        div_le_div_of_nonneg_right hsumXi hden.le
  have htheta :
      0 ≤ (∑ j : Fin p.K, θ z j * (r hq j - m₁ hq j z)) := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (preTheta_bounds rate rewards C_star C_h u t j z).1
      (by linarith [(hmom j).2.1])
  have halgebra :
      (∑ j ∈ S.1, r hq j) - ∑ j : Fin p.K, θ z j * r hq j =
        ((∑ j ∈ S.1, m₁ hq j z) -
          ∑ j : Fin p.K, θ z j * m₁ hq j z) +
          (∑ j ∈ S.1, (r hq j - m₁ hq j z)) -
            ∑ j : Fin p.K, θ z j * (r hq j - m₁ hq j z) := by
    have hS : (∑ j ∈ S.1, (r hq j - m₁ hq j z)) =
        (∑ j ∈ S.1, r hq j) - (∑ j ∈ S.1, m₁ hq j z) := by
      rw [Finset.sum_sub_distrib]
    have hT : (∑ j : Fin p.K, θ z j * (r hq j - m₁ hq j z)) =
        (∑ j : Fin p.K, θ z j * r hq j) -
          (∑ j : Fin p.K, θ z j * m₁ hq j z) := by
      calc
        (∑ j : Fin p.K, θ z j * (r hq j - m₁ hq j z)) =
            ∑ j : Fin p.K, (θ z j * r hq j - θ z j * m₁ hq j z) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
        _ = (∑ j : Fin p.K, θ z j * r hq j) -
            (∑ j : Fin p.K, θ z j * m₁ hq j z) := by
              rw [← Finset.sum_sub_distrib]
    rw [hS, hT]
    ring
  rw [halgebra]
  linarith

theorem roundedRewardGap_le_condExp_add_floor (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    roundedRewardGap rate rewards C_star C_h u t hq S ≤ᵐ[ν]
      (ν[(comparatorObservation rate rewards C_star C_h u t hq S) | Fq]) +
        (G hq).indicator
          (fun _ : Z => (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) := by
  have hce := comparatorObservation_condExp_eq
    rate rewards C_star C_h u t control0 hq S
  filter_upwards [hce] with z hcez
  by_cases hz : z ∈ G hq
  · change roundedRewardGap rate rewards C_star C_h u t hq S z ≤
      ν[(comparatorObservation rate rewards C_star C_h u t hq S) | Fq] z +
        (G hq).indicator
          (fun _ : Z => (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) z
    rw [hcez]
    simp only [roundedRewardGap, Set.indicator_of_mem hz,
      Set.indicator_of_mem hz]
    exact retainedRoundedBias_bound rate rewards C_star C_h u t hq S z hz
  · simp [roundedRewardGap, hz, hcez]

theorem integral_roundedRewardGap_le_comparator_add_floor
    (control0 : TimeControl p) (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, roundedRewardGap rate rewards C_star C_h u t hq S z ∂ν) ≤
      (∫ z, comparatorObservation rate rewards C_star C_h u t hq S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (G hq) := by
  let field := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
  let cexp := ν[(comparatorObservation rate rewards C_star C_h u t hq S) | field]
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hrounded := integrable_roundedRewardGap
    rate rewards C_star C_h u t control0 hq S
  have hcomp := integrable_comparatorObservation
    rate rewards C_star C_h u t control0 hq S
  have hce : Integrable cexp ν := integrable_condExp
  have hceTotal := integral_condExp (μ := ν) (m := field)
    (f := comparatorObservation rate rewards C_star C_h u t hq S) hfield
  have hgate : Integrable
      ((G hq).indicator (fun _ : Z =>
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ)))) ν :=
    (integrable_const ((p.m : ℝ) / (rate.eta.val * (D p : ℝ)))).indicator
      (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)
  have hbound := roundedRewardGap_le_condExp_add_floor
    rate rewards C_star C_h u t control0 hq S
  have hmono := integral_mono_ae hrounded (hce.add hgate) hbound
  have hgateIntegral :
      (∫ z, (G hq).indicator (fun _ : Z =>
        (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) z ∂ν) =
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (G hq) := by
    rw [integral_indicator_const, smul_eq_mul, mul_comm]
    exact retained_measurable_ambient rate rewards C_star C_h u t control0 hq
  calc
    (∫ z, roundedRewardGap rate rewards C_star C_h u t hq S z ∂ν) ≤
        ∫ z, (cexp z + (G hq).indicator (fun _ : Z =>
          (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) z) ∂ν := hmono
    _ = (∫ z, cexp z ∂ν) +
        ∫ z, (G hq).indicator (fun _ : Z =>
          (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) z ∂ν := integral_add hce hgate
    _ = (∫ z, comparatorObservation rate rewards C_star C_h u t hq S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (G hq) := by
      rw [hceTotal, hgateIntegral]

private theorem naturalArrivalObservation_of_date
    (hq : t.val + 1 < p.T) :
    naturalArrivalObservation rate rewards C_star C_h u t =
      arrivalObservation rate rewards C_star C_h u t hq := by
  funext z
  simp [naturalArrivalObservation, hq]

private theorem naturalComparatorObservation_of_date
    (hq : t.val + 1 < p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    naturalComparatorObservation rate rewards C_star C_h u t S =
      comparatorObservation rate rewards C_star C_h u t hq S := by
  funext z
  simp [naturalComparatorObservation, hq]

private theorem naturalRoundedRewardGap_of_date
    (hq : t.val + 1 < p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    naturalRoundedRewardGap rate rewards C_star C_h u t S =
      roundedRewardGap rate rewards C_star C_h u t hq S := by
  funext z
  simp [naturalRoundedRewardGap, hq]

private theorem naturalArrivalObservation_no_date
    (hq : ¬ t.val + 1 < p.T) :
    naturalArrivalObservation rate rewards C_star C_h u t = fun _ => 0 := by
  funext z
  simp [naturalArrivalObservation, hq]

private theorem naturalComparatorObservation_no_date
    (hq : ¬ t.val + 1 < p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    naturalComparatorObservation rate rewards C_star C_h u t S = fun _ => 0 := by
  funext z
  simp [naturalComparatorObservation, hq]

private theorem naturalRoundedRewardGap_no_date
    (hq : ¬ t.val + 1 < p.T) (S : ProductSetLaw.ProductSet p.K p.m) :
    naturalRoundedRewardGap rate rewards C_star C_h u t S = fun _ => 0 := by
  funext z
  simp [naturalRoundedRewardGap, hq]

private theorem naturalRetainedIndicator_of_date
    (hq : t.val + 1 < p.T) :
    naturalRetainedIndicator rate rewards C_star C_h u t =
      (G hq).indicator (fun _ : Z => (1 : ℝ)) := by
  funext z
  simp [naturalRetainedIndicator, hq]

private theorem naturalRetainedIndicator_no_date
    (hq : ¬ t.val + 1 < p.T) :
    naturalRetainedIndicator rate rewards C_star C_h u t = fun _ => 0 := by
  funext z
  simp [naturalRetainedIndicator, hq]

theorem naturalObservations_measurable
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (naturalArrivalObservation rate rewards C_star C_h u t) ∧
      Measurable (naturalComparatorObservation rate rewards C_star C_h u t S) ∧
      Measurable (naturalRoundedRewardGap rate rewards C_star C_h u t S) := by
  by_cases hq : t.val + 1 < p.T
  · rw [naturalArrivalObservation_of_date rate rewards C_star C_h u t hq,
      naturalComparatorObservation_of_date rate rewards C_star C_h u t hq S,
      naturalRoundedRewardGap_of_date rate rewards C_star C_h u t hq S]
    exact ⟨measurable_arrivalObservation rate rewards C_star C_h u t control0 hq,
      measurable_comparatorObservation rate rewards C_star C_h u t control0 hq S,
      measurable_roundedRewardGap rate rewards C_star C_h u t control0 hq S⟩
  · rw [naturalArrivalObservation_no_date rate rewards C_star C_h u t hq,
      naturalComparatorObservation_no_date rate rewards C_star C_h u t hq S,
      naturalRoundedRewardGap_no_date rate rewards C_star C_h u t hq S]
    exact ⟨measurable_const, measurable_const, measurable_const⟩

theorem naturalObservations_integrable
    (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (naturalArrivalObservation rate rewards C_star C_h u t) ν ∧
      Integrable (naturalComparatorObservation rate rewards C_star C_h u t S) ν ∧
      Integrable (naturalRoundedRewardGap rate rewards C_star C_h u t S) ν := by
  by_cases hq : t.val + 1 < p.T
  · rw [naturalArrivalObservation_of_date rate rewards C_star C_h u t hq,
      naturalComparatorObservation_of_date rate rewards C_star C_h u t hq S,
      naturalRoundedRewardGap_of_date rate rewards C_star C_h u t hq S]
    exact ⟨integrable_arrivalObservation rate rewards C_star C_h u t control0 hq,
      integrable_comparatorObservation rate rewards C_star C_h u t control0 hq S,
      integrable_roundedRewardGap rate rewards C_star C_h u t control0 hq S⟩
  · rw [naturalArrivalObservation_no_date rate rewards C_star C_h u t hq,
      naturalComparatorObservation_no_date rate rewards C_star C_h u t hq S,
      naturalRoundedRewardGap_no_date rate rewards C_star C_h u t hq S]
    exact ⟨integrable_const 0, integrable_const 0, integrable_const 0⟩

theorem naturalRetainedIndicator_measurable (control0 : TimeControl p) :
    Measurable (naturalRetainedIndicator rate rewards C_star C_h u t) := by
  by_cases hq : t.val + 1 < p.T
  · rw [naturalRetainedIndicator_of_date rate rewards C_star C_h u t hq]
    exact measurable_const.indicator
      (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)
  · rw [naturalRetainedIndicator_no_date rate rewards C_star C_h u t hq]
    exact measurable_const

theorem naturalRetainedIndicator_integrable (control0 : TimeControl p) :
    Integrable (naturalRetainedIndicator rate rewards C_star C_h u t) ν := by
  by_cases hq : t.val + 1 < p.T
  · rw [naturalRetainedIndicator_of_date rate rewards C_star C_h u t hq]
    exact (integrable_const (1 : ℝ)).indicator
      (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)
  · rw [naturalRetainedIndicator_no_date rate rewards C_star C_h u t hq]
    exact integrable_const 0

theorem naturalObservations_terminal_zero
    (S : ProductSetLaw.ProductSet p.K p.m) (ht : t.val + 1 = p.T) :
    naturalArrivalObservation rate rewards C_star C_h u t = (fun _ => 0) ∧
      naturalComparatorObservation rate rewards C_star C_h u t S = (fun _ => 0) ∧
      naturalRoundedRewardGap rate rewards C_star C_h u t S = (fun _ => 0) := by
  have hnot : ¬ t.val + 1 < p.T := by omega
  rw [naturalArrivalObservation_no_date rate rewards C_star C_h u t hnot,
    naturalComparatorObservation_no_date rate rewards C_star C_h u t hnot S,
    naturalRoundedRewardGap_no_date rate rewards C_star C_h u t hnot S]
  exact ⟨rfl, rfl, rfl⟩

theorem naturalObservations_gated_bounds
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) :
    0 ≤ naturalArrivalObservation rate rewards C_star C_h u t z ∧
      naturalArrivalObservation rate rewards C_star C_h u t z ≤
        ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val) *
          naturalRetainedIndicator rate rewards C_star C_h u t z ∧
      |naturalComparatorObservation rate rewards C_star C_h u t S z| ≤
        (2 * ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val)) *
          naturalRetainedIndicator rate rewards C_star C_h u t z ∧
      |naturalRoundedRewardGap rate rewards C_star C_h u t S z| ≤
        (p.m : ℝ) * naturalRetainedIndicator rate rewards C_star C_h u t z := by
  by_cases hq : t.val + 1 < p.T
  · rw [naturalArrivalObservation_of_date rate rewards C_star C_h u t hq,
      naturalComparatorObservation_of_date rate rewards C_star C_h u t hq S,
      naturalRoundedRewardGap_of_date rate rewards C_star C_h u t hq S,
      naturalRetainedIndicator_of_date rate rewards C_star C_h u t hq]
    by_cases hz : z ∈ G hq
    · have hA := arrivalInner_bounds rate rewards C_star C_h u t hq z
      have hDleft := selectedArrival_bounds rate rewards C_star C_h u t hq S z
      have hDright := arrivalInner_bounds rate rewards C_star C_h u t hq z
      have hL := rewardGapInner_bounds rate rewards C_star C_h u t hq S z
      simp only [arrivalObservation, comparatorObservation, roundedRewardGap,
        Set.indicator_of_mem hz]
      refine ⟨hA.1, ?_, ?_, ?_⟩
      · simpa [mul_one] using hA.2
      · calc
          |(∑ j ∈ S.1, a hq j z) -
              ∑ j : Fin p.K, θ z j * a hq j z| ≤
            |∑ j ∈ S.1, a hq j z| +
              |∑ j : Fin p.K, θ z j * a hq j z| := abs_sub _ _
          _ ≤ (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val +
              (p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val := by
                rw [abs_of_nonneg hDleft.1, abs_of_nonneg hDright.1]
                nlinarith [hDleft.2, hDright.2]
          _ = 2 * ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val) := by ring
          _ = (2 * ((p.K : ℝ) / CanonicalRecordingRates.beta p rate.eta.val)) * 1 := by ring
      · simpa [mul_one] using hL
    · simp only [arrivalObservation, comparatorObservation, roundedRewardGap,
        Set.indicator_of_notMem hz]
      simp [Set.indicator_of_notMem hz, mul_zero, abs_zero]
  · rw [naturalArrivalObservation_no_date rate rewards C_star C_h u t hq,
      naturalComparatorObservation_no_date rate rewards C_star C_h u t hq S,
      naturalRoundedRewardGap_no_date rate rewards C_star C_h u t hq S,
      naturalRetainedIndicator_no_date rate rewards C_star C_h u t hq]
    simp [mul_zero, abs_zero]

theorem currentRegisters_are_original_wholePostReadout (z : Z) :
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.currentRegisters
        rate rewards C_star C_h u t z =
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z).1 :=
  currentRegisters_eq_wholePostReadout rate rewards C_star C_h u t z

theorem actual_nextDate_prefix_is_existing_source_prefix
    (hq : t.val + 1 < p.T) (z : Z) :
    actual_nextDate_physical_prefix rate rewards C_star C_h u t z hq =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.actual_nextDate_physical_prefix
        rate rewards C_star C_h u t z hq := rfl

theorem retained_gate_services_even_if_scalar_zero
    (hq : t.val + 1 < p.T) (z : Z) (hz : z ∈ G hq) (j : Fin p.K)
    (hzero : a hq j z = 0) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq = some c ∧
      c.enabled = true ∧ a hq j z = 0 := by
  rcases retained_nextCell_data rate rewards C_star C_h u t hq z hz with
    ⟨c, xi, hc, hp, henabled, hrate, hoverflow⟩
  exact ⟨c, hc, henabled, hzero⟩

theorem retainedGate_excludes_absent_cell (hq : t.val + 1 < p.T) (z : Z)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = none) :
    z ∉ G hq := by
  intro hz
  rcases (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
      rate rewards C_star C_h u t hq z).1 hz with ⟨⟨xi, hp⟩, _⟩
  simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
    hc] at hp

theorem retainedGate_excludes_disabled_cell (hq : t.val + 1 < p.T) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) (henabled : c.enabled = false) :
    z ∉ G hq := by
  intro hz
  rcases (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
      rate rewards C_star C_h u t hq z).1 hz with ⟨⟨xi, hp⟩, _⟩
  have hpresent := ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
    rate rewards C_star C_h u t hq z c hc
  have hpair : (c.enabled, c.rate) = (true, xi) :=
    Option.some.inj (hpresent.symm.trans hp)
  have hbool := congrArg Prod.fst hpair
  rw [henabled] at hbool
  cases hbool

theorem retainedGate_excludes_prior_overflow (hq : t.val + 1 < p.T) (z : Z)
    (hoverflow : ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
      rate rewards C_star C_h u t z = true) :
    z ∉ G hq := by
  intro hz
  rcases (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep.mem_retainedNextDate_iff
      rate rewards C_star C_h u t hq z).1 hz with ⟨_, hclear⟩
  rw [hoverflow] at hclear
  cases hclear

theorem observations_zero_of_not_retained (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) (hz : z ∉ G hq) :
    arrivalObservation rate rewards C_star C_h u t hq z = 0 ∧
      comparatorObservation rate rewards C_star C_h u t hq S z = 0 ∧
      roundedRewardGap rate rewards C_star C_h u t hq S z = 0 := by
  simp [arrivalObservation, comparatorObservation, roundedRewardGap, hz]

theorem naturalObservations_zero_of_not_retained (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z) (hz : z ∉ G hq) :
    naturalArrivalObservation rate rewards C_star C_h u t z = 0 ∧
      naturalComparatorObservation rate rewards C_star C_h u t S z = 0 ∧
      naturalRoundedRewardGap rate rewards C_star C_h u t S z = 0 := by
  rw [naturalArrivalObservation_of_date rate rewards C_star C_h u t hq,
    naturalComparatorObservation_of_date rate rewards C_star C_h u t hq S,
    naturalRoundedRewardGap_of_date rate rewards C_star C_h u t hq S]
  exact observations_zero_of_not_retained rate rewards C_star C_h u t hq S z hz

theorem naturalObservations_zero_of_absent_cell (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = none) :
    naturalArrivalObservation rate rewards C_star C_h u t z = 0 ∧
      naturalComparatorObservation rate rewards C_star C_h u t S z = 0 ∧
      naturalRoundedRewardGap rate rewards C_star C_h u t S z = 0 :=
  naturalObservations_zero_of_not_retained rate rewards C_star C_h u t hq S z
    (retainedGate_excludes_absent_cell rate rewards C_star C_h u t hq z hc)

theorem naturalObservations_zero_of_disabled_cell (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) (henabled : c.enabled = false) :
    naturalArrivalObservation rate rewards C_star C_h u t z = 0 ∧
      naturalComparatorObservation rate rewards C_star C_h u t S z = 0 ∧
      naturalRoundedRewardGap rate rewards C_star C_h u t S z = 0 :=
  naturalObservations_zero_of_not_retained rate rewards C_star C_h u t hq S z
    (retainedGate_excludes_disabled_cell rate rewards C_star C_h u t hq z c hc henabled)

theorem naturalObservations_zero_of_prior_overflow (hq : t.val + 1 < p.T)
    (S : ProductSetLaw.ProductSet p.K p.m) (z : Z)
    (hoverflow : ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
      rate rewards C_star C_h u t z = true) :
    naturalArrivalObservation rate rewards C_star C_h u t z = 0 ∧
      naturalComparatorObservation rate rewards C_star C_h u t S z = 0 ∧
      naturalRoundedRewardGap rate rewards C_star C_h u t S z = 0 :=
  naturalObservations_zero_of_not_retained rate rewards C_star C_h u t hq S z
    (retainedGate_excludes_prior_overflow rate rewards C_star C_h u t hq z hoverflow)

theorem arrivalObservation_condExp_ae_bounds (hq : t.val + 1 < p.T) :
    ∀ᵐ z ∂ν,
      0 ≤ ν[(arrivalObservation rate rewards C_star C_h u t hq) | Fq] z ∧
      ν[(arrivalObservation rate rewards C_star C_h u t hq) | Fq] z ≤
        (G hq).indicator (fun _ : Z => (p.m : ℝ)) z := by
  have hcond := arrivalObservation_condExp_eq
    rate rewards C_star C_h u t control0 hq
  filter_upwards [hcond] with z hcond
  by_cases hz : z ∈ G hq
  · rw [hcond]
    simpa [hz] using arrivalMomentInner_bounds_of_retained
      rate rewards C_star C_h u t hq z hz
  · rw [hcond]
    simp [hz]

theorem integral_arrivalObservation_condExp_bounds (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    0 ≤ ∫ z, arrivalObservation rate rewards C_star C_h u t hq z ∂ν ∧
      (∫ z, arrivalObservation rate rewards C_star C_h u t hq z ∂ν) ≤
        (p.m : ℝ) * (ν).real (G hq) := by
  let field := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
  let cexp := ν[(arrivalObservation rate rewards C_star C_h u t hq) | field]
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have htotal :=
    integral_condExp (μ := ν) (m := field) (f := arrivalObservation
      rate rewards C_star C_h u t hq) hfield
  have hbounds := arrivalObservation_condExp_ae_bounds
    rate rewards C_star C_h u t control0 hq
  have hceInt : (∫ z, cexp z ∂ν) =
      ∫ z, arrivalObservation rate rewards C_star C_h u t hq z ∂ν := by
    exact htotal
  have hnonneg : ∀ᵐ z ∂ν, 0 ≤ cexp z :=
    hbounds.mono fun z hz => hz.1
  have hupper : ∀ᵐ z ∂ν, cexp z ≤ (G hq).indicator
      (fun _ : Z => (p.m : ℝ)) z :=
    hbounds.mono fun z hz => hz.2
  have hzero : 0 ≤ ∫ z, cexp z ∂ν := by
    have hzInt : Integrable (fun _ : Z => (0 : ℝ)) ν := integrable_const (0 : ℝ)
    have hmono := integral_mono_ae
      hzInt
      integrable_condExp hnonneg
    simpa using hmono
  have hgateInt : Integrable
      ((G hq).indicator (fun _ : Z => (p.m : ℝ))) ν :=
    (integrable_const (p.m : ℝ)).indicator
      (retained_measurable_ambient rate rewards C_star C_h u t control0 hq)
  have hup := integral_mono_ae integrable_condExp hgateInt
    hupper
  have hgateIntegral :
      (∫ z, (G hq).indicator (fun _ : Z => (p.m : ℝ)) z ∂ν) =
        (p.m : ℝ) * (ν).real (G hq) := by
    rw [integral_indicator_const, smul_eq_mul, mul_comm]
    exact retained_measurable_ambient rate rewards C_star C_h u t control0 hq
  constructor
  · rw [← hceInt]
    exact hzero
  · calc
      (∫ z, arrivalObservation rate rewards C_star C_h u t hq z ∂ν) =
          ∫ z, cexp z ∂ν := hceInt.symm
      _ ≤ ∫ z, (G hq).indicator (fun _ : Z => (p.m : ℝ)) z ∂ν := hup
      _ = (p.m : ℝ) * (ν).real (G hq) := hgateIntegral


end Bandits.Support.ReferenceFirstCollectionRenewalNextLearningMoments
