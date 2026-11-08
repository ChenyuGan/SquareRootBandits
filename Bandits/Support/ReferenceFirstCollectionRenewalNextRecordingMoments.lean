/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# First and second moments of the first next renewal recording

This file keeps the original unnormalized renewal source and its exact next
prior field. The scalar is read from the actual optional next numerical cell;
an absent cell contributes zero to this scalar observation.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments

open ReferenceFirstCollectionRenewalNextRecordingLaw
open ReferenceFirstCollectionRenewalNextRecordingPriorView
open ReferenceFirstCollectionRenewalNextPhysicalPrefix
open ReferenceFirstCollectionRenewalSourceCurrentPrefix
open ReferenceFirstCollectionRenewalNextControlLaw

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "Fq" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
  rate rewards C_star C_h u t control0

def rewardAt (hq : t.val + 1 < p.T) (a : Fin p.K) : ℝ :=
  ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)

def priorOverflow (z : Z) : Bool :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout rate rewards C_star C_h u t z).2.1

/-- The actual accepted raw arrival at arm `a` on the first numerical cell
after the renewal call. Absence contributes zero to this scalar test. -/
def nextScalar (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq with
  | none => 0
  | some c => RecordedRoundMoments.rawEstimate Q (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) c a

/-- The retained prior amplitude of the same actual marker. -/
def nextAmplitude (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq with
  | none => 0
  | some (false, _) => 0
  | some (true, xi) =>
      if priorOverflow rate rewards C_star C_h u t z then 0
      else QuantizedRecordingMoments.quantizedValue (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a) (rewardAt rewards t hq a)

/-- Literal first conditional moment, with absence, disabled dates, and the
prior overflow gate handled by the actual optional parameter case. -/
def nextMomentOne (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq with
  | none => 0
  | some (false, _) => 0
  | some (true, xi) =>
      if priorOverflow rate rewards C_star C_h u t z then 0
      else xi a * QuantizedRecordingMoments.quantizedValue (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (xi a) (rewardAt rewards t hq a)

/-- Literal second conditional moment of the same actual scalar arrival. -/
def nextMomentTwo (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq with
  | none => 0
  | some (false, _) => 0
  | some (true, xi) =>
      if priorOverflow rate rewards C_star C_h u t z then 0
      else xi a * (QuantizedRecordingMoments.quantizedValue (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (xi a) (rewardAt rewards t hq a)) ^ 2

def nextArmTest (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  nextTest rate rewards C_star C_h u t (some (some a)) z hq

private theorem measurable_quantizedReward (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (fun xi : Fin p.K → ℝ => QuantizedRecordingMoments.quantizedValue
      (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (xi a) (rewardAt rewards t hq a)) := by
  have hxi : Measurable (fun xi : Fin p.K → ℝ => xi a) := measurable_pi_apply a
  have harg : Measurable (fun xi : Fin p.K → ℝ =>
      (((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta * rewardAt rewards t hq a) / xi a) :=
    (measurable_const : Measurable (fun _ : Fin p.K → ℝ =>
      ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta * rewardAt rewards t hq a)).div hxi
  have hfloor : Measurable (fun xi : Fin p.K → ℝ =>
      Nat.floor ((((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta * rewardAt rewards t hq a) / xi a)) :=
    Nat.measurable_floor.comp harg
  have hcast : Measurable (fun xi : Fin p.K → ℝ =>
      (Nat.floor ((((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta * rewardAt rewards t hq a) / xi a) : ℝ)) :=
    (measurable_of_countable _).comp hfloor
  change Measurable (fun xi : Fin p.K → ℝ =>
    (Nat.floor ((((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) * (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta * rewardAt rewards t hq a) / xi a) : ℝ) /
      ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta * ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ)))
  exact hcast.div_const _

private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

theorem measurable_nextAmplitude (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable[Fq] (nextAmplitude rate rewards C_star C_h u t hq a) := by
  have hp := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_nextParameters rate rewards C_star C_h u t control0 hq
  have ho := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPriorReadout.measurable_wholePostReadout_nextPrior rate rewards C_star C_h u t control0
  have hoverflow : Measurable[Fq] (priorOverflow rate rewards C_star C_h u t) := by
    have hpair := measurable_snd.comp ho
    have hflag := measurable_fst.comp hpair
    change Measurable[Fq]
      (fun z : Z => (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout rate rewards C_star C_h u t z).2.1)
    exact hflag
  have hbranch (b : Bool) : Measurable (fun v : Bool × (Fin p.K → ℝ) =>
      if v.1 then if b then 0 else QuantizedRecordingMoments.quantizedValue (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (v.2 a) (rewardAt rewards t hq a) else 0) := by
    have hbase : Measurable (fun xi : Fin p.K → ℝ => if b then 0 else
        QuantizedRecordingMoments.quantizedValue
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
          (xi a) (rewardAt rewards t hq a)) := by
      cases b with
      | false => simpa using measurable_quantizedReward rate rewards t hq a
      | true => simp
    exact Measurable.ite (measurable_fst (measurableSet_singleton true))
      (hbase.comp measurable_snd) measurable_const
  have hoption (b : Bool) : Measurable (fun o : Option (Bool × (Fin p.K → ℝ)) =>
      o.elim 0 (fun v => if v.1 then if b then 0
        else QuantizedRecordingMoments.quantizedValue (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (v.2 a)
          (rewardAt rewards t hq a) else 0)) :=
    measurable_option_elim _ (hbranch b) 0
  have hpair : Measurable (fun v : Option (Bool × (Fin p.K → ℝ)) × Bool =>
      v.1.elim 0 (fun x => if x.1 then if v.2 then 0
        else QuantizedRecordingMoments.quantizedValue (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta (x.2 a)
          (rewardAt rewards t hq a) else 0)) := by
    refine measurable_from_prod_countable_left ?_
    intro b
    exact hoption b
  have hfun := hpair.comp (hp.prodMk hoverflow)
  have hEq : nextAmplitude rate rewards C_star C_h u t hq a =
      (fun z : Z => (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq).elim 0
        (fun x => if x.1 then if priorOverflow rate rewards C_star C_h u t z then 0
          else QuantizedRecordingMoments.quantizedValue
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
            (x.2 a) (rewardAt rewards t hq a) else 0)) := by
    funext z
    cases hp' : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq with
    | none => simp [nextAmplitude, hp']
    | some pair => cases pair with
      | mk enabled xi => cases enabled <;> simp [nextAmplitude, hp']
  rw [hEq]
  exact hfun

private theorem rewardAt_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) :
    0 ≤ rewardAt rewards t hq a ∧
      rewardAt rewards t hq a ≤ 1 := by
  have hD : 0 < (D p : ℝ) := by exact_mod_cast (D_pos p)
  have hv0 : (0 : ℝ) ≤ (rewards ⟨t.val + 1, hq⟩ a).val := Nat.cast_nonneg _
  have hvD : ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) ≤ (D p : ℝ) := by
    have hn : (rewards ⟨t.val + 1, hq⟩ a).val ≤ D p :=
      Nat.le_of_lt_succ (rewards ⟨t.val + 1, hq⟩ a).isLt
    exact_mod_cast hn
  constructor
  · exact div_nonneg hv0 hD.le
  · exact (div_le_iff₀ hD).2 (by simpa using hvD)

theorem nextParameters_present (hq : t.val + 1 < p.T) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = some c) :
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq = some (c.enabled, c.rate) := by
  simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hc]

theorem nextCell_reward (hq : t.val + 1 < p.T) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = some c) :
    c.reward = rewardAt rewards t hq := by
  have hread := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_readouts rate rewards C_star C_h u t z hq
  have hlive := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_continuing_physical rate rewards C_star C_h u t z hq
  have hcollection := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.next_cutoff_physical rate rewards C_star C_h u t z hq
  dsimp only at hread hlive hcollection
  cases hd : (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRecord rate rewards C_star C_h u t z hq).output.preparation.coordinator
    <;> simp only [hd] at hread hlive hcollection
  all_goals try
    obtain ⟨hL, _hL0, hC, _hC0⟩ := hread
    have hnone : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = none := by
      simp only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, hC, Option.none_or]
    rw [hnone] at hc
    cases hc
  rename_i outcome
  cases outcome <;> simp only at hread hlive hcollection
  all_goals try
    obtain ⟨hL, _hL0, hC, _hC0⟩ := hread
    have hnone : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = none := by
      simp only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, hC, Option.none_or]
    rw [hnone] at hc
    cases hc
  · obtain ⟨c', _payload, _ledger, _started, _weights, _out, hC, hL, _hcall,
      _henabled, _hrate, hreward, _⟩ := hcollection
    have hcell : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = some c' := by
      simp only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, hC, Option.none_or]
    have heq : c' = c := Option.some.inj (hcell.symm.trans hc)
    subst c'
    have hrewards : (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) =
        rewardAt rewards t hq := by
      funext a
      rfl
    exact hreward.trans hrewards

  · obtain ⟨cell, hL, hC, _henabled, hreward, _⟩ := hlive
    have hcell : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq = some cell.input := by
      simp only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell, hL, Option.some_or]
    have heq : cell.input = c := Option.some.inj (hcell.symm.trans hc)
    subst c
    have hrewards : (fun a => ((rewards ⟨t.val + 1, hq⟩ a).val : ℝ) / (D p : ℝ)) =
        rewardAt rewards t hq := by
      funext a
      rfl
    exact hreward.trans hrewards

theorem nextCell_rewardVector (hq : t.val + 1 < p.T) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :
    c.reward = rewardAt rewards t hq :=
  nextCell_reward rate rewards C_star C_h u t hq z c hc

/-- The scalar is exactly the same arm-fiber indicator as the marker law,
multiplied by its prior quantized amplitude and the incoming overflow gate. -/
theorem nextScalar_eq_test_mul_amplitude (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    nextScalar rate rewards C_star C_h u t hq a z =
      nextAmplitude rate rewards C_star C_h u t hq a z *
        nextArmTest rate rewards C_star C_h u t hq a z := by
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq with
  | none =>
      simp [nextScalar, nextAmplitude, nextArmTest, nextTest, nextMarker, hc,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters]
  | some c =>
      have hp := nextParameters_present rate rewards C_star C_h u t hq z c hc
      have hflag := congrArg (fun x => x.2.1)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout rate rewards C_star C_h u t z)
      change (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).overflow =
        priorOverflow rate rewards C_star C_h u t z at hflag
      cases henabled : c.enabled with
      | false =>
          have hz := RecordedRoundMoments.rawEstimate_eq_zero_of_disabled Q
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) c a henabled
          simp [nextScalar, nextAmplitude, nextArmTest, nextTest, nextMarker,
            hc, hp, henabled, hz]
      | true =>
          simp only [henabled] at hp
          cases hflag' : (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z).overflow with
          | true =>
              have hz := RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q
                (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) c a hflag'
              have hoverflow : priorOverflow rate rewards C_star C_h u t z = true := by
                rw [← hflag]
                exact hflag'
              simp [nextScalar, nextAmplitude, nextArmTest, nextTest, nextMarker,
                hc, hp, hoverflow, hz]
          | false =>
              have hnot : priorOverflow rate rewards C_star C_h u t z = false := by
                rw [← hflag]
                exact hflag'
              have hreward := nextCell_reward rate rewards C_star C_h u t hq z c hc
              simp only [nextScalar, hc]
              change RecordedRoundMoments.rawEstimate Q
                (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) c a = _
              rw [RecordedRoundMoments.rawEstimate_eq_normalizedQuantizedArrival_of_enabled
                Q (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState rate rewards C_star C_h u t z) c a henabled hflag']
              by_cases hrec : c.recordedArm = some a
              · rw [RecordedRoundMoments.normalizedQuantizedArrival_eq_quantizedValue_of_recorded
                  Q c a hrec, hreward]
                simp [nextAmplitude, nextArmTest, nextTest, nextMarker,
                  hc, hp, hnot, hrec]
              · have hz : RecordedQueueRun.quantizedArrival Q c a = 0 :=
                  RecordedQueueRun.quantizedArrival_eq_zero Q c a hrec
                simp [RecordedRoundMoments.normalizedQuantizedArrival, hz,
                  nextAmplitude, nextArmTest, nextTest, nextMarker,
                  hc, hp, hnot, hrec]

theorem nextScalar_zero_of_marker_mismatch (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z)
    (hmarker : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextMarker
      rate rewards C_star C_h u t z hq ≠ some (some a)) :
    nextScalar rate rewards C_star C_h u t hq a z = 0 := by
  rw [nextScalar_eq_test_mul_amplitude rate rewards C_star C_h u t hq a z]
  simp [nextArmTest, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextTest,
    hmarker]

theorem nextAmplitude_nonneg (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextAmplitude rate rewards C_star C_h u t hq a z := by
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq with
  | none => simp [nextAmplitude, hp]
  | some pair =>
      cases pair with
      | mk enabled xi =>
          cases enabled with
          | false => simp [nextAmplitude, hp]
          | true =>
              cases hover : priorOverflow rate rewards C_star C_h u t z with
              | true => simp [nextAmplitude, hp, hover]
              | false =>
                  simp only [nextAmplitude, hp, hover, Bool.false_eq_true, ite_false]
                  exact QuantizedRecordingMoments.quantizedValue_nonneg
                    (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D
                    (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
                    (xi a) (rewardAt rewards t hq a) rate.eta.property

private theorem nextAmplitude_le_inv_beta_of_present_enabled (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters rate rewards C_star C_h u t z hq = some (true, xi))
    (hoverflow : priorOverflow rate rewards C_star C_h u t z = false) :
    nextAmplitude rate rewards C_star C_h u t hq a z ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  cases hcell : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell rate rewards C_star C_h u t z hq with
  | none => simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hcell] at hp
  | some c =>
      have hparams := nextParameters_present rate rewards C_star C_h u t hq z c hcell
      have hxi : c.rate = xi := (Prod.mk.inj (Option.some.inj (hparams.symm.trans hp))).2
      have hcanon := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical rate rewards C_star C_h u t z hq
      rw [hcell] at hcanon
      obtain ⟨view, _hview, hrate, hcanonical⟩ := hcanon
      have hbeta : CanonicalRecordingRates.beta p rate.eta.val ≤ xi a := by
        calc
          CanonicalRecordingRates.beta p rate.eta.val ≤
              CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a :=
            CanonicalRecordingRates.beta_le_xi p rate.eta.property view.payload.anchor a
          _ = c.rate a := (hcanonical a).symm
          _ = xi a := congrFun hxi a
      have hbetapos := CanonicalRecordingRates.beta_pos p rate.eta.property
      simp only [nextAmplitude, hp, hoverflow, Bool.false_eq_true, ite_false]
      exact QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta
        (xi a) (rewardAt rewards t hq a)
        (CanonicalRecordingRates.beta p rate.eta.val)
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D_pos (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta_pos (lt_of_lt_of_le hbetapos hbeta)
        (rewardAt_bounds rewards t hq a)
        hbetapos hbeta

/-- The actual next parameter case has a strictly positive canonical rate;
the lower envelope is obtained from the cell's physical rate producer. -/
private theorem nextRate_beta_le (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (true, xi)) :
    CanonicalRecordingRates.beta p rate.eta.val ≤ xi a := by
  cases hcell : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none => simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
      hcell] at hp
  | some c =>
      have hparams := nextParameters_present rate rewards C_star C_h u t hq z c hcell
      have hxi : c.rate = xi := (Prod.mk.inj
        (Option.some.inj (hparams.symm.trans hp))).2
      have hcanonical := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextCell_rate_canonical
        rate rewards C_star C_h u t z hq
      rw [hcell] at hcanonical
      obtain ⟨view, _hview, _hrate, hrateCanonical⟩ := hcanonical
      calc
        CanonicalRecordingRates.beta p rate.eta.val ≤
            CanonicalRecordingRates.xi p rate.eta.val view.payload.anchor a :=
          CanonicalRecordingRates.beta_le_xi p rate.eta.property view.payload.anchor a
        _ = c.rate a := (hrateCanonical a).symm
        _ = xi a := congrFun hxi a

/-- The scalar amplitude is uniformly bounded, with no rate bound added to
the root telescope. Absent, disabled, and overflowed cases contribute zero. -/
theorem nextAmplitude_le_inv_beta (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    nextAmplitude rate rewards C_star C_h u t hq a z ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none =>
      simp [nextAmplitude, hp]
      positivity
  | some pair =>
      cases pair with
      | mk enabled xi =>
          cases enabled with
          | false => simp [nextAmplitude, hp]; positivity
          | true =>
              cases hover : priorOverflow rate rewards C_star C_h u t z with
              | true => simp [nextAmplitude, hp, hover]; positivity
              | false =>
                  exact nextAmplitude_le_inv_beta_of_present_enabled rate rewards C_star C_h u t
                    hq a z xi hp hover

/-- The literal prior coefficient multiplying one numerical arm test. -/
theorem nextMomentOne_eq_amplitude_mul_coefficient (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) :
    nextMomentOne rate rewards C_star C_h u t hq a z =
      nextAmplitude rate rewards C_star C_h u t hq a z *
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient
          rate rewards C_star C_h u t (some (some a)) z hq := by
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none => simp [nextMomentOne, nextAmplitude, nextCoefficient, coefficientOfParameters, hp]
  | some pair =>
      cases pair with
      | mk enabled xi =>
          cases enabled <;> cases hover : priorOverflow rate rewards C_star C_h u t z <;>
            simp [nextMomentOne, nextAmplitude, nextCoefficient, coefficientOfParameters, hp, hover] ; ring

/-- The literal prior coefficient multiplying the square of that same test. -/
theorem nextMomentTwo_eq_amplitude_sq_mul_coefficient (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) :
    nextMomentTwo rate rewards C_star C_h u t hq a z =
      (nextAmplitude rate rewards C_star C_h u t hq a z) ^ 2 *
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient
          rate rewards C_star C_h u t (some (some a)) z hq := by
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none => simp [nextMomentTwo, nextAmplitude, nextCoefficient, coefficientOfParameters, hp]
  | some pair =>
      cases pair with
      | mk enabled xi =>
          cases enabled <;> cases hover : priorOverflow rate rewards C_star C_h u t z <;>
            simp [nextMomentTwo, nextAmplitude, nextCoefficient, coefficientOfParameters, hp, hover] ; ring

theorem measurable_nextMomentOne (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable[Fq] (nextMomentOne rate rewards C_star C_h u t hq a) := by
  have ha := measurable_nextAmplitude rate rewards C_star C_h u t control0 hq a
  have hc := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_nextCoefficient
    rate rewards C_star C_h u t control0 hq (some (some a))
  have heq : nextMomentOne rate rewards C_star C_h u t hq a = fun z =>
      nextAmplitude rate rewards C_star C_h u t hq a z *
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient
          rate rewards C_star C_h u t (some (some a)) z hq := by
    funext z
    exact nextMomentOne_eq_amplitude_mul_coefficient rate rewards C_star C_h u t hq a z
  rw [heq]
  exact ha.mul hc

theorem measurable_nextMomentTwo (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable[Fq] (nextMomentTwo rate rewards C_star C_h u t hq a) := by
  have ha := (measurable_nextAmplitude rate rewards C_star C_h u t control0 hq a).pow_const 2
  have hc := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_nextCoefficient
    rate rewards C_star C_h u t control0 hq (some (some a))
  have heq : nextMomentTwo rate rewards C_star C_h u t hq a = fun z =>
      (nextAmplitude rate rewards C_star C_h u t hq a z) ^ 2 *
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient
          rate rewards C_star C_h u t (some (some a)) z hq := by
    funext z
    exact nextMomentTwo_eq_amplitude_sq_mul_coefficient rate rewards C_star C_h u t hq a z
  rw [heq]
  exact ha.mul hc

theorem nextArmTest_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextArmTest rate rewards C_star C_h u t hq a z ∧
      nextArmTest rate rewards C_star C_h u t hq a z ≤ 1 := by
  unfold nextArmTest nextTest
  split <;> norm_num

theorem nextAmplitude_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextAmplitude rate rewards C_star C_h u t hq a z ∧
      nextAmplitude rate rewards C_star C_h u t hq a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val :=
  ⟨nextAmplitude_nonneg rate rewards C_star C_h u t hq a z,
    nextAmplitude_le_inv_beta rate rewards C_star C_h u t hq a z⟩

theorem nextMomentOne_nonneg (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextMomentOne rate rewards C_star C_h u t hq a z := by
  rw [nextMomentOne_eq_amplitude_mul_coefficient rate rewards C_star C_h u t hq a z]
  exact mul_nonneg (nextAmplitude_nonneg rate rewards C_star C_h u t hq a z)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient_bounds
      rate rewards C_star C_h u t (some (some a)) z hq).1

theorem nextMomentTwo_nonneg (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextMomentTwo rate rewards C_star C_h u t hq a z := by
  rw [nextMomentTwo_eq_amplitude_sq_mul_coefficient rate rewards C_star C_h u t hq a z]
  exact mul_nonneg (sq_nonneg _)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient_bounds
      rate rewards C_star C_h u t (some (some a)) z hq).1

theorem nextScalar_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextScalar rate rewards C_star C_h u t hq a z ∧
      nextScalar rate rewards C_star C_h u t hq a z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  rw [nextScalar_eq_test_mul_amplitude rate rewards C_star C_h u t hq a z]
  have ha := nextAmplitude_bounds rate rewards C_star C_h u t hq a z
  have ht := nextArmTest_bounds rate rewards C_star C_h u t hq a z
  refine ⟨mul_nonneg ha.1 ht.1, ?_⟩
  calc
    nextAmplitude rate rewards C_star C_h u t hq a z *
        nextArmTest rate rewards C_star C_h u t hq a z ≤
      nextAmplitude rate rewards C_star C_h u t hq a z * 1 :=
        mul_le_mul_of_nonneg_left ht.2 ha.1
    _ = nextAmplitude rate rewards C_star C_h u t hq a z := by ring
    _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val := ha.2

theorem nextMomentOne_retained_bounds (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (true, xi))
    (hoverflow : priorOverflow rate rewards C_star C_h u t z = false) :
    rewardAt rewards t hq a - xi a /
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta *
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ)) ≤
        nextMomentOne rate rewards C_star C_h u t hq a z ∧
      nextMomentOne rate rewards C_star C_h u t hq a z ≤ rewardAt rewards t hq a ∧
      rewardAt rewards t hq a ≤ 1 := by
  have hbeta := nextRate_beta_le rate rewards C_star C_h u t hq a z xi hp
  have hbetapos := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi a := lt_of_lt_of_le hbetapos hbeta
  have hr : rewardAt rewards t hq a ∈ Set.Icc (0 : ℝ) 1 := rewardAt_bounds rewards t hq a
  have hround := QuantizedRecordingMoments.quantizedValue_roundingError
    (D p) rate.eta.val (xi a) (rewardAt rewards t hq a) (D_pos p)
    rate.eta.property hxi hr
  have hupper := QuantizedRecordingMoments.quantizedValue_firstMoment_le
    (D p) rate.eta.val (xi a) (rewardAt rewards t hq a) (D_pos p)
    rate.eta.property hxi hr
  have hQD : (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D = D p := rfl
  have hQeta : (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta = rate.eta.val := rfl
  have hformula : nextMomentOne rate rewards C_star C_h u t hq a z =
      xi a * QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (xi a) (rewardAt rewards t hq a) := by
    simp [nextMomentOne, hp, hoverflow, hQD, hQeta]
  rw [hformula]
  have hround' : rewardAt rewards t hq a - xi a /
      ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta *
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ)) ≤
      xi a * QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (xi a) (rewardAt rewards t hq a) := by
    simpa [hQD, hQeta] using hround
  exact ⟨hround', hupper, hr.2⟩

theorem nextMomentTwo_retained_bounds (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (true, xi))
    (hoverflow : priorOverflow rate rewards C_star C_h u t z = false) :
    0 ≤ nextMomentTwo rate rewards C_star C_h u t hq a z ∧
      nextMomentTwo rate rewards C_star C_h u t hq a z ≤
        (rewardAt rewards t hq a) ^ 2 / xi a ∧
      nextMomentTwo rate rewards C_star C_h u t hq a z ≤ 1 / xi a := by
  have hbeta := nextRate_beta_le rate rewards C_star C_h u t hq a z xi hp
  have hbetapos := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hxi : 0 < xi a := lt_of_lt_of_le hbetapos hbeta
  have hr : rewardAt rewards t hq a ∈ Set.Icc (0 : ℝ) 1 := rewardAt_bounds rewards t hq a
  have hsecond := QuantizedRecordingMoments.quantizedValue_secondMoment_le
    (D p) rate.eta.val (xi a) (rewardAt rewards t hq a) (D_pos p)
    rate.eta.property hxi hr
  have hsq : (rewardAt rewards t hq a) ^ 2 ≤ 1 := by
    nlinarith [hr.1, hr.2]
  have htop : (rewardAt rewards t hq a) ^ 2 / xi a ≤ 1 / xi a :=
    div_le_div_of_nonneg_right hsq hxi.le
  have hQD : (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).D = D p := rfl
  have hQeta : (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).eta = rate.eta.val := rfl
  have hformula : nextMomentTwo rate rewards C_star C_h u t hq a z =
      xi a * (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (xi a) (rewardAt rewards t hq a)) ^ 2 := by
    simp [nextMomentTwo, hp, hoverflow, hQD, hQeta]
  rw [hformula]
  exact ⟨mul_nonneg (le_of_lt hxi)
      (sq_nonneg (QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (xi a) (rewardAt rewards t hq a))), hsecond, hsecond.trans htop⟩

theorem nextMomentTwo_le_inv_beta (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    nextMomentTwo rate rewards C_star C_h u t hq a z ≤
      1 / CanonicalRecordingRates.beta p rate.eta.val := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none => simp [nextMomentTwo, hp]; positivity
  | some pair =>
      cases pair with
      | mk enabled xi =>
          cases enabled with
          | false => simp [nextMomentTwo, hp]; positivity
          | true =>
              cases hover : priorOverflow rate rewards C_star C_h u t z with
              | true => simp [nextMomentTwo, hp, hover]; positivity
              | false =>
                  have hrate := nextRate_beta_le rate rewards C_star C_h u t hq a z xi hp
                  have hbound := nextMomentTwo_retained_bounds rate rewards C_star C_h u t
                    hq a z xi hp hover
                  calc
                    nextMomentTwo rate rewards C_star C_h u t hq a z ≤ 1 / xi a := hbound.2.2
                    _ ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
                      one_div_le_one_div_of_le hbeta hrate

private theorem nextArmTest_values (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    nextArmTest rate rewards C_star C_h u t hq a z = 0 ∨
      nextArmTest rate rewards C_star C_h u t hq a z = 1 := by
  unfold nextArmTest nextTest
  split <;> simp

theorem nextScalar_sq_eq_amplitude_sq_mul_test (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) :
    (nextScalar rate rewards C_star C_h u t hq a z) ^ 2 =
      (nextAmplitude rate rewards C_star C_h u t hq a z) ^ 2 *
        nextArmTest rate rewards C_star C_h u t hq a z := by
  rw [nextScalar_eq_test_mul_amplitude rate rewards C_star C_h u t hq a z]
  rcases nextArmTest_values rate rewards C_star C_h u t hq a z with h | h <;>
    simp [h]

theorem measurable_nextScalar (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (nextScalar rate rewards C_star C_h u t hq a) := by
  have hle := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have ha := (measurable_nextAmplitude rate rewards C_star C_h u t control0 hq a).mono hle le_rfl
  have ht := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.measurable_nextTest
    rate rewards C_star C_h u t hq (some (some a))
  have heq : nextScalar rate rewards C_star C_h u t hq a = fun z =>
      nextAmplitude rate rewards C_star C_h u t hq a z *
        nextArmTest rate rewards C_star C_h u t hq a z := by
    funext z
    exact nextScalar_eq_test_mul_amplitude rate rewards C_star C_h u t hq a z
  rw [heq]
  exact ha.mul ht

theorem measurable_nextScalar_sq (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (fun z => (nextScalar rate rewards C_star C_h u t hq a z) ^ 2) :=
  (measurable_nextScalar rate rewards C_star C_h u t control0 hq a).pow_const 2

private theorem integrable_of_measurable_norm_le_const {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (c : ℝ) (hb : ∀ x, ‖f x‖ ≤ c) : Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem nextScalar_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (nextScalar rate rewards C_star C_h u t hq a) ν := by
  apply integrable_of_measurable_norm_le_const _
    (measurable_nextScalar rate rewards C_star C_h u t control0 hq a)
    (1 / CanonicalRecordingRates.beta p rate.eta.val)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg
    (nextScalar_bounds rate rewards C_star C_h u t hq a z).1]
  exact (nextScalar_bounds rate rewards C_star C_h u t hq a z).2

theorem nextScalar_sq_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (fun z => (nextScalar rate rewards C_star C_h u t hq a z) ^ 2) ν := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbound (z : Z) :
      ‖(nextScalar rate rewards C_star C_h u t hq a z) ^ 2‖ ≤
        (1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hs := nextScalar_bounds rate rewards C_star C_h u t hq a z
    nlinarith
  exact integrable_of_measurable_norm_le_const _
    (measurable_nextScalar_sq rate rewards C_star C_h u t control0 hq a)
    ((1 / CanonicalRecordingRates.beta p rate.eta.val) ^ 2) hbound

theorem nextMomentOne_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (nextMomentOne rate rewards C_star C_h u t hq a) ν := by
  have hmeas := (measurable_nextMomentOne rate rewards C_star C_h u t control0 hq a).mono
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl
  have hbound (z : Z) :
      ‖nextMomentOne rate rewards C_star C_h u t hq a z‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (nextMomentOne_nonneg rate rewards C_star C_h u t hq a z)]
    have hsum := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextCoefficient_bounds
      rate rewards C_star C_h u t (some (some a)) z hq
    have ha := nextAmplitude_bounds rate rewards C_star C_h u t hq a z
    rw [nextMomentOne_eq_amplitude_mul_coefficient rate rewards C_star C_h u t hq a z]
    nlinarith
  exact integrable_of_measurable_norm_le_const _ hmeas
    (1 / CanonicalRecordingRates.beta p rate.eta.val) hbound

theorem nextMomentTwo_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (nextMomentTwo rate rewards C_star C_h u t hq a) ν := by
  have hmeas := (measurable_nextMomentTwo rate rewards C_star C_h u t control0 hq a).mono
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hbound (z : Z) :
      ‖nextMomentTwo rate rewards C_star C_h u t hq a z‖ ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (nextMomentTwo_nonneg rate rewards C_star C_h u t hq a z)]
    exact nextMomentTwo_le_inv_beta rate rewards C_star C_h u t hq a z
  exact integrable_of_measurable_norm_le_const _ hmeas
    (1 / CanonicalRecordingRates.beta p rate.eta.val) hbound

/-- Conditional expectation of the actual scalar arrival on the exact next
prior field. The marker law is multiplied by its bounded, prior-measurable
quantized amplitude under the same unnormalized source measure. -/
theorem nextScalar_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    ν[(fun z => nextScalar rate rewards C_star C_h u t hq a z) |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] =ᵐ[ν]
      fun z => nextMomentOne rate rewards C_star C_h u t hq a z := by
  let amp := nextAmplitude rate rewards C_star C_h u t hq a
  let test := nextArmTest rate rewards C_star C_h u t hq a
  have heq : (fun z => nextScalar rate rewards C_star C_h u t hq a z) =
      fun z => amp z * test z := by
    funext z
    exact nextScalar_eq_test_mul_amplitude rate rewards C_star C_h u t hq a z
  have hamp : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] amp :=
    measurable_nextAmplitude rate rewards C_star C_h u t control0 hq a
  have hprod : Integrable (fun z => amp z * test z) ν :=
    (nextScalar_integrable rate rewards C_star C_h u t control0 hq a).congr
      (Filter.Eventually.of_forall fun z => congrFun heq z)
  have htest := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.integrable_nextTest
    rate rewards C_star C_h u t hq (some (some a))
  have hpull := condExp_mul_of_stronglyMeasurable_left hamp.stronglyMeasurable hprod htest
  have hmarker := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextMarker_condExp
    rate rewards C_star C_h u t control0 hq (some (some a))
  calc
    _ =ᵐ[ν] ν[(fun z => amp z * test z) |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun heq z)
    _ =ᵐ[ν] (fun z => amp z * ν[test |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] z) := hpull
    _ =ᵐ[ν] fun z => nextMomentOne rate rewards C_star C_h u t hq a z := by
      filter_upwards [hmarker] with z hz
      change amp z * ν[(fun w => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextTest
        rate rewards C_star C_h u t (some (some a)) w hq) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
          rate rewards C_star C_h u t control0] z =
        nextMomentOne rate rewards C_star C_h u t hq a z
      rw [hz]
      exact (nextMomentOne_eq_amplitude_mul_coefficient
        rate rewards C_star C_h u t hq a z).symm

/-- Conditional square moment of that same actual scalar arrival, retaining
the same marker and squaring only its prior-measurable amplitude. -/
theorem nextScalar_sq_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    ν[(fun z => (nextScalar rate rewards C_star C_h u t hq a z) ^ 2) |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] =ᵐ[ν]
      fun z => nextMomentTwo rate rewards C_star C_h u t hq a z := by
  let amp := nextAmplitude rate rewards C_star C_h u t hq a
  let test := nextArmTest rate rewards C_star C_h u t hq a
  have heq : (fun z => (nextScalar rate rewards C_star C_h u t hq a z) ^ 2) =
      fun z => (amp z) ^ 2 * test z := by
    funext z
    exact nextScalar_sq_eq_amplitude_sq_mul_test rate rewards C_star C_h u t hq a z
  have hamp : Measurable[_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] amp :=
    measurable_nextAmplitude rate rewards C_star C_h u t control0 hq a
  have hprod : Integrable (fun z => (amp z) ^ 2 * test z) ν :=
    (nextScalar_sq_integrable rate rewards C_star C_h u t control0 hq a).congr
      (Filter.Eventually.of_forall fun z => congrFun heq z)
  have htest := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.integrable_nextTest
    rate rewards C_star C_h u t hq (some (some a))
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (hamp.pow_const 2).stronglyMeasurable hprod htest
  have hmarker := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextMarker_condExp
    rate rewards C_star C_h u t control0 hq (some (some a))
  calc
    _ =ᵐ[ν] ν[(fun z => (amp z) ^ 2 * test z) |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun heq z)
    _ =ᵐ[ν] (fun z => (amp z) ^ 2 * ν[test |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] z) := hpull
    _ =ᵐ[ν] fun z => nextMomentTwo rate rewards C_star C_h u t hq a z := by
      filter_upwards [hmarker] with z hz
      change (amp z) ^ 2 * ν[(fun w => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingLaw.nextTest
        rate rewards C_star C_h u t (some (some a)) w hq) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
          rate rewards C_star C_h u t control0] z =
        nextMomentTwo rate rewards C_star C_h u t hq a z
      rw [hz]
      exact (nextMomentTwo_eq_amplitude_sq_mul_coefficient
        rate rewards C_star C_h u t hq a z).symm

/-- Every event of the exact next-prior field tests the first scalar moment
under the original finite, unnormalized renewal measure. -/
theorem nextScalar_setIntegral (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) (G : Set Z)
    (hG : MeasurableSet[_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] G) :
    (∫ z in G, nextScalar rate rewards C_star C_h u t hq a z ∂ν) =
      ∫ z in G, nextMomentOne rate rewards C_star C_h u t hq a z ∂ν := by
  have hfield := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hce := nextScalar_condExp rate rewards C_star C_h u t control0 hq a
  have hceG : ∀ᵐ z ∂ν, z ∈ G →
      ν[(fun z => nextScalar rate rewards C_star C_h u t hq a z) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
          rate rewards C_star C_h u t control0] z =
        nextMomentOne rate rewards C_star C_h u t hq a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in G, ν[(fun z => nextScalar rate rewards C_star C_h u t hq a z) |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] z ∂ν :=
      (setIntegral_condExp hfield
        (nextScalar_integrable rate rewards C_star C_h u t control0 hq a) hG).symm
    _ = _ := setIntegral_congr_ae (hfield _ hG) hceG

/-- Every next-prior event tests the square of the same scalar arrival. -/
theorem nextScalar_sq_setIntegral (control0 : ContinuousLearningRows.TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) (G : Set Z)
    (hG : MeasurableSet[_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] G) :
    (∫ z in G, (nextScalar rate rewards C_star C_h u t hq a z) ^ 2 ∂ν) =
      ∫ z in G, nextMomentTwo rate rewards C_star C_h u t hq a z ∂ν := by
  have hfield := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hce := nextScalar_sq_condExp rate rewards C_star C_h u t control0 hq a
  have hceG : ∀ᵐ z ∂ν, z ∈ G →
      ν[(fun z => (nextScalar rate rewards C_star C_h u t hq a z) ^ 2) |
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
          rate rewards C_star C_h u t control0] z =
        nextMomentTwo rate rewards C_star C_h u t hq a z :=
    hce.mono fun z hz _ => hz
  calc
    _ = ∫ z in G, ν[(fun z => (nextScalar rate rewards C_star C_h u t hq a z) ^ 2) |
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] z ∂ν :=
      (setIntegral_condExp hfield
        (nextScalar_sq_integrable rate rewards C_star C_h u t control0 hq a) hG).symm
    _ = _ := setIntegral_congr_ae (hfield _ hG) hceG

theorem nextScalar_zero_of_absent (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = none) :
    nextScalar rate rewards C_star C_h u t hq a z = 0 ∧
      nextAmplitude rate rewards C_star C_h u t hq a z = 0 ∧
      nextMomentOne rate rewards C_star C_h u t hq a z = 0 ∧
      nextMomentTwo rate rewards C_star C_h u t hq a z = 0 := by
  have hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = none := by
    cases hcell : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
        rate rewards C_star C_h u t z hq with
    | none => rfl
    | some c =>
        have hparams := nextParameters_present rate rewards C_star C_h u t hq z c hcell
        rw [hparams] at hp
        cases hp
  simp [nextScalar, nextAmplitude, nextMomentOne, nextMomentTwo, hp, hc]

theorem nextScalar_zero_of_disabled (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (false, xi)) :
    nextScalar rate rewards C_star C_h u t hq a z = 0 ∧
      nextAmplitude rate rewards C_star C_h u t hq a z = 0 ∧
      nextMomentOne rate rewards C_star C_h u t hq a z = 0 ∧
      nextMomentTwo rate rewards C_star C_h u t hq a z = 0 := by
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none =>
      have hnone : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
          rate rewards C_star C_h u t z hq = none := by
        simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hc]
      rw [hnone] at hp
      cases hp
  | some c =>
      have hparams := nextParameters_present rate rewards C_star C_h u t hq z c hc
      have hpair : (c.enabled, c.rate) = (false, xi) :=
        Option.some.inj (hparams.symm.trans hp)
      have hdisabled : c.enabled = false := congrArg Prod.fst hpair
      have hscalar : nextScalar rate rewards C_star C_h u t hq a z =
          RecordedRoundMoments.rawEstimate Q
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c a := by
        simp [nextScalar, hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hscalar]
        exact RecordedRoundMoments.rawEstimate_eq_zero_of_disabled Q
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c a hdisabled
      · simp [nextAmplitude, hp]
      · simp [nextMomentOne, hp]
      · simp [nextMomentTwo, hp]

theorem nextScalar_zero_of_prior_overflow (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (xi : Fin p.K → ℝ)
    (hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq = some (true, xi))
    (hoverflow : priorOverflow rate rewards C_star C_h u t z = true) :
    nextScalar rate rewards C_star C_h u t hq a z = 0 ∧
      nextAmplitude rate rewards C_star C_h u t hq a z = 0 ∧
      nextMomentOne rate rewards C_star C_h u t hq a z = 0 ∧
      nextMomentTwo rate rewards C_star C_h u t hq a z = 0 := by
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none =>
      have hnone : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
          rate rewards C_star C_h u t z hq = none := by
        simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters, hc]
      rw [hnone] at hp
      cases hp
  | some c =>
      have hparams := nextParameters_present rate rewards C_star C_h u t hq z c hc
      have hpair : (c.enabled, c.rate) = (true, xi) :=
        Option.some.inj (hparams.symm.trans hp)
      have hstateOverflow :
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z).overflow = true := by
        have hread := congrArg (fun x => x.2.1)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
            rate rewards C_star C_h u t z)
        change (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z).overflow = priorOverflow rate rewards C_star C_h u t z at hread
        exact hread.symm ▸ hoverflow
      have hscalar : nextScalar rate rewards C_star C_h u t hq a z =
          RecordedRoundMoments.rawEstimate Q
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c a := by
        simp [nextScalar, hc]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hscalar]
        exact RecordedRoundMoments.rawEstimate_eq_zero_after_overflow Q
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c a hstateOverflow
      · simp [nextAmplitude, hp, hoverflow]
      · simp [nextMomentOne, hp, hoverflow]
      · simp [nextMomentTwo, hp, hoverflow]

/-- On each actual present cell, the scalar is exactly the accepted raw
arrival divided by the queue denominator. The physical run retains the full
pre-date history, the accepted current record, and the first date's actual
branch-specific prefix semantics. -/
theorem nextScalar_present_run (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :
    nextScalar rate rewards C_star C_h u t hq a z =
        RecordedRoundMoments.rawEstimate Q
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c a ∧
      RecordedQueueRun.acceptedRecord Q
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c a =
        (if (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z).2.1 then (false, 0)
        else if c.enabled then (true, RecordedQueueRun.quantizedArrival Q c a) else (false, 0)) ∧
      (RecordedQueueRun.run Q
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
            rate rewards C_star C_h u t z ++ [c])).records = (fun j =>
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
            rate rewards C_star C_h u t z).2.2 j ++
            [RecordedQueueRun.acceptedRecord Q
              (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
                rate rewards C_star C_h u t z) c j]) ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) =
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [nextScalar, hc]
  · exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_acceptedRecord
      rate rewards C_star C_h u t z c a
  · exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_acceptedHistories
      rate rewards C_star C_h u t z c
  · exact (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_physical_prefix
      rate rewards C_star C_h u t z hq).1

/-- At a terminal renewal call only the existing physical prefix is exposed;
there is no fabricated next action or future date. -/
theorem terminal_prefix (z : Z) (ht : t.val + 1 = p.T) :
    _root_.Bandits.Support.ReferenceCompleteObservationPrefixInformation.datePrefix
        rate p.T
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
          rate rewards C_star C_h u t z) =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.completeObservation
        rate rewards C_star C_h u t z ∧
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z p.T =
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z).map
        (fun c => some (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical c)) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.terminal_physical_prefix
    rate rewards C_star C_h u t z ht

end Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments

end
