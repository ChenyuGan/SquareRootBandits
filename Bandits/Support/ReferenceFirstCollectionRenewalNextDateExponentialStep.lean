/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# Actual first next-date exponential queue step

This module observes the first actual date after a renewal call on the original
unnormalized renewal source and its exact next-prior field. It does not iterate
the estimate across dates.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep

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

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalLawFinite : IsFiniteMeasure ν :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite
    rate rewards C_star C_h u t

/-- The normalized backlog in the actual current numerical run. -/
def backlogBefore (a : Fin p.K) (z : Z) : ℝ :=
  ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
    rate rewards C_star C_h u t z).registers a).2 /
    ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)

/-- The actual first scalar arrival supplied by the admitted moment producer. -/
def nextArrival (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar
    rate rewards C_star C_h u t hq a z

/-- The literal retained branch: the actual next parameters are enabled and
the incoming, pre-date overflow flag is clear. -/
def retainedNextDate (hq : t.val + 1 < p.T) : Set Z :=
  {z |
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq).elim false Prod.fst = true ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
        rate rewards C_star C_h u t z = false}

/-- The zero-one indicator of the literal retained branch. -/
def retainedNextDateIndicator (hq : t.val + 1 < p.T) (z : Z) : ℝ :=
  Set.indicator (retainedNextDate rate rewards C_star C_h u t hq)
    (fun _ : Z => (1 : ℝ)) z

/-- Retained increment; all other actual branches have zero increment. -/
def nextIncrement (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  if z ∈ retainedNextDate rate rewards C_star C_h u t hq then
    nextArrival rate rewards C_star C_h u t hq a z - 4 else 0

/-- The literal scalar projection of the actual optional next numerical cell.
Absence preserves the existing backlog and constructs no queue input. -/
def backlogAfter (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  match _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none => backlogBefore rate rewards C_star C_h u t a z
  | some c =>
      ((RecordedQueueRun.step
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) c).registers a).2 /
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)

def expBacklogBefore (a : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta * backlogBefore rate rewards C_star C_h u t a z)

def expBacklogAfter (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta * backlogAfter rate rewards C_star C_h u t hq a z)

def expNextIncrement (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) : ℝ :=
  Real.exp (beta * nextIncrement rate rewards C_star C_h u t hq a z)

private theorem measurable_option_elim {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (f : α → β) (hf : Measurable f) (b : β) :
    Measurable (fun o : Option α => o.elim b f) := by
  have hsum : Measurable (fun o : Option α => Equiv.optionEquivSumPUnit α o) :=
    comap_measurable _
  convert (hf.sumElim measurable_const).comp hsum using 1
  funext o
  cases o <;> rfl

private theorem option_fst_true_iff_exists {α : Type*}
    (o : Option (Bool × α)) :
    o.elim false Prod.fst = true ↔ ∃ a : α, o = some (true, a) := by
  cases o with
  | none => simp
  | some pair =>
      cases pair with
      | mk enabled a => cases enabled <;> simp

/-- The complete incoming readout is measurable on exactly the next-prior
field supplied by the admitted readout producer. -/
theorem measurable_incomingReadout :
    Measurable[Fq] (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
      rate rewards C_star C_h u t) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPriorReadout.measurable_wholePostReadout_nextPrior
    rate rewards C_star C_h u t control0

/-- The same complete readout is the readout of the actual current run. -/
theorem incomingReadout_eq_currentState (z : Z) :
    ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
          rate rewards C_star C_h u t z) =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
    rate rewards C_star C_h u t z

/-- The literal retained event is measurable on the exact next-prior field. -/
theorem measurableSet_retainedNextDate (hq : t.val + 1 < p.T) :
    MeasurableSet[Fq] (retainedNextDate rate rewards C_star C_h u t hq) := by
  have hp := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.measurable_nextParameters
    rate rewards C_star C_h u t control0 hq
  have hEnabled : Measurable[Fq] (fun z : Z =>
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
        rate rewards C_star C_h u t z hq).elim false Prod.fst) :=
    (measurable_option_elim Prod.fst measurable_fst false).comp hp
  have hFlagRead := measurable_fst.comp (measurable_snd.comp
    (measurable_incomingReadout rate rewards C_star C_h u t control0))
  have hFlag : Measurable[Fq]
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
        rate rewards C_star C_h u t) := by
    change Measurable[Fq] (fun z : Z =>
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z).2.1)
    exact hFlagRead
  have hEnabledSet : MeasurableSet[Fq]
      {z : Z | (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
          rate rewards C_star C_h u t z hq).elim
          false Prod.fst = true} :=
    hEnabled (measurableSet_singleton true)
  have hFlagSet : MeasurableSet[Fq]
      {z : Z | _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
        rate rewards C_star C_h u t z = false} :=
    hFlag (measurableSet_singleton false)
  change MeasurableSet[Fq] ({z : Z |
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq).elim false Prod.fst = true} ∩
    {z : Z | _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
      rate rewards C_star C_h u t z = false})
  exact hEnabledSet.inter hFlagSet

/-- The option projection in the event definition is exactly the literal
enabled-parameter branch, including its original rate vector witness. -/
theorem mem_retainedNextDate_iff (hq : t.val + 1 < p.T) (z : Z) :
    z ∈ retainedNextDate rate rewards C_star C_h u t hq ↔
      (∃ xi : Fin p.K → ℝ,
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
          rate rewards C_star C_h u t z hq = some (true, xi)) ∧
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
          rate rewards C_star C_h u t z = false := by
  change (((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq).elim false Prod.fst = true) ∧
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
      rate rewards C_star C_h u t z = false) ↔ _
  exact and_congr (option_fst_true_iff_exists
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq)) Iff.rfl

/-- Measurability of the incoming normalized queue on the exact field. -/
theorem measurable_backlogBefore (a : Fin p.K) :
    Measurable[Fq] (backlogBefore rate rewards C_star C_h u t a) := by
  have hread := measurable_incomingReadout rate rewards C_star C_h u t control0
  have hEq : backlogBefore rate rewards C_star C_h u t a =
      (fun z : Z =>
        ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
          rate rewards C_star C_h u t z).1 a).2 /
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters
            rate).n : ℝ)) := by
    funext z
    change (((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
      rate rewards C_star C_h u t z).registers a).2 : ℝ) /
        ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) = _
    rw [← incomingReadout_eq_currentState rate rewards C_star C_h u t z]
    rfl
  rw [hEq]
  have hreg := measurable_pi_apply a |>.comp
    (measurable_fst.comp hread)
  have hback := measurable_snd.comp hreg
  have hcast : Measurable (fun n : ℕ => (n : ℝ)) := measurable_of_countable _
  exact ((hcast.comp hback).div_const
    ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))

/-- The exact next-prior observations retain their supplied measurability. -/
theorem measurable_nextArrival (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (nextArrival rate rewards C_star C_h u t hq a) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.measurable_nextScalar
    rate rewards C_star C_h u t control0 hq a

theorem integrable_nextArrival (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (nextArrival rate rewards C_star C_h u t hq a) ν :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_integrable
    rate rewards C_star C_h u t control0 hq a

private theorem beta_floor : 32 * rate.eta.val ≤ beta := by
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  rw [CanonicalRecordingRates.beta]
  calc
    32 * rate.eta.val = (32 * rate.eta.val) * 1 := by ring
    _ ≤ (32 * rate.eta.val) * (CanonicalRecordingRates.L_stab p : ℝ) :=
      mul_le_mul_of_nonneg_left hL (le_of_lt (mul_pos (by norm_num) rate.eta.property))

private theorem pastCells_rate_lower_bound (z : Z) :
    ∀ round ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z,
      ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  have hparts := List.mem_append.mp (by
    simpa only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells]
      using hround)
  rcases hparts with hlive | hcollection
  · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hlive
    let hc := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.crossing
      rate rewards C_star C_h u t z
    let count := p.T - _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start
      rate rewards C_star C_h u t z
    let hspan := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.full_span
      rate rewards C_star C_h u t z
    have hiWindow : i <
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate z.val rewards C_star C_h hc count hspan).length := by
      have hwindowLen :
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.liveCells
            rate rewards C_star C_h u t z).length =
          (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
            rate z.val rewards C_star C_h hc count hspan).length := by
        change (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
          rate z.val rewards C_star C_h hc count hspan).length = _
        exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
          rate z.val rewards C_star C_h hc count hspan
      exact hwindowLen ▸ hi
    let k : Fin (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate z.val rewards C_star C_h hc count hspan).length := ⟨i, hiWindow⟩
    let sourceCell := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt
      rate z.val rewards C_star C_h hc count hspan k
    have hcell : round = sourceCell.input := by
      calc
        round = (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.liveCells
          rate rewards C_star C_h u t z)[i]'hi := hget.symm
        _ = sourceCell.input := by
          change (ReferenceFirstWindowNumericalStream.actualLiveSourceCells
            rate z.val rewards C_star C_h hc count hspan)[i]'_ = _
          exact ReferenceFirstWindowNumericalStream.actualLiveSourceCells_get
            rate z.val rewards C_star C_h hc count hspan k
    have hfacts := ReferenceFirstWindowNumericalStream.actualLiveSourceCellAt_facts
      rate z.val rewards C_star C_h hc count hspan k
    dsimp only at hfacts
    rcases hfacts with ⟨_, _, _, _, _, _, hrate, _, _⟩
    rw [hcell, hrate]
    exact le_trans (beta_floor rate) (sourceCell.selected.view.payload.beta_le_rate j)
  · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hcollection
    obtain ⟨_, _, _, hcalls⟩ :=
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_chronological_reconstruction
        rate rewards C_star C_h u t z
    obtain ⟨call, _valid, _, hcell⟩ := hcalls ⟨i, by
      simpa only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.collectionCells_length]
        using hi⟩
    rw [hget.symm, hcell]
    change 32 * rate.eta.val ≤ call.payload.rate j
    exact le_trans (beta_floor rate) (call.payload.beta_le_rate j)

private theorem currentCells_rate_lower_bound (z : Z) :
    ∀ round ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z,
      ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells,
    List.mem_append] at hround
  rcases hround with hpast | hcurrent
  · exact pastCells_rate_lower_bound rate rewards C_star C_h u t z round hpast j
  · simp only [List.mem_singleton] at hcurrent
    rw [hcurrent]
    obtain ⟨_, selected, _, _, hrate⟩ :=
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell_numerical
        rate rewards C_star C_h u t z
    rw [hrate]
    exact le_trans (beta_floor rate) (selected.view.payload.beta_le_rate j)

/-- The complete original current run obeys the accepted stopped-queue
envelope; this is derived from its actual source prefix and actual cell rates. -/
theorem backlogBefore_bounds (a : Fin p.K) (z : Z) :
    0 ≤ backlogBefore rate rewards C_star C_h u t a z ∧
      backlogBefore rate rewards C_star C_h u t a z ≤
        2 * (1 / (32 * rate.eta.val)) := by
  have hnonneg : 0 ≤ backlogBefore rate rewards C_star C_h u t a z := by
    unfold backlogBefore
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_pos.mpr
      (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos).le
  have hrun := _root_.Bandits.Support.StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
    (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z)
    (currentCells_rate_lower_bound rate rewards C_star C_h u t z)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
      rate rewards C_star C_h u t z).length a
  have htake :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
        rate rewards C_star C_h u t z).take
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z).length =
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z := by
    apply List.take_of_length_le
    exact le_rfl
  rw [htake] at hrun
  have hupper : backlogBefore rate rewards C_star C_h u t a z ≤
      2 * (1 / (32 * rate.eta.val)) := by
    simpa [backlogBefore,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState,
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells,
      _root_.Bandits.Support.StoppedQueueBound.normalizedBacklog,
      _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters] using hrun
  exact ⟨hnonneg, hupper⟩

theorem nextArrival_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ nextArrival rate rewards C_star C_h u t hq a z ∧
      nextArrival rate rewards C_star C_h u t hq a z ≤ 1 / beta := by
  simpa [nextArrival] using
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_bounds
      rate rewards C_star C_h u t hq a z

theorem nextMomentOne_le_one (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne
        rate rewards C_star C_h u t hq a z ≤ 1 := by
  classical
  cases hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
      rate rewards C_star C_h u t z hq with
  | none => simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne, hp]
  | some pair =>
      cases pair with
      | mk enabled xi =>
          cases enabled with
          | false => simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne, hp]
          | true =>
              cases hf : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
                  rate rewards C_star C_h u t z with
              | true => simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne, hp, hf]
              | false =>
                  have hret :=
                    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne_retained_bounds
                      rate rewards C_star C_h u t hq a z xi hp hf
                  exact hret.2.1.trans hret.2.2

/-- The actual optional cell's queue projection is the reflected update of the
same retained scalar. Inactive, absent, and already-overflowed branches
preserve the incoming backlog. -/
theorem backlogAfter_eq_reflected (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) :
    backlogAfter rate rewards C_star C_h u t hq a z =
      max (backlogBefore rate rewards C_star C_h u t a z +
        nextIncrement rate rewards C_star C_h u t hq a z) 0 := by
  let state := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
    rate rewards C_star C_h u t z
  have hflag : state.overflow =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
        rate rewards C_star C_h u t z := by
    have h := congrArg (fun r => r.2.1)
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState_readout
        rate rewards C_star C_h u t z)
    exact h
  cases hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq with
  | none =>
      have hp : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters
          rate rewards C_star C_h u t z hq = none := by
        simp [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingPriorView.nextParameters,
          hc]
      have hnot : z ∉ retainedNextDate rate rewards C_star C_h u t hq := by
        simp [retainedNextDate, hp]
      simp [backlogAfter, hc, nextIncrement, hnot,
        max_eq_left (backlogBefore_bounds rate rewards C_star C_h u t a z).1]
  | some c =>
      have hp := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextParameters_present
        rate rewards C_star C_h u t hq z c hc
      cases hs : state.overflow with
      | true =>
          have hf : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
              rate rewards C_star C_h u t z = true := by
            rw [← hflag]
            exact hs
          have hnot : z ∉ retainedNextDate rate rewards C_star C_h u t hq := by
            simp [retainedNextDate, hp, hf]
          have hpres := RecordedQueueRun.step_after_overflow_preserves
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            state c hs a
          have hback : backlogAfter rate rewards C_star C_h u t hq a z =
              backlogBefore rate rewards C_star C_h u t a z := by
            simp [backlogAfter, hc, state, backlogBefore, hpres.1]
          rw [hback]
          simp [nextIncrement, hnot,
            max_eq_left (backlogBefore_bounds rate rewards C_star C_h u t a z).1]
      | false =>
          cases he : c.enabled with
          | false =>
              have hnot : z ∉ retainedNextDate rate rewards C_star C_h u t hq := by
                simp [retainedNextDate, hp, he]
              have hpres := RecordedQueueRun.step_disabled_preserves
                (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
                state c he a
              have hback : backlogAfter rate rewards C_star C_h u t hq a z =
                  backlogBefore rate rewards C_star C_h u t a z := by
                simp [backlogAfter, hc, state, backlogBefore, hpres.1]
              rw [hback]
              simp [nextIncrement, hnot,
                max_eq_left (backlogBefore_bounds rate rewards C_star C_h u t a z).1]
          | true =>
              have hf : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.priorOverflow
                  rate rewards C_star C_h u t z = false := by
                rw [← hflag]
                exact hs
              have hgood : z ∈ retainedNextDate rate rewards C_star C_h u t hq := by
                rw [mem_retainedNextDate_iff rate rewards C_star C_h u t hq z]
                exact ⟨⟨c.rate, by simpa [he] using hp⟩, hf⟩
              have hstep :=
                _root_.Bandits.Support.CanonicalQueueProcess.normalizedBacklog_step_of_retained
                  (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
                  state c a hs he
              have hscalar :=
                (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_present_run
                  rate rewards C_star C_h u t hq a z c hc).1
              have hresult : backlogAfter rate rewards C_star C_h u t hq a z =
                  max (backlogBefore rate rewards C_star C_h u t a z +
                    nextArrival rate rewards C_star C_h u t hq a z - 4) 0 := by
                simpa [backlogAfter, hc, state,
                  _root_.Bandits.Support.StoppedQueueBound.normalizedBacklog,
                  backlogBefore, nextArrival, hscalar] using hstep
              rw [nextIncrement, ite_eq_left hgood]
              convert hresult using 1; congr 1; ring

/-- The complete incoming readout's projections stay measurable on the exact
next-prior field, and therefore on the ambient source Borel space. -/
theorem measurable_backlogBefore_ambient (control0 : TimeControl p) (a : Fin p.K) :
    Measurable (backlogBefore rate rewards C_star C_h u t a) := by
  exact (measurable_backlogBefore rate rewards C_star C_h u t control0 a).mono
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) le_rfl

theorem measurableSet_retainedNextDate_ambient (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) :
    MeasurableSet (retainedNextDate rate rewards C_star C_h u t hq) := by
  have hfield := measurableSet_retainedNextDate rate rewards C_star C_h u t control0 hq
  rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_eq_comap
    rate rewards C_star C_h u t control0] at hfield
  rcases hfield with ⟨S, hS, hpre⟩
  rw [← hpre]
  exact hS.preimage
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.measurable_nextPriorObserver
      rate rewards C_star C_h u t control0)

theorem measurable_nextIncrement (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (nextIncrement rate rewards C_star C_h u t hq a) := by
  have hG := measurableSet_retainedNextDate_ambient rate rewards C_star C_h u t control0 hq
  have hY := measurable_nextArrival rate rewards C_star C_h u t control0 hq a
  change Measurable (fun z : Z => if z ∈ retainedNextDate rate rewards C_star C_h u t hq
    then nextArrival rate rewards C_star C_h u t hq a z - 4 else 0)
  exact Measurable.ite hG (hY.sub_const 4) measurable_const

theorem measurable_expBacklogBefore (control0 : TimeControl p) (a : Fin p.K) :
    Measurable (expBacklogBefore rate rewards C_star C_h u t a) := by
  have hb := measurable_backlogBefore_ambient rate rewards C_star C_h u t control0 a
  have hs : Measurable (fun z : Z => beta * backlogBefore rate rewards C_star C_h u t a z) :=
    (measurable_const : Measurable (fun _ : Z => beta)).mul hb
  change Measurable (fun z : Z => Real.exp
    (beta * backlogBefore rate rewards C_star C_h u t a z))
  exact hs.exp

theorem measurable_expNextIncrement (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (expNextIncrement rate rewards C_star C_h u t hq a) := by
  have hx := measurable_nextIncrement rate rewards C_star C_h u t control0 hq a
  have hs : Measurable (fun z : Z => beta * nextIncrement rate rewards C_star C_h u t hq a z) :=
    (measurable_const : Measurable (fun _ : Z => beta)).mul hx
  change Measurable (fun z : Z => Real.exp
    (beta * nextIncrement rate rewards C_star C_h u t hq a z))
  exact hs.exp

theorem measurable_backlogAfter (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (backlogAfter rate rewards C_star C_h u t hq a) := by
  have hb := measurable_backlogBefore_ambient rate rewards C_star C_h u t control0 a
  have hx := measurable_nextIncrement rate rewards C_star C_h u t control0 hq a
  have hsum := hb.add hx
  have hmax := Measurable.max hsum
    (measurable_const : Measurable (fun _ : Z => (0 : ℝ)))
  have heq : backlogAfter rate rewards C_star C_h u t hq a =
      (fun z : Z => max (backlogBefore rate rewards C_star C_h u t a z +
        nextIncrement rate rewards C_star C_h u t hq a z) 0) := by
    funext z
    exact backlogAfter_eq_reflected rate rewards C_star C_h u t hq a z
  rw [heq]
  exact hmax

theorem measurable_expBacklogAfter (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (expBacklogAfter rate rewards C_star C_h u t hq a) := by
  have hb := measurable_backlogAfter rate rewards C_star C_h u t control0 hq a
  have hs : Measurable (fun z : Z => beta * backlogAfter rate rewards C_star C_h u t hq a z) :=
    (measurable_const : Measurable (fun _ : Z => beta)).mul hb
  change Measurable (fun z : Z => Real.exp
    (beta * backlogAfter rate rewards C_star C_h u t hq a z))
  exact hs.exp

private theorem integrable_of_measurable_norm_le_const {f : Z → ℝ}
    (hf : Measurable f) (C : ℝ) (hbound : ∀ z, ‖f z‖ ≤ C) : Integrable f ν := by
  refine (integrable_const C).mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with z
  exact hbound z

theorem backlogBefore_integrable (control0 : TimeControl p) (a : Fin p.K) :
    Integrable (backlogBefore rate rewards C_star C_h u t a) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_backlogBefore_ambient rate rewards C_star C_h u t control0 a)
    (2 * (1 / (32 * rate.eta.val)) )
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (backlogBefore_bounds rate rewards C_star C_h u t a z).1]
  exact (backlogBefore_bounds rate rewards C_star C_h u t a z).2

theorem nextIncrement_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    -4 ≤ nextIncrement rate rewards C_star C_h u t hq a z ∧
      nextIncrement rate rewards C_star C_h u t hq a z ≤ 1 / beta := by
  by_cases hG : z ∈ retainedNextDate rate rewards C_star C_h u t hq
  · rw [nextIncrement, ite_eq_left hG]
    have hY := nextArrival_bounds rate rewards C_star C_h u t hq a z
    constructor <;> linarith
  · rw [nextIncrement, ite_eq_right hG]
    have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
    exact ⟨by norm_num, le_of_lt (one_div_pos.mpr hbeta)⟩

theorem backlogAfter_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ backlogAfter rate rewards C_star C_h u t hq a z ∧
      backlogAfter rate rewards C_star C_h u t hq a z ≤
        2 * (1 / (32 * rate.eta.val)) + 1 / beta := by
  rw [backlogAfter_eq_reflected rate rewards C_star C_h u t hq a z]
  have hb := backlogBefore_bounds rate rewards C_star C_h u t a z
  have hx := nextIncrement_bounds rate rewards C_star C_h u t hq a z
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hInv : 0 ≤ 1 / beta := one_div_nonneg.mpr hbeta.le
  constructor
  · exact le_max_right _ _
  · calc
      max (backlogBefore rate rewards C_star C_h u t a z +
          nextIncrement rate rewards C_star C_h u t hq a z) 0 ≤
        max (backlogBefore rate rewards C_star C_h u t a z + 1 / beta) 0 :=
          max_le_max (by nlinarith [hx.2]) le_rfl
      _ = backlogBefore rate rewards C_star C_h u t a z + 1 / beta :=
        max_eq_left (add_nonneg hb.1 hInv)
      _ ≤ 2 * (1 / (32 * rate.eta.val)) + 1 / beta := by linarith [hb.2]

theorem measurable_expNextArrival (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Measurable (fun z : Z => Real.exp
      (beta * nextArrival rate rewards C_star C_h u t hq a z)) := by
  exact ((measurable_const : Measurable (fun _ : Z => beta)).mul
    (measurable_nextArrival rate rewards C_star C_h u t control0 hq a)).exp

theorem expNextArrival_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ Real.exp (beta * nextArrival rate rewards C_star C_h u t hq a z) ∧
      Real.exp (beta * nextArrival rate rewards C_star C_h u t hq a z) ≤ Real.exp 1 := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hY := nextArrival_bounds rate rewards C_star C_h u t hq a z
  have hscaled : beta * nextArrival rate rewards C_star C_h u t hq a z ≤ 1 := by
    calc
      beta * nextArrival rate rewards C_star C_h u t hq a z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hY.2 hbeta.le
      _ = 1 := by field_simp
  exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le hscaled⟩

theorem expNextIncrement_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ expNextIncrement rate rewards C_star C_h u t hq a z ∧
      expNextIncrement rate rewards C_star C_h u t hq a z ≤ Real.exp 1 := by
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hx := nextIncrement_bounds rate rewards C_star C_h u t hq a z
  have hscaled : beta * nextIncrement rate rewards C_star C_h u t hq a z ≤ 1 := by
    calc
      beta * nextIncrement rate rewards C_star C_h u t hq a z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hx.2 hbeta.le
      _ = 1 := by field_simp
  exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le hscaled⟩

theorem expBacklogBefore_bounds (a : Fin p.K) (z : Z) :
    0 ≤ expBacklogBefore rate rewards C_star C_h u t a z ∧
      expBacklogBefore rate rewards C_star C_h u t a z ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
  have hb := backlogBefore_bounds rate rewards C_star C_h u t a z
  exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le
    (mul_le_mul_of_nonneg_left hb.2
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le)⟩

theorem expBacklogAfter_bounds (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    0 ≤ expBacklogAfter rate rewards C_star C_h u t hq a z ∧
      expBacklogAfter rate rewards C_star C_h u t hq a z ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)) + 1 / beta)) := by
  have hb := backlogAfter_bounds rate rewards C_star C_h u t hq a z
  exact ⟨Real.exp_nonneg _, Real.exp_le_exp_of_le
    (mul_le_mul_of_nonneg_left hb.2
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le)⟩

theorem nextIncrement_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (nextIncrement rate rewards C_star C_h u t hq a) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_nextIncrement rate rewards C_star C_h u t control0 hq a)
    (4 + 1 / beta)
  intro z
  rw [Real.norm_eq_abs]
  have hbeta : 0 < beta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hInv : 0 ≤ 1 / beta := one_div_nonneg.mpr hbeta.le
  exact abs_le.mpr ⟨by linarith [(nextIncrement_bounds rate rewards C_star C_h u t hq a z).1, hInv],
    by linarith [(nextIncrement_bounds rate rewards C_star C_h u t hq a z).2, hInv]⟩

theorem expNextArrival_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (fun z : Z => Real.exp
      (beta * nextArrival rate rewards C_star C_h u t hq a z)) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_expNextArrival rate rewards C_star C_h u t control0 hq a) (Real.exp 1)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (expNextArrival_bounds rate rewards C_star C_h u t hq a z).1]
  exact (expNextArrival_bounds rate rewards C_star C_h u t hq a z).2

theorem expNextIncrement_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (expNextIncrement rate rewards C_star C_h u t hq a) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_expNextIncrement rate rewards C_star C_h u t control0 hq a) (Real.exp 1)
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (expNextIncrement_bounds rate rewards C_star C_h u t hq a z).1]
  exact (expNextIncrement_bounds rate rewards C_star C_h u t hq a z).2

theorem expBacklogBefore_integrable (control0 : TimeControl p) (a : Fin p.K) :
    Integrable (expBacklogBefore rate rewards C_star C_h u t a) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_expBacklogBefore rate rewards C_star C_h u t control0 a)
    (Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) )
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (expBacklogBefore_bounds rate rewards C_star C_h u t a z).1]
  exact (expBacklogBefore_bounds rate rewards C_star C_h u t a z).2

theorem expBacklogAfter_integrable (control0 : TimeControl p)
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (expBacklogAfter rate rewards C_star C_h u t hq a) ν := by
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    (measurable_expBacklogAfter rate rewards C_star C_h u t control0 hq a)
    (Real.exp (beta * (2 * (1 / (32 * rate.eta.val)) + 1 / beta)))
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (expBacklogAfter_bounds rate rewards C_star C_h u t hq a z).1]
  exact (expBacklogAfter_bounds rate rewards C_star C_h u t hq a z).2

private theorem condExp_real_const_mul (c : ℝ) (f : Z → ℝ) :
    ν[(fun z : Z => c * f z) | Fq] =ᵐ[ν]
      (fun z : Z => c * ν[f | Fq] z) := by
  have hscaled := condExp_smul (μ := ν) c f Fq
  have hfun : (fun z : Z => c * f z) = c • f := by
    funext z
    simp [smul_eq_mul]
  calc
    ν[(fun z : Z => c * f z) | Fq] =ᵐ[ν] ν[c • f | Fq] :=
      condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hfun z)
    _ =ᵐ[ν] (fun z : Z => c * ν[f | Fq] z) := by
      filter_upwards [hscaled] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz

private theorem expNextArrival_le_chord (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) :
    Real.exp (beta * nextArrival rate rewards C_star C_h u t hq a z) ≤
      1 + ((Real.exp 1 - 1) * beta) * nextArrival rate rewards C_star C_h u t hq a z := by
  have hY := nextArrival_bounds rate rewards C_star C_h u t hq a z
  have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
  have hscaled_nonneg : 0 ≤ beta * nextArrival rate rewards C_star C_h u t hq a z :=
    mul_nonneg hbeta.le hY.1
  have hscaled_le : beta * nextArrival rate rewards C_star C_h u t hq a z ≤ 1 := by
    calc
      beta * nextArrival rate rewards C_star C_h u t hq a z ≤ beta * (1 / beta) :=
        mul_le_mul_of_nonneg_left hY.2 hbeta.le
      _ = 1 := by field_simp
  calc
    Real.exp (beta * nextArrival rate rewards C_star C_h u t hq a z) ≤
        1 + (Real.exp 1 - 1) *
          (beta * nextArrival rate rewards C_star C_h u t hq a z) :=
      RecordedRoundMoments.exp_le_unit_chord hscaled_nonneg hscaled_le
    _ = 1 + ((Real.exp 1 - 1) * beta) *
          nextArrival rate rewards C_star C_h u t hq a z := by ring

/-- Conditional exponential chord on the original source law and the exact
next-prior field, with the actual first scalar's conditional moment. -/
theorem condExp_expNextArrival_le_chord (hq : t.val + 1 < p.T) (a : Fin p.K) :
    ν[(fun z : Z => Real.exp
      (beta * nextArrival rate rewards C_star C_h u t hq a z)) | Fq] ≤ᵐ[ν]
      (fun z : Z => 1 + ((Real.exp 1 - 1) * beta) *
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne
          rate rewards C_star C_h u t hq a z) := by
  let c : ℝ := (Real.exp 1 - 1) * beta
  let moment : Z → ℝ :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne
      rate rewards C_star C_h u t hq a
  have hExpInt := expNextArrival_integrable rate rewards C_star C_h u t control0 hq a
  have hYInt := integrable_nextArrival rate rewards C_star C_h u t control0 hq a
  have hScaledInt : Integrable (fun z : Z => c * nextArrival rate rewards C_star C_h u t hq a z) ν := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hYInt.const_mul c
  have hChordInt : Integrable
      (fun z : Z => 1 + c * nextArrival rate rewards C_star C_h u t hq a z) ν :=
    (integrable_const (1 : ℝ)).add hScaledInt
  have hPoint : ∀ z : Z,
      Real.exp (beta * nextArrival rate rewards C_star C_h u t hq a z) ≤
        1 + c * nextArrival rate rewards C_star C_h u t hq a z := by
    intro z
    simpa [c] using expNextArrival_le_chord rate rewards C_star C_h u t hq a z
  have hmono := condExp_mono (m := Fq) hExpInt hChordInt
    (Filter.Eventually.of_forall hPoint)
  have hAdd := condExp_add (integrable_const (1 : ℝ)) hScaledInt Fq
  have hConst := condExp_const (μ := ν)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0) (1 : ℝ)
  have hScale := condExp_real_const_mul rate rewards C_star C_h u t control0 c
    (nextArrival rate rewards C_star C_h u t hq a)
  have hMoment :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_condExp
      rate rewards C_star C_h u t control0 hq a
  have hMoment' : ν[nextArrival rate rewards C_star C_h u t hq a | Fq] =ᵐ[ν] moment := by
    change ν[_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar
      rate rewards C_star C_h u t hq a | Fq] =ᵐ[ν] moment
    simpa [moment] using hMoment
  have hChordCE : ν[(fun z : Z => 1 + c * nextArrival rate rewards C_star C_h u t hq a z) | Fq] =ᵐ[ν]
      (fun z : Z => 1 + c * moment z) := by
    have hChordAdd : (fun z : Z => 1 + c * nextArrival rate rewards C_star C_h u t hq a z) =
        (fun _ : Z => (1 : ℝ)) +
          (fun z : Z => c * nextArrival rate rewards C_star C_h u t hq a z) := by
      funext z
      rfl
    rw [hChordAdd]
    filter_upwards [hAdd, hScale, hMoment'] with z hAddZ hScaleZ hMomentZ
    have hconst := congrFun hConst z
    calc
      ν[(fun _ : Z => (1 : ℝ)) +
          (fun z : Z => c * nextArrival rate rewards C_star C_h u t hq a z) | Fq] z =
          ν[(fun _ : Z => (1 : ℝ)) | Fq] z +
            ν[(fun z : Z => c * nextArrival rate rewards C_star C_h u t hq a z) | Fq] z := hAddZ
      _ = 1 + c * moment z := by rw [hconst, hScaleZ, hMomentZ]
  have hfinal := Filter.EventuallyLE.trans hmono hChordCE.le
  simpa [c, moment] using hfinal

private theorem expNextIncrement_indicator_identity (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z) :
    expNextIncrement rate rewards C_star C_h u t hq a z =
      Real.exp (-4 * beta) * Set.indicator
        (retainedNextDate rate rewards C_star C_h u t hq)
        (fun w : Z => Real.exp
          (beta * nextArrival rate rewards C_star C_h u t hq a w)) z +
        Set.indicator (retainedNextDate rate rewards C_star C_h u t hq)ᶜ
          (fun _ : Z => (1 : ℝ)) z := by
  by_cases hG : z ∈ retainedNextDate rate rewards C_star C_h u t hq
  · have harg : beta * (nextArrival rate rewards C_star C_h u t hq a z - 4) =
        (-4 * beta) + beta * nextArrival rate rewards C_star C_h u t hq a z := by ring
    simp [expNextIncrement, nextIncrement, hG, harg, Real.exp_add]
  · simp [expNextIncrement, nextIncrement, hG]

/-- Conditional exponential increment bound on the actual unnormalized
source law and exact next-prior field. -/
theorem condExp_expNextIncrement_le_one (hq : t.val + 1 < p.T) (a : Fin p.K) :
    ν[expNextIncrement rate rewards C_star C_h u t hq a | Fq] ≤ᵐ[ν]
      (fun _ : Z => 1) := by
  let G := retainedNextDate rate rewards C_star C_h u t hq
  let f : Z → ℝ := fun z => Real.exp
    (beta * nextArrival rate rewards C_star C_h u t hq a z)
  let fG : Z → ℝ := Set.indicator G f
  let fGc : Z → ℝ := Set.indicator Gᶜ (fun _ : Z => (1 : ℝ))
  let cExp : ℝ := Real.exp (-4 * beta)
  have hGfield : MeasurableSet[Fq] G :=
    measurableSet_retainedNextDate rate rewards C_star C_h u t control0 hq
  have hGambient := measurableSet_retainedNextDate_ambient
    rate rewards C_star C_h u t control0 hq
  have hfInt : Integrable f ν := by
    simpa [f] using expNextArrival_integrable rate rewards C_star C_h u t control0 hq a
  have hfGInt : Integrable fG ν := by
    simpa [fG] using hfInt.indicator hGambient
  have hfGcInt : Integrable fGc ν := by
    simpa [fGc] using (integrable_const (1 : ℝ)).indicator hGambient.compl
  have hcExpInt : Integrable (fun z : Z => cExp * fG z) ν := hfGInt.const_mul cExp
  have hEq : expNextIncrement rate rewards C_star C_h u t hq a =
      (fun z : Z => cExp * fG z + fGc z) := by
    funext z
    simpa [G, f, fG, fGc, cExp] using
      expNextIncrement_indicator_identity rate rewards C_star C_h u t hq a z
  have hAdd := condExp_add hcExpInt hfGcInt Fq
  have hAddForm : (fun z : Z => cExp * fG z + fGc z) =
      (fun z : Z => cExp * fG z) + fGc := by
    funext z
    rfl
  have hScale := condExp_real_const_mul rate rewards C_star C_h u t control0 cExp fG
  have hMask := condExp_indicator (μ := ν) hfInt hGfield
  have hMaskComp := condExp_indicator (μ := ν) (integrable_const (1 : ℝ)) hGfield.compl
  have hConst : ν[(fun _ : Z => (1 : ℝ)) | Fq] = (fun _ : Z => (1 : ℝ)) :=
    condExp_const (μ := ν) (m := Fq) (m₀ := inferInstance)
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
        rate rewards C_star C_h u t control0) (1 : ℝ)
  have hDecomp : ν[expNextIncrement rate rewards C_star C_h u t hq a | Fq] =ᵐ[ν]
      (fun z : Z => cExp * Set.indicator G (fun w => ν[f | Fq] w) z +
        Set.indicator Gᶜ (fun _ : Z => (1 : ℝ)) z) := by
    calc
      ν[expNextIncrement rate rewards C_star C_h u t hq a | Fq] =ᵐ[ν]
          ν[(fun z : Z => cExp * fG z + fGc z) | Fq] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hEq z)
      _ =ᵐ[ν] ν[(fun z : Z => cExp * fG z) + fGc | Fq] :=
        condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hAddForm z)
      _ =ᵐ[ν] ν[(fun z : Z => cExp * fG z) | Fq] + ν[fGc | Fq] := hAdd
      _ =ᵐ[ν] (fun z : Z => cExp * ν[fG | Fq] z + ν[fGc | Fq] z) := by
        filter_upwards [hScale] with z hz
        exact congrArg (fun v : ℝ => v + ν[fGc | Fq] z) hz
      _ =ᵐ[ν] (fun z : Z => cExp * Set.indicator G
            (fun w => ν[f | Fq] w) z +
          Set.indicator Gᶜ (fun _ : Z => (1 : ℝ)) z) := by
        filter_upwards [hMask, hMaskComp] with z hg hgc
        rw [hg, hgc, hConst]
  have hChord := condExp_expNextArrival_le_chord rate rewards C_star C_h u t control0 hq a
  have hExpFactor : 0 < cExp := by positivity
  have hCoeff : 0 ≤ (Real.exp 1 - 1) * beta := by
    have he : 1 ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact mul_nonneg (by linarith) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  have hScalar :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalExponentialIncrement.exp_neg_four_beta_chord_le_one
      rate
  filter_upwards [hDecomp, hChord] with z hdecomp hchord
  rw [hdecomp]
  by_cases hG : z ∈ G
  · have hnot : z ∉ Gᶜ := by simpa using hG
    simp only [Set.indicator_of_mem hG, Set.indicator_of_notMem hnot, add_zero]
    have hM := nextMomentOne_le_one rate rewards C_star C_h u t hq a z
    have hUpperM :
        ν[(fun w : Z => Real.exp (beta * nextArrival rate rewards C_star C_h u t hq a w)) | Fq] z ≤
          1 + ((Real.exp 1 - 1) * beta) := by
      calc
        _ ≤ 1 + ((Real.exp 1 - 1) * beta) *
              _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextMomentOne
                rate rewards C_star C_h u t hq a z := hchord
        _ ≤ 1 + ((Real.exp 1 - 1) * beta) * 1 := by
          nlinarith [mul_le_mul_of_nonneg_left hM hCoeff]
        _ = 1 + ((Real.exp 1 - 1) * beta) := by ring
    calc
      cExp * ν[f | Fq] z ≤ cExp * (1 + ((Real.exp 1 - 1) * beta)) :=
        mul_le_mul_of_nonneg_left hUpperM hExpFactor.le
      _ ≤ 1 := by simpa [cExp] using hScalar
  · have hmem : z ∈ Gᶜ := by simpa using hG
    simp [Set.indicator_of_notMem hG, Set.indicator_of_mem hmem]

private theorem exp_max_add_le (b x : ℝ) :
    Real.exp (beta * max (b + x) 0) ≤
      1 + Real.exp (beta * b) * Real.exp (beta * x) := by
  by_cases h : 0 ≤ b + x
  · rw [max_eq_left h]
    have harg : beta * (b + x) = beta * b + beta * x := by ring
    rw [harg, Real.exp_add]
    have hprod : 0 < Real.exp (beta * b) * Real.exp (beta * x) :=
      mul_pos (Real.exp_pos _) (Real.exp_pos _)
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    simp only [mul_zero, Real.exp_zero]
    have hprod : 0 < Real.exp (beta * b) * Real.exp (beta * x) :=
      mul_pos (Real.exp_pos _) (Real.exp_pos _)
    linarith

/-- Off the literal retained event the actual queue is unchanged, so its
exponential is unchanged as well. -/
theorem expBacklogAfter_eq_expBacklogBefore_of_not_retained
    (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z)
    (hG : z ∉ retainedNextDate rate rewards C_star C_h u t hq) :
    expBacklogAfter rate rewards C_star C_h u t hq a z =
      expBacklogBefore rate rewards C_star C_h u t a z := by
  have hback := backlogAfter_eq_reflected rate rewards C_star C_h u t hq a z
  have hb := backlogBefore_bounds rate rewards C_star C_h u t a z
  have hsame : backlogAfter rate rewards C_star C_h u t hq a z =
      backlogBefore rate rewards C_star C_h u t a z := by
    rw [hback, nextIncrement, ite_eq_right hG, add_zero]
    exact max_eq_left hb.1
  rw [expBacklogAfter, hsame, expBacklogBefore]

/-- The reflected queue exponential is bounded by one plus the incoming
exponential times this date's actual increment exponential. -/
theorem expBacklogAfter_le_one_add_product
    (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    expBacklogAfter rate rewards C_star C_h u t hq a z ≤
      1 + expBacklogBefore rate rewards C_star C_h u t a z *
        expNextIncrement rate rewards C_star C_h u t hq a z := by
  rw [expBacklogAfter, backlogAfter_eq_reflected rate rewards C_star C_h u t hq a z]
  simpa [expBacklogBefore, expNextIncrement] using
    exp_max_add_le rate
      (backlogBefore rate rewards C_star C_h u t a z)
      (nextIncrement rate rewards C_star C_h u t hq a z)

/-- Pointwise one-date queue estimate on the original source; the retained
indicator has unit cost and the increment factor is unmasked. -/
theorem expBacklogAfter_le_indicator_add_product
    (hq : t.val + 1 < p.T) (a : Fin p.K) (z : Z) :
    expBacklogAfter rate rewards C_star C_h u t hq a z ≤
      retainedNextDateIndicator rate rewards C_star C_h u t hq z +
        expBacklogBefore rate rewards C_star C_h u t a z *
          expNextIncrement rate rewards C_star C_h u t hq a z := by
  by_cases hG : z ∈ retainedNextDate rate rewards C_star C_h u t hq
  · have h := expBacklogAfter_le_one_add_product
      rate rewards C_star C_h u t hq a z
    simpa [retainedNextDateIndicator, hG, add_comm] using h
  · rw [expBacklogAfter_eq_expBacklogBefore_of_not_retained
      rate rewards C_star C_h u t hq a z hG]
    have hE : expNextIncrement rate rewards C_star C_h u t hq a z = 1 := by
      simp [expNextIncrement, nextIncrement, hG]
    simp [retainedNextDateIndicator, hG, hE]

theorem measurable_expBacklogBefore_nextPrior (a : Fin p.K) :
    Measurable[Fq] (expBacklogBefore rate rewards C_star C_h u t a) := by
  change Measurable[Fq] (fun z : Z => Real.exp
    (beta * backlogBefore rate rewards C_star C_h u t a z))
  exact ((measurable_const : Measurable[Fq] (fun _ : Z => beta)).mul
    (measurable_backlogBefore rate rewards C_star C_h u t control0 a)).exp

private theorem integrable_expBacklogBefore_mul_expNextIncrement
    (control0 : TimeControl p) (hq : t.val + 1 < p.T) (a : Fin p.K) :
    Integrable (fun z : Z => expBacklogBefore rate rewards C_star C_h u t a z *
      expNextIncrement rate rewards C_star C_h u t hq a z) ν := by
  let C := Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) * Real.exp 1
  apply integrable_of_measurable_norm_le_const rate rewards C_star C_h u t
    ((measurable_expBacklogBefore rate rewards C_star C_h u t control0 a).mul
      (measurable_expNextIncrement rate rewards C_star C_h u t control0 hq a)) C
  intro z
  have hb := expBacklogBefore_bounds rate rewards C_star C_h u t a z
  have hx := expNextIncrement_bounds rate rewards C_star C_h u t hq a z
  change ‖expBacklogBefore rate rewards C_star C_h u t a z *
    expNextIncrement rate rewards C_star C_h u t hq a z‖ ≤ C
  rw [Real.norm_of_nonneg (mul_nonneg hb.1 hx.1)]
  dsimp [C]
  exact mul_le_mul hb.2 hx.2 hx.1 (Real.exp_nonneg _)

/-- Conditional queue estimate on this one actual date and exact next-prior
field. -/
theorem condExp_expBacklogAfter_le_expBacklogBefore_add_indicator
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    ν[expBacklogAfter rate rewards C_star C_h u t hq a | Fq] ≤ᵐ[ν]
      (fun z : Z => expBacklogBefore rate rewards C_star C_h u t a z +
        retainedNextDateIndicator rate rewards C_star C_h u t hq z) := by
  let product : Z → ℝ := fun z =>
    expBacklogBefore rate rewards C_star C_h u t a z *
      expNextIncrement rate rewards C_star C_h u t hq a z
  let majorant : Z → ℝ := fun z =>
    retainedNextDateIndicator rate rewards C_star C_h u t hq z + product z
  have hGfield := measurableSet_retainedNextDate rate rewards C_star C_h u t control0 hq
  have hGambient := measurableSet_retainedNextDate_ambient
    rate rewards C_star C_h u t control0 hq
  have hIndicatorInt : Integrable
      (retainedNextDateIndicator rate rewards C_star C_h u t hq) ν := by
    change Integrable (Set.indicator _ (fun _ : Z => (1 : ℝ))) ν
    exact (integrable_const (1 : ℝ)).indicator hGambient
  have hBeforeInt := expBacklogBefore_integrable rate rewards C_star C_h u t control0 a
  have hAfterInt := expBacklogAfter_integrable rate rewards C_star C_h u t control0 hq a
  have hIncrementInt := expNextIncrement_integrable rate rewards C_star C_h u t control0 hq a
  have hProductInt : Integrable product ν := by
    change Integrable (fun z : Z =>
      expBacklogBefore rate rewards C_star C_h u t a z *
        expNextIncrement rate rewards C_star C_h u t hq a z) ν
    exact integrable_expBacklogBefore_mul_expNextIncrement
      rate rewards C_star C_h u t control0 hq a
  have hMajorantInt : Integrable majorant ν := by
    change Integrable
      ((retainedNextDateIndicator rate rewards C_star C_h u t hq) + product) ν
    exact hIndicatorInt.add hProductInt
  have hPoint :
      (fun z : Z => expBacklogAfter rate rewards C_star C_h u t hq a z) ≤ᵐ[ν] majorant := by
    filter_upwards [] with z
    change expBacklogAfter rate rewards C_star C_h u t hq a z ≤
      retainedNextDateIndicator rate rewards C_star C_h u t hq z +
        expBacklogBefore rate rewards C_star C_h u t a z *
          expNextIncrement rate rewards C_star C_h u t hq a z
    exact expBacklogAfter_le_indicator_add_product
      rate rewards C_star C_h u t hq a z
  have hmono := condExp_mono (m := Fq) hAfterInt hMajorantInt hPoint
  have hAdd := condExp_add hIndicatorInt hProductInt Fq
  have hOneInt : Integrable (fun _ : Z => (1 : ℝ)) ν := integrable_const 1
  have hMask := condExp_indicator (μ := ν) hOneInt hGfield
  have hConst : ν[(fun _ : Z => (1 : ℝ)) | Fq] = (fun _ : Z => (1 : ℝ)) :=
    condExp_const (μ := ν) (m := Fq) (m₀ := inferInstance)
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
        rate rewards C_star C_h u t control0) (1 : ℝ)
  have hIndicatorCE :
      ν[retainedNextDateIndicator rate rewards C_star C_h u t hq | Fq] =ᵐ[ν]
        retainedNextDateIndicator rate rewards C_star C_h u t hq := by
    change ν[Set.indicator (retainedNextDate rate rewards C_star C_h u t hq)
        (fun _ : Z => (1 : ℝ)) | Fq] =ᵐ[ν]
      Set.indicator (retainedNextDate rate rewards C_star C_h u t hq)
        (fun _ : Z => (1 : ℝ))
    filter_upwards [hMask] with z hz
    change ν[Set.indicator (retainedNextDate rate rewards C_star C_h u t hq)
        (fun _ : Z => (1 : ℝ)) | Fq] z =
      Set.indicator (retainedNextDate rate rewards C_star C_h u t hq)
        (fun w : Z => ν[(fun _ : Z => (1 : ℝ)) | Fq] w) z at hz
    rw [hConst] at hz
    exact hz
  have hPull := condExp_mul_of_aestronglyMeasurable_left
    (measurable_expBacklogBefore_nextPrior rate rewards C_star C_h u t control0 a).aestronglyMeasurable
    hProductInt hIncrementInt
  have hProductCE : ν[product | Fq] =ᵐ[ν]
      (fun z : Z => expBacklogBefore rate rewards C_star C_h u t a z *
        ν[expNextIncrement rate rewards C_star C_h u t hq a | Fq] z) := by
    change ν[(expBacklogBefore rate rewards C_star C_h u t a) *
      (expNextIncrement rate rewards C_star C_h u t hq a) | Fq] =ᵐ[ν] _
    exact hPull
  have hStep := condExp_expNextIncrement_le_one rate rewards C_star C_h u t control0 hq a
  have hBeforeNonneg : ∀ᵐ z ∂ν,
      0 ≤ expBacklogBefore rate rewards C_star C_h u t a z := by
    filter_upwards [] with z
    exact (expBacklogBefore_bounds rate rewards C_star C_h u t a z).1
  filter_upwards [hmono, hAdd, hIndicatorCE, hProductCE, hStep, hBeforeNonneg]
      with z hmonoZ hAddZ hIndicatorZ hProductZ hStepZ hBeforeZ
  calc
    ν[expBacklogAfter rate rewards C_star C_h u t hq a | Fq] z ≤
        ν[majorant | Fq] z := hmonoZ
    _ = ν[retainedNextDateIndicator rate rewards C_star C_h u t hq | Fq] z +
        ν[product | Fq] z := hAddZ
    _ = retainedNextDateIndicator rate rewards C_star C_h u t hq z +
        expBacklogBefore rate rewards C_star C_h u t a z *
          ν[expNextIncrement rate rewards C_star C_h u t hq a | Fq] z := by
      rw [hIndicatorZ, hProductZ]
    _ ≤ retainedNextDateIndicator rate rewards C_star C_h u t hq z +
        expBacklogBefore rate rewards C_star C_h u t a z * 1 :=
      by nlinarith [mul_le_mul_of_nonneg_left hStepZ hBeforeZ]
    _ = expBacklogBefore rate rewards C_star C_h u t a z +
        retainedNextDateIndicator rate rewards C_star C_h u t hq z := by ring

/-- The coarser one-date bound follows because the retained cost is an
indicator. -/
theorem condExp_expBacklogAfter_le_expBacklogBefore_add_one
    (hq : t.val + 1 < p.T) (a : Fin p.K) :
    ν[expBacklogAfter rate rewards C_star C_h u t hq a | Fq] ≤ᵐ[ν]
      (fun z : Z => expBacklogBefore rate rewards C_star C_h u t a z + 1) := by
  have h := condExp_expBacklogAfter_le_expBacklogBefore_add_indicator
    rate rewards C_star C_h u t control0 hq a
  have hInd : ∀ z : Z,
      retainedNextDateIndicator rate rewards C_star C_h u t hq z ≤ 1 := by
    intro z
    by_cases hz : z ∈ retainedNextDate rate rewards C_star C_h u t hq <;>
      simp [retainedNextDateIndicator, hz]
  filter_upwards [h] with z hz
  exact (by nlinarith [hInd z, hz])

/-- Weighted one-date estimate for a bounded nonnegative test measurable on
the exact next-prior field. The test assumptions are internal to this API. -/
theorem integral_mul_expBacklogAfter_le
    (hq : t.val + 1 < p.T) (a : Fin p.K) {W : Z → ℝ}
    (hWfield : AEStronglyMeasurable[Fq] W ν)
    (hWambient : Measurable W)
    (hWnonneg : 0 ≤ᵐ[ν] W)
    (hWbounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z ∂ν, ‖W z‖ ≤ C) :
    (∫ z : Z, W z * expBacklogAfter rate rewards C_star C_h u t hq a z ∂ν) ≤
      (∫ z : Z, W z * expBacklogBefore rate rewards C_star C_h u t a z ∂ν) +
        ∫ z : Z, W z * retainedNextDateIndicator rate rewards C_star C_h u t hq z ∂ν := by
  rcases hWbounded with ⟨C, hC, hWbound⟩
  have hWInt : Integrable W ν := by
    refine (integrable_const C).mono' hWambient.aestronglyMeasurable ?_
    filter_upwards [hWbound] with z hz
    simpa [Real.norm_of_nonneg hC] using hz
  have hAfterBound : ∀ᵐ z ∂ν,
      ‖expBacklogAfter rate rewards C_star C_h u t hq a z‖ ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)) + 1 / beta)) := by
    filter_upwards [] with z
    rw [Real.norm_of_nonneg
      (expBacklogAfter_bounds rate rewards C_star C_h u t hq a z).1]
    exact (expBacklogAfter_bounds rate rewards C_star C_h u t hq a z).2
  have hBeforeBound : ∀ᵐ z ∂ν,
      ‖expBacklogBefore rate rewards C_star C_h u t a z‖ ≤
        Real.exp (beta * (2 * (1 / (32 * rate.eta.val)))) := by
    filter_upwards [] with z
    rw [Real.norm_of_nonneg
      (expBacklogBefore_bounds rate rewards C_star C_h u t a z).1]
    exact (expBacklogBefore_bounds rate rewards C_star C_h u t a z).2
  have hIndicatorBound : ∀ᵐ z ∂ν,
      ‖retainedNextDateIndicator rate rewards C_star C_h u t hq z‖ ≤ 1 := by
    filter_upwards [] with z
    by_cases hz : z ∈ retainedNextDate rate rewards C_star C_h u t hq
    · simp [retainedNextDateIndicator, hz]
    · simp [retainedNextDateIndicator, hz]
  have hIndicatorMeas : Measurable
      (retainedNextDateIndicator rate rewards C_star C_h u t hq) :=
    (measurable_const : Measurable (fun _ : Z => (1 : ℝ))).indicator
      (measurableSet_retainedNextDate_ambient rate rewards C_star C_h u t control0 hq)
  have hAfterInt := expBacklogAfter_integrable rate rewards C_star C_h u t control0 hq a
  have hBeforeInt := expBacklogBefore_integrable rate rewards C_star C_h u t control0 a
  have hplus : Integrable
      (fun z : Z => W z * expBacklogAfter rate rewards C_star C_h u t hq a z) ν :=
    hWInt.mul_bdd
      (measurable_expBacklogAfter rate rewards C_star C_h u t control0 hq a).aestronglyMeasurable
      hAfterBound
  have hminus : Integrable
      (fun z : Z => W z * expBacklogBefore rate rewards C_star C_h u t a z) ν :=
    hWInt.mul_bdd
      (measurable_expBacklogBefore rate rewards C_star C_h u t control0 a).aestronglyMeasurable
      hBeforeBound
  have hindicator : Integrable
      (fun z : Z => W z * retainedNextDateIndicator rate rewards C_star C_h u t hq z) ν :=
    hWInt.mul_bdd hIndicatorMeas.aestronglyMeasurable hIndicatorBound
  have hPull := condExp_mul_of_aestronglyMeasurable_left hWfield hplus hAfterInt
  have hCEweighted : Integrable
      (fun z : Z => W z * ν[expBacklogAfter rate rewards C_star C_h u t hq a | Fq] z) ν :=
    (integrable_condExp (μ := ν) (m := Fq)
      (f := fun z : Z => W z * expBacklogAfter rate rewards C_star C_h u t hq a z)).congr hPull
  have hpoint :
      (fun z : Z => W z * ν[expBacklogAfter rate rewards C_star C_h u t hq a | Fq] z) ≤ᵐ[ν]
        (fun z : Z => W z * (expBacklogBefore rate rewards C_star C_h u t a z +
          retainedNextDateIndicator rate rewards C_star C_h u t hq z)) := by
    filter_upwards [condExp_expBacklogAfter_le_expBacklogBefore_add_indicator
      rate rewards C_star C_h u t control0 hq a, hWnonneg] with z hce hW
    exact mul_le_mul_of_nonneg_left hce hW
  have hright : Integrable
      (fun z : Z => W z * (expBacklogBefore rate rewards C_star C_h u t a z +
        retainedNextDateIndicator rate rewards C_star C_h u t hq z)) ν := by
    have hadd := hminus.add hindicator
    apply hadd.congr
    filter_upwards [] with z
    change (W z * expBacklogBefore rate rewards C_star C_h u t a z) +
        (W z * retainedNextDateIndicator rate rewards C_star C_h u t hq z) =
      W z * (expBacklogBefore rate rewards C_star C_h u t a z +
        retainedNextDateIndicator rate rewards C_star C_h u t hq z)
    rw [mul_add]
  have hdom :=
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
      rate rewards C_star C_h u t control0
  calc
    (∫ z : Z, W z * expBacklogAfter rate rewards C_star C_h u t hq a z ∂ν) =
        ∫ z : Z, W z * ν[expBacklogAfter rate rewards C_star C_h u t hq a | Fq] z ∂ν := by
      calc
        _ = ∫ z : Z,
            ν[(fun z : Z => W z * expBacklogAfter rate rewards C_star C_h u t hq a z) | Fq] z ∂ν :=
          (integral_condExp hdom).symm
        _ = _ := integral_congr_ae hPull
    _ ≤ ∫ z : Z, W z * (expBacklogBefore rate rewards C_star C_h u t a z +
        retainedNextDateIndicator rate rewards C_star C_h u t hq z) ∂ν :=
      integral_mono_ae hCEweighted hright hpoint
    _ = (∫ z : Z, W z * expBacklogBefore rate rewards C_star C_h u t a z ∂ν) +
        ∫ z : Z, W z * retainedNextDateIndicator rate rewards C_star C_h u t hq z ∂ν := by
      calc
        _ = ∫ z : Z,
            (W z * expBacklogBefore rate rewards C_star C_h u t a z) +
              (W z * retainedNextDateIndicator rate rewards C_star C_h u t hq z) ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with z
          rw [mul_add]
        _ = _ := integral_add hminus hindicator

private theorem measurableSet_of_nextPrior {H : Set Z}
    (hH : MeasurableSet[Fq] H) : MeasurableSet H := by
  rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_eq_comap
    rate rewards C_star C_h u t control0] at hH
  rcases hH with ⟨S, hS, hpre⟩
  rw [← hpre]
  exact hS.preimage
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextControlLaw.measurable_nextPriorObserver
      rate rewards C_star C_h u t control0)

/-- Set-integral form on every event in the exact next-prior field. The
retained-event charge is its measure under the original unnormalized source.
-/
theorem setIntegral_expBacklogAfter_le
    (hq : t.val + 1 < p.T) (a : Fin p.K) {H : Set Z}
    (hH : MeasurableSet[Fq] H) :
    (∫ z in H, expBacklogAfter rate rewards C_star C_h u t hq a z ∂ν) ≤
      (∫ z in H, expBacklogBefore rate rewards C_star C_h u t a z ∂ν) +
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (H ∩ retainedNextDate rate rewards C_star C_h u t hq) := by
  let W : Z → ℝ := Set.indicator H (fun _ : Z => (1 : ℝ))
  have hHambient := measurableSet_of_nextPrior rate rewards C_star C_h u t control0 hH
  have hWfield : AEStronglyMeasurable[Fq] W ν := by
    exact (Measurable.indicator
      (measurable_const : Measurable[Fq] (fun _ : Z => (1 : ℝ))) hH).aestronglyMeasurable
  have hWambient : Measurable W := by
    exact (measurable_const : Measurable (fun _ : Z => (1 : ℝ))).indicator hHambient
  have hWnonneg : 0 ≤ᵐ[ν] W := by
    filter_upwards [] with z
    by_cases hz : z ∈ H <;> simp [W, hz]
  have hWbound : ∀ᵐ z ∂ν, ‖W z‖ ≤ 1 := by
    filter_upwards [] with z
    by_cases hz : z ∈ H <;> simp [W, hz]
  have hWeighted := integral_mul_expBacklogAfter_le
    rate rewards C_star C_h u t control0 hq a (W := W)
    hWfield hWambient hWnonneg ⟨1, by norm_num, hWbound⟩
  have hWplus :
      (fun z : Z => W z * expBacklogAfter rate rewards C_star C_h u t hq a z) =
        Set.indicator H (fun z : Z =>
          expBacklogAfter rate rewards C_star C_h u t hq a z) := by
    funext z
    by_cases hz : z ∈ H <;> simp [W, hz]
  have hWminus :
      (fun z : Z => W z * expBacklogBefore rate rewards C_star C_h u t a z) =
        Set.indicator H (fun z : Z =>
          expBacklogBefore rate rewards C_star C_h u t a z) := by
    funext z
    by_cases hz : z ∈ H <;> simp [W, hz]
  have hWevent :
      (fun z : Z => W z * retainedNextDateIndicator rate rewards C_star C_h u t hq z) =
        Set.indicator H (retainedNextDateIndicator rate rewards C_star C_h u t hq) := by
    funext z
    by_cases hz : z ∈ H <;> simp [W, retainedNextDateIndicator, hz]
  have hGambient := measurableSet_retainedNextDate_ambient
    rate rewards C_star C_h u t control0 hq
  have hEventFunction :
      (fun z : Z => Set.indicator H
        (retainedNextDateIndicator rate rewards C_star C_h u t hq) z) =
        Set.indicator (H ∩ retainedNextDate rate rewards C_star C_h u t hq)
          (fun _ : Z => (1 : ℝ)) := by
    funext z
    by_cases hHz : z ∈ H
    · by_cases hGz : z ∈ retainedNextDate rate rewards C_star C_h u t hq <;>
        simp [retainedNextDateIndicator, hHz, hGz]
    · simp [hHz]
  have hEventMass :
      (∫ z in H, retainedNextDateIndicator rate rewards C_star C_h u t hq z ∂ν) =
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (H ∩ retainedNextDate rate rewards C_star C_h u t hq) := by
    calc
      _ = ∫ z : Z, Set.indicator H
          (retainedNextDateIndicator rate rewards C_star C_h u t hq) z ∂ν :=
        (integral_indicator hHambient).symm
      _ = ∫ z : Z, Set.indicator
          (H ∩ retainedNextDate rate rewards C_star C_h u t hq)
          (fun _ : Z => (1 : ℝ)) z ∂ν := by rw [hEventFunction]
      _ = (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
            (H ∩ retainedNextDate rate rewards C_star C_h u t hq) := by
        rw [integral_indicator_const (1 : ℝ) (hHambient.inter hGambient)]
        simp
  rw [hWplus, hWminus, hWevent, integral_indicator hHambient,
    integral_indicator hHambient, integral_indicator hHambient] at hWeighted
  rw [hEventMass] at hWeighted
  exact hWeighted

/-- The successful optional cell keeps the exact scalar, queue projection,
accepted histories, one-step full-prefix recursion, and physical dated join
from the same source constructor. -/
theorem nextCell_some_physical_run (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :
    backlogAfter rate rewards C_star C_h u t hq a z =
        ((RecordedQueueRun.step
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
            rate rewards C_star C_h u t z) c).registers a).2 /
          ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ) ∧
      expBacklogAfter rate rewards C_star C_h u t hq a z =
        Real.exp (beta *
          (((RecordedQueueRun.step
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c).registers a).2 /
            ((_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ))) ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z (t.val + 2) =
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z).map
          (fun cell => some
            (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) ++
          [some
            (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical c)] ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run
          (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
            rate rewards C_star C_h u t z ++ [c])) =
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step
            (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
              rate rewards C_star C_h u t z) c) ∧
      (RecordedQueueRun.run
        (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z ++ [c])).records =
        fun j =>
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
            rate rewards C_star C_h u t z).2.2 j ++
              [RecordedQueueRun.acceptedRecord
                (_root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentState
                  rate rewards C_star C_h u t z) c j] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [backlogAfter, hc]
  · simp [expBacklogAfter, backlogAfter, hc]
  · rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_next
      rate rewards C_star C_h u t z hq, hc]
    rfl
  · exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_fullPrefix
      rate rewards C_star C_h u t z c
  · exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_acceptedHistories
      rate rewards C_star C_h u t z c

/-- An actually absent optional cell preserves the prior scalar queue and
exponential and retains the producer's actual absent dated entry. -/
theorem nextCell_none_preserves_physical_prefix (hq : t.val + 1 < p.T)
    (a : Fin p.K) (z : Z)
    (hnone : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = none) :
    backlogAfter rate rewards C_star C_h u t hq a z =
        backlogBefore rate rewards C_star C_h u t a z ∧
      expBacklogAfter rate rewards C_star C_h u t hq a z =
        expBacklogBefore rate rewards C_star C_h u t a z ∧
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix
        rate rewards C_star C_h u t z (t.val + 2) =
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.currentCells
          rate rewards C_star C_h u t z).map
          (fun cell => some
            (_root_.Bandits.Support.ReferenceCompleteNumericalBranchObservation.encodeNumerical cell)) ++
          [none] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [backlogAfter, hnone]
  · simp [expBacklogAfter, backlogAfter, expBacklogBefore, hnone]
  · rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.rawJoinedPrefix_next
      rate rewards C_star C_h u t z hq, hnone]
    rfl

/-- Public scalar/readout identity for the same successful optional cell. -/
abbrev actual_nextScalar_present_run (hq : t.val + 1 < p.T) (a : Fin p.K)
    (z : Z) (c : RecordedQueueRun.RoundInput p.K)
    (hc : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextCell
      rate rewards C_star C_h u t z hq = some c) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextRecordingMoments.nextScalar_present_run
    rate rewards C_star C_h u t hq a z c hc

/-- Public one-date full-prefix queue recursion on the actual source. -/
abbrev actual_nextRun_fullPrefix (z : Z) (c : RecordedQueueRun.RoundInput p.K) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_fullPrefix
    rate rewards C_star C_h u t z c

/-- Public one-date accepted-history recursion on the actual source. -/
abbrev actual_nextRun_acceptedHistories (z : Z) (c : RecordedQueueRun.RoundInput p.K) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextRun_acceptedHistories
    rate rewards C_star C_h u t z c

/-- Public physical one-date prefix, including the actual absent dated-entry
branch when no optional numerical cell exists. -/
abbrev actual_nextDate_physical_prefix (z : Z) (hq : t.val + 1 < p.T) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.nextDate_physical_prefix
    rate rewards C_star C_h u t z hq

/-- At the terminal renewal date retain only the admitted physical-prefix
producer; this statement constructs no future date, action, or queue input. -/
abbrev terminal_physical_prefix (z : Z) (ht : t.val + 1 = p.T) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextPhysicalPrefix.terminal_physical_prefix
    rate rewards C_star C_h u t z ht

end Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep

end
