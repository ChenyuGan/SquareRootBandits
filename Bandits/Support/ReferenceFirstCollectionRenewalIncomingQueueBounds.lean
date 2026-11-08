/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments

import Mathlib.Tactic

/-!
# Actual first-renewal incoming queue envelopes

The queue readouts below use the actual second-source prefix run on its
original pair law. Every past source cell obtains its recording-rate floor
from its actual live or collection payload.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support
open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local notation "B" =>
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.Pair
    rate rewards C_star C_h u t
local notation "mu" =>
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw
    rate rewards C_star C_h u t
local notation "queue" => ReferenceFirstLaunchNumericalCell.queueParameters rate

local instance pairLawIsFinite : IsFiniteMeasure mu :=
  ReferenceFirstCollectionRenewalInstallationCoupling.pairLaw_finite
    rate rewards C_star C_h u t

def Bcap (_rewards : RewardTable p) (_C_star _C_h : ℝ) (_u _t : Fin p.T)
    (_control0 : TimeControl p) : ℝ := 1 / (32 * rate.eta.val)

def bMinus (_control0 : TimeControl p) (j : Fin p.K) (b : B) : ℝ :=
  ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).registers j).2 /
    (rate.n : ℝ)

def wMinus (_control0 : TimeControl p) (j : Fin p.K) (b : B) : ℝ :=
  RecordedQueueRun.scoreWeight queue (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2) j

def thetaMinus (control0 : TimeControl p) (j : Fin p.K) (b : B) : ℝ :=
  ProductSetLaw.theta p.m (fun i => wMinus rate rewards C_star C_h u t control0 i b) j

def VMinus (control0 : TimeControl p) (b : B) : ℝ :=
  ∑ j : Fin p.K,
    thetaMinus rate rewards C_star C_h u t control0 j b *
      bMinus rate rewards C_star C_h u t control0 j b ^ 2

private theorem beta_floor :
    32 * rate.eta.val ≤ CanonicalRecordingRates.beta p rate.eta.val := by
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  rw [CanonicalRecordingRates.beta]
  calc
    32 * rate.eta.val = (32 * rate.eta.val) * 1 := by ring
    _ ≤ (32 * rate.eta.val) * (CanonicalRecordingRates.L_stab p : ℝ) :=
      mul_le_mul_of_nonneg_left hL (le_of_lt (mul_pos (by norm_num) rate.eta.property))

private theorem pastCells_rate_lower_bound (b : B) :
    ∀ round ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t b.2,
      ∀ j : Fin p.K, 32 * rate.eta.val ≤ round.rate j := by
  intro round hround j
  have hparts := List.mem_append.mp (by simpa only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells] using hround)
  rcases hparts with hlive | hcollection
  · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hlive
    let z := b.2
    let hc := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.crossing rate rewards C_star C_h u t z
    let count := p.T - _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.start rate rewards C_star C_h u t z
    let hspan := _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.full_span rate rewards C_star C_h u t z
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
    exact le_trans (beta_floor rate)
      (sourceCell.selected.view.payload.beta_le_rate j)
  · obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hcollection
    obtain ⟨_, _, _, hcalls⟩ :=
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.actual_chronological_reconstruction rate rewards C_star C_h u t b.2
    obtain ⟨call, valid, _, hcell⟩ := hcalls ⟨i, by
      simpa only [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.collectionCells_length] using hi⟩
    rw [hget.symm, hcell]
    change 32 * rate.eta.val ≤ call.payload.rate j
    exact le_trans (beta_floor rate)
      (call.payload.beta_le_rate j)

/-- Every arm's incoming backlog is globally bounded by the stopped-queue
envelope, including after the first overflow update. -/
theorem bMinus_le_two_Bcap (j : Fin p.K) (b : B) :
    bMinus rate rewards C_star C_h u t control0 j b ≤
      2 * Bcap rate rewards C_star C_h u t control0 := by
  have h := StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
    queue (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t b.2)
    (pastCells_rate_lower_bound rate rewards C_star C_h u t b)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength rate rewards C_star C_h u t b.2) j
  have htake :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t b.2).take
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
          rate rewards C_star C_h u t b.2) =
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
          rate rewards C_star C_h u t b.2 := by
    apply List.take_of_length_le
    rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells_length]
  rw [htake] at h
  simpa [bMinus, Bcap, _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming, StoppedQueueBound.normalizedBacklog,
    ReferenceFirstLaunchNumericalCell.queueParameters] using h

/-- A strict-past no-overflow flag bounds the incoming backlog before the
current renewal update. -/
theorem bMinus_le_Bcap_of_noOverflow (j : Fin p.K) (b : B)
    (hfalse : (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming rate rewards C_star C_h u t b.2).overflow = false) :
    bMinus rate rewards C_star C_h u t control0 j b ≤
      Bcap rate rewards C_star C_h u t control0 := by
  have hlen :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t b.2).length ≤
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
        rate rewards C_star C_h u t b.2 := by
    rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells_length]
  have h := StoppedQueueBound.run_prefix_normalized_backlog_le_threshold_of_overflow_false
    queue (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells rate rewards C_star C_h u t b.2)
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength rate rewards C_star C_h u t b.2) j (by
      rw [List.take_of_length_le hlen]
      exact hfalse)
  have htake :
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t b.2).take
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastLength
          rate rewards C_star C_h u t b.2) =
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
          rate rewards C_star C_h u t b.2 :=
    List.take_of_length_le hlen
  rw [htake] at h
  simpa [bMinus, Bcap, _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming, StoppedQueueBound.normalizedBacklog,
    ReferenceFirstLaunchNumericalCell.queueParameters] using h

/-- The actual incoming inclusion marginals sum to the original slow-set
cardinality. -/
theorem sum_thetaMinus (b : B) :
    (∑ j : Fin p.K, thetaMinus rate rewards C_star C_h u t control0 j b) =
      (p.m : ℝ) := by
  unfold thetaMinus
  apply ProductSetLaw.sum_theta_eq_card
  · exact Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)
  · exact p.m_lt_K
  · intro j
    unfold wMinus
    change 0 < ScoreWeights.scoreWeight
      (1 + 1 / (ConstructorDimensions.D p : ℝ))
      ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).registers j).1
    exact ScoreWeights.scoreWeight_pos
      (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _

/-- Normalized queue readouts are nonnegative on the whole pair carrier. -/
theorem bMinus_nonneg (j : Fin p.K) (b : B) :
    0 ≤ bMinus rate rewards C_star C_h u t control0 j b := by
  unfold bMinus
  exact div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr
      (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos).le

private theorem wMinus_pos (j : Fin p.K) (b : B) :
    0 < wMinus rate rewards C_star C_h u t control0 j b := by
  unfold wMinus RecordedQueueRun.scoreWeight
  exact ScoreWeights.scoreWeight_pos
    (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _

/-- Every incoming product-set marginal remains between zero and one. -/
theorem thetaMinus_bounds (j : Fin p.K) (b : B) :
    0 ≤ thetaMinus rate rewards C_star C_h u t control0 j b ∧
    thetaMinus rate rewards C_star C_h u t control0 j b ≤ 1 := by
  constructor
  · exact (ProductSetLaw.theta_pos
      (fun i => wMinus rate rewards C_star C_h u t control0 i b) j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (fun i => wMinus_pos rate rewards C_star C_h u t control0 i b)).le
  · exact (ProductSetLaw.theta_lt_one
      (fun i => wMinus rate rewards C_star C_h u t control0 i b) j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (fun i => wMinus_pos rate rewards C_star C_h u t control0 i b)).le

/-- The incoming quadratic energy is bounded by the queue cap and the full
`m`-arm inclusion mass. -/
theorem VMinus_bounds (b : B) :
    0 ≤ VMinus rate rewards C_star C_h u t control0 b ∧
    VMinus rate rewards C_star C_h u t control0 b ≤
      (p.m : ℝ) * (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by
  have hcap : 0 ≤ 2 * Bcap rate rewards C_star C_h u t control0 := by
    unfold Bcap
    exact mul_nonneg (by norm_num)
      (le_of_lt (one_div_pos.mpr
        (mul_pos (by norm_num) rate.eta.property)))
  constructor
  · unfold VMinus
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (thetaMinus_bounds rate rewards C_star C_h u t control0 j b).1
      (sq_nonneg _)
  · calc
      VMinus rate rewards C_star C_h u t control0 b ≤
          ∑ j : Fin p.K,
            thetaMinus rate rewards C_star C_h u t control0 j b *
              (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by
        unfold VMinus
        apply Finset.sum_le_sum
        intro j hj
        have htheta := thetaMinus_bounds rate rewards C_star C_h u t control0 j b
        have hback := bMinus_le_two_Bcap rate rewards C_star C_h u t control0 j b
        have hback0 := bMinus_nonneg rate rewards C_star C_h u t control0 j b
        have hdiff :
            0 ≤ 2 * Bcap rate rewards C_star C_h u t control0 -
              bMinus rate rewards C_star C_h u t control0 j b :=
          sub_nonneg.mpr hback
        have hsum :
            0 ≤ 2 * Bcap rate rewards C_star C_h u t control0 +
              bMinus rate rewards C_star C_h u t control0 j b :=
          add_nonneg hcap hback0
        have hsq :
            bMinus rate rewards C_star C_h u t control0 j b ^ 2 ≤
              (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by
          nlinarith [mul_nonneg
            hdiff hsum]
        calc
          _ ≤ thetaMinus rate rewards C_star C_h u t control0 j b *
              (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq htheta.1
          _ = _ := rfl
      _ = (∑ j : Fin p.K,
            thetaMinus rate rewards C_star C_h u t control0 j b) *
              (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by
        rw [Finset.sum_mul]
      _ = (p.m : ℝ) *
            (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by
        rw [sum_thetaMinus]

def backlogFromRegisters (j : Fin p.K)
    (registers : Fin p.K → ℕ × ℕ) : ℝ :=
  (registers j).2 / (rate.n : ℝ)

def weightFromRegisters (j : Fin p.K)
    (registers : Fin p.K → ℕ × ℕ) : ℝ :=
  ScoreWeights.scoreWeight
    (1 + 1 / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ))
    (registers j).1

def thetaFromRegisters (j : Fin p.K)
    (registers : Fin p.K → ℕ × ℕ) : ℝ :=
  ProductSetLaw.theta p.m (fun i => weightFromRegisters rate i registers) j

def energyFromRegisters (registers : Fin p.K → ℕ × ℕ) : ℝ :=
  ∑ j : Fin p.K,
    thetaFromRegisters rate j registers * backlogFromRegisters rate j registers ^ 2

def incomingRegisters (b : B) : Fin p.K → ℕ × ℕ :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
    rate rewards C_star C_h u t b.2).registers

def retainedRegisters (b : B) : Fin p.K → ℕ × ℕ :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
    rate rewards C_star C_h u t control0 b).registers

def bMinusRetained (j : Fin p.K) (b : B) : ℝ :=
  backlogFromRegisters rate j (retainedRegisters rate rewards C_star C_h u t control0 b)

def wMinusRetained (j : Fin p.K) (b : B) : ℝ :=
  weightFromRegisters rate j (retainedRegisters rate rewards C_star C_h u t control0 b)

def thetaMinusRetained (j : Fin p.K) (b : B) : ℝ :=
  thetaFromRegisters rate j (retainedRegisters rate rewards C_star C_h u t control0 b)

def VMinusRetained (b : B) : ℝ :=
  energyFromRegisters rate
    (retainedRegisters rate rewards C_star C_h u t control0 b)

private theorem measurable_incomingRegisters :
    Measurable (incomingRegisters rate rewards C_star C_h u t) := by
  exact measurable_fst.comp
    ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
      rate rewards C_star C_h u t).comp measurable_snd)

private theorem measurable_retainedRegisters :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (retainedRegisters rate rewards C_star C_h u t control0) := by
  exact _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncoming_registers
    rate rewards C_star C_h u t control0

/-- The complete incoming register, overflow, and accepted-record readout is
ambient Borel on the original finite pair carrier. -/
theorem measurable_actualIncomingReadout :
    Measurable (fun b : B =>
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout
        rate rewards C_star C_h u t b.2) :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_incomingReadout
    rate rewards C_star C_h u t).comp
      (measurable_snd : Measurable (fun b : B => b.2))

/-- The retained incoming register/overflow/record representatives use the
exact original retained comap field. -/
theorem measurable_retainedIncomingReadout :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B =>
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
            rate rewards C_star C_h u t control0 b)) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncomingReadout
    rate rewards C_star C_h u t control0

/-- The retained incoming queue registers are pointwise measurable on the
existing retained-control comap field. -/
theorem measurable_retainedIncoming_registers :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B =>
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
          rate rewards C_star C_h u t control0 b).registers) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncoming_registers
    rate rewards C_star C_h u t control0

/-- The retained incoming overflow flag is pointwise measurable on the same
retained-control comap field. -/
theorem measurable_retainedIncoming_overflow :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B =>
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
          rate rewards C_star C_h u t control0 b).overflow) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncoming_overflow
    rate rewards C_star C_h u t control0

/-- The retained accepted-record histories are pointwise measurable on the
same retained-control comap field. -/
theorem measurable_retainedIncoming_records :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B =>
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming
          rate rewards C_star C_h u t control0 b).records) :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.measurable_retainedIncoming_records
    rate rewards C_star C_h u t control0

theorem measurable_bMinus (j : Fin p.K) :
    Measurable (fun b : B => bMinus rate rewards C_star C_h u t control0 j b) := by
  have hmap : Measurable (backlogFromRegisters rate j) := measurable_of_countable _
  have hm := hmap.comp (measurable_incomingRegisters rate rewards C_star C_h u t)
  have hfun : (backlogFromRegisters rate j) ∘ incomingRegisters rate rewards C_star C_h u t =
      fun b : B => bMinus rate rewards C_star C_h u t control0 j b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_wMinus (j : Fin p.K) :
    Measurable (fun b : B => wMinus rate rewards C_star C_h u t control0 j b) := by
  have hmap : Measurable (weightFromRegisters rate j) := measurable_of_countable _
  have hm := hmap.comp (measurable_incomingRegisters rate rewards C_star C_h u t)
  have hfun : (weightFromRegisters rate j) ∘ incomingRegisters rate rewards C_star C_h u t =
      fun b : B => wMinus rate rewards C_star C_h u t control0 j b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_thetaMinus (j : Fin p.K) :
    Measurable (fun b : B => thetaMinus rate rewards C_star C_h u t control0 j b) := by
  have hmap : Measurable (thetaFromRegisters rate j) := measurable_of_countable _
  have hm := hmap.comp (measurable_incomingRegisters rate rewards C_star C_h u t)
  have hfun : (thetaFromRegisters rate j) ∘ incomingRegisters rate rewards C_star C_h u t =
      fun b : B => thetaMinus rate rewards C_star C_h u t control0 j b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_VMinus :
    Measurable (fun b : B => VMinus rate rewards C_star C_h u t control0 b) := by
  have hmap : Measurable (energyFromRegisters rate) := measurable_of_countable _
  have hm := hmap.comp (measurable_incomingRegisters rate rewards C_star C_h u t)
  have hfun : (energyFromRegisters rate) ∘ incomingRegisters rate rewards C_star C_h u t =
      fun b : B => VMinus rate rewards C_star C_h u t control0 b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_bMinusRetained (j : Fin p.K) :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B => bMinusRetained rate rewards C_star C_h u t control0 j b) := by
  have hmap : Measurable (backlogFromRegisters rate j) := measurable_of_countable _
  have hm := hmap.comp (measurable_retainedRegisters rate rewards C_star C_h u t control0)
  have hfun : (backlogFromRegisters rate j) ∘
      retainedRegisters rate rewards C_star C_h u t control0 =
        fun b : B => bMinusRetained rate rewards C_star C_h u t control0 j b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_wMinusRetained (j : Fin p.K) :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B => wMinusRetained rate rewards C_star C_h u t control0 j b) := by
  have hmap : Measurable (weightFromRegisters rate j) := measurable_of_countable _
  have hm := hmap.comp (measurable_retainedRegisters rate rewards C_star C_h u t control0)
  have hfun : (weightFromRegisters rate j) ∘
      retainedRegisters rate rewards C_star C_h u t control0 =
        fun b : B => wMinusRetained rate rewards C_star C_h u t control0 j b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_thetaMinusRetained (j : Fin p.K) :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B => thetaMinusRetained rate rewards C_star C_h u t control0 j b) := by
  have hmap : Measurable (thetaFromRegisters rate j) := measurable_of_countable _
  have hm := hmap.comp (measurable_retainedRegisters rate rewards C_star C_h u t control0)
  have hfun : (thetaFromRegisters rate j) ∘
      retainedRegisters rate rewards C_star C_h u t control0 =
        fun b : B => thetaMinusRetained rate rewards C_star C_h u t control0 j b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

theorem measurable_VMinusRetained :
    Measurable[MeasurableSpace.comap
      (ReferenceFirstCollectionRenewalControlFactor.retainedControlCoordinates
        rate rewards C_star C_h u t control0)
      (inferInstance : MeasurableSpace
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.RetainedCoordinates
          p))]
      (fun b : B => VMinusRetained rate rewards C_star C_h u t control0 b) := by
  have hmap : Measurable (energyFromRegisters rate) := measurable_of_countable _
  have hm := hmap.comp (measurable_retainedRegisters rate rewards C_star C_h u t control0)
  have hfun : (energyFromRegisters rate) ∘
      retainedRegisters rate rewards C_star C_h u t control0 =
        fun b : B => VMinusRetained rate rewards C_star C_h u t control0 b := by
    funext b
    rfl
  rw [← hfun]
  exact hm

private theorem ae_incomingRegisters_eq_retained :
    ∀ᵐ b : B ∂mu,
      incomingRegisters rate rewards C_star C_h u t b =
        retainedRegisters rate rewards C_star C_h u t control0 b := by
  filter_upwards [_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.ae_incomingReadout_eq_retained
    rate rewards C_star C_h u t control0] with b hb
  simpa [incomingRegisters, retainedRegisters,
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout,
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.retainedIncoming] using
      congrArg Prod.fst hb

/-- The incoming normalized backlog is AE equal to its pointwise retained
representative on the same unnormalized pair law. -/
theorem ae_bMinus_eq_retained (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      bMinus rate rewards C_star C_h u t control0 j b =
        bMinusRetained rate rewards C_star C_h u t control0 j b := by
  filter_upwards [ae_incomingRegisters_eq_retained rate rewards C_star C_h u t control0]
    with b hb
  change ((incomingRegisters rate rewards C_star C_h u t b j).2 : ℝ) /
      (rate.n : ℝ) =
    ((retainedRegisters rate rewards C_star C_h u t control0 b j).2 : ℝ) /
      (rate.n : ℝ)
  have hback :
      (incomingRegisters rate rewards C_star C_h u t b j).2 =
        (retainedRegisters rate rewards C_star C_h u t control0 b j).2 :=
    congrArg (fun registers : Fin p.K → ℕ × ℕ => (registers j).2) hb
  rw [hback]

theorem ae_wMinus_eq_retained (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      wMinus rate rewards C_star C_h u t control0 j b =
        wMinusRetained rate rewards C_star C_h u t control0 j b := by
  filter_upwards [ae_incomingRegisters_eq_retained rate rewards C_star C_h u t control0]
    with b hb
  change weightFromRegisters rate j (incomingRegisters rate rewards C_star C_h u t b) =
    weightFromRegisters rate j (retainedRegisters rate rewards C_star C_h u t control0 b)
  rw [hb]

theorem ae_thetaMinus_eq_retained (j : Fin p.K) :
    ∀ᵐ b : B ∂mu,
      thetaMinus rate rewards C_star C_h u t control0 j b =
        thetaMinusRetained rate rewards C_star C_h u t control0 j b := by
  filter_upwards [ae_incomingRegisters_eq_retained rate rewards C_star C_h u t control0]
    with b hb
  change thetaFromRegisters rate j (incomingRegisters rate rewards C_star C_h u t b) =
    thetaFromRegisters rate j (retainedRegisters rate rewards C_star C_h u t control0 b)
  rw [hb]

theorem ae_VMinus_eq_retained :
    ∀ᵐ b : B ∂mu,
      VMinus rate rewards C_star C_h u t control0 b =
        VMinusRetained rate rewards C_star C_h u t control0 b := by
  filter_upwards [ae_incomingRegisters_eq_retained rate rewards C_star C_h u t control0]
    with b hb
  change energyFromRegisters rate (incomingRegisters rate rewards C_star C_h u t b) =
    energyFromRegisters rate (retainedRegisters rate rewards C_star C_h u t control0 b)
  rw [hb]

private theorem queueScoreBase_eq_sourceWeightBase :
    1 + 1 / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ) =
      AssignmentScoreReconstruction.sourceWeightBase p := by
  simp [ReferenceFirstLaunchNumericalCell.queueParameters,
    AssignmentScoreReconstruction.sourceWeightBase]

/-- On the existing current-anchor feasible branch, the actual incoming
weight is the same renewal anchor supplied by the public recorder identity. -/
theorem ae_wMinus_eq_renewalAnchor :
    ∀ᵐ b : B ∂mu,
      b ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0 →
      ∀ j : Fin p.K,
        wMinus rate rewards C_star C_h u t control0 j b =
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.v
            rate rewards C_star C_h u t b j := by
  filter_upwards [_root_.Bandits.Support.ReferenceFirstCollectionRenewalAcceptedComplementMoments.ae_actual_recorder_acceptedRecord_identity
    rate rewards C_star C_h u t control0]
    with b hidentity
  rcases hidentity with ⟨d, recording, _, _, hanchor, _, _, _, _, hregisters, _⟩
  intro hG j
  have hscore :
      ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
        rate rewards C_star C_h u t b.2).registers j).1 =
        AssignmentScoreReconstruction.sourceScore d.out j :=
    congrArg Prod.fst (hregisters j hG).symm
  calc
    wMinus rate rewards C_star C_h u t control0 j b =
        ScoreWeights.scoreWeight
          (1 + 1 / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ))
          ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming
            rate rewards C_star C_h u t b.2).registers j).1 := rfl
    _ = ScoreWeights.scoreWeight
          (1 + 1 / ((ReferenceFirstLaunchNumericalCell.queueParameters rate).D : ℝ))
          (AssignmentScoreReconstruction.sourceScore d.out j) := by rw [hscore]
    _ = ScoreWeights.scoreWeight (AssignmentScoreReconstruction.sourceWeightBase p)
          (AssignmentScoreReconstruction.sourceScore d.out j) := by
      rw [queueScoreBase_eq_sourceWeightBase rate]
    _ = AssignmentScoreReconstruction.currentWeight d.out j := rfl
    _ = _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.v
          rate rewards C_star C_h u t b j := (congrFun hanchor j).symm

/-- The actual renewal-anchor vector is strictly positive by the successful
renewal parameter specification. -/
theorem renewalAnchor_pos (b : B) (j : Fin p.K) :
    0 < _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.v
      rate rewards C_star C_h u t b j :=
  (_root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewal_parameter_spec
    rate rewards C_star C_h u t b.1.1).1 j

/-- The canonical base rate is below every actual renewed recording rate. -/
theorem beta_le_actualRenewalRate (b : B) (j : Fin p.K) :
    CanonicalRecordingRates.beta p rate.eta.val ≤
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.xi
        rate rewards C_star C_h u t b j :=
  CanonicalRecordingRates.beta_le_xi p rate.eta.property
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.v
      rate rewards C_star C_h u t b) j

/-- The actual renewed recording rates retain the full `32 η` floor. -/
theorem thirtyTwo_mul_eta_le_actualRenewalRate (b : B) (j : Fin p.K) :
    32 * rate.eta.val ≤
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.xi
        rate rewards C_star C_h u t b j :=
  CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p rate.eta.property
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.v
      rate rewards C_star C_h u t b) j

/-- On the same original pair law, the incoming product-set marginals divided
by the actual renewal rates obey the manuscript's instantaneous `R` bound on
the current-anchor feasible branch. -/
theorem ae_sum_thetaMinus_div_actualRenewalRate_le_R :
    ∀ᵐ b : B ∂mu,
      b ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueuePrefix.G_R
        rate rewards C_star C_h u t control0 →
      (∑ j : Fin p.K,
        thetaMinus rate rewards C_star C_h u t control0 j b /
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.xi
            rate rewards C_star C_h u t b j) ≤ CanonicalRecordingRates.R p := by
  filter_upwards [ae_wMinus_eq_renewalAnchor rate rewards C_star C_h u t control0]
    with b hweight
  intro hG
  let anchor := _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.v
    rate rewards C_star C_h u t b
  have htheta (j : Fin p.K) :
      thetaMinus rate rewards C_star C_h u t control0 j b =
        ProductSetLaw.theta p.m anchor j := by
    unfold thetaMinus
    congr 1
    funext i
    exact hweight hG i
  have hsum := CanonicalRecordingRates.sum_theta_div_xi_le_R p
    rate.eta.property anchor anchor
    (fun j => renewalAnchor_pos rate rewards C_star C_h u t b j)
    (fun j => ⟨le_rfl, by linarith [renewalAnchor_pos rate rewards C_star C_h u t b j]⟩)
  calc
    (∑ j : Fin p.K,
        thetaMinus rate rewards C_star C_h u t control0 j b /
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalComplementMoments.xi
            rate rewards C_star C_h u t b j) =
        ∑ j : Fin p.K,
          ProductSetLaw.theta p.m anchor j /
            CanonicalRecordingRates.xi p rate.eta.val anchor j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [htheta j]
      rfl
    _ ≤ CanonicalRecordingRates.R p := hsum

private theorem integrable_of_norm_le_const {f : B → ℝ} (hf : Measurable f)
    (C : ℝ) (hbound : ∀ b, ‖f b‖ ≤ C) : Integrable f mu := by
  have hconst : Integrable (fun _ : B => C) mu := integrable_const C
  refine hconst.mono' hf.aestronglyMeasurable ?_
  filter_upwards [] with b
  simpa using hbound b

/-- The actual normalized incoming backlogs are integrable on the finite,
possibly zero, original pair law. -/
theorem integrable_bMinus (j : Fin p.K) :
    Integrable (fun b : B => bMinus rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_norm_le_const rate rewards C_star C_h u t
    (measurable_bMinus rate rewards C_star C_h u t control0 j)
    (2 * Bcap rate rewards C_star C_h u t control0)
  intro b
  have hb := bMinus_le_two_Bcap rate rewards C_star C_h u t control0 j b
  have hnonneg := bMinus_nonneg rate rewards C_star C_h u t control0 j b
  rw [Real.norm_of_nonneg hnonneg]
  exact hb

/-- Each actual incoming inclusion marginal is integrable on the same law. -/
theorem integrable_thetaMinus (j : Fin p.K) :
    Integrable (fun b : B => thetaMinus rate rewards C_star C_h u t control0 j b) mu := by
  apply integrable_of_norm_le_const rate rewards C_star C_h u t
    (measurable_thetaMinus rate rewards C_star C_h u t control0 j) 1
  intro b
  have hb := thetaMinus_bounds rate rewards C_star C_h u t control0 j b
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

/-- The actual incoming quadratic energy is integrable by its full-arm
pointwise envelope. -/
theorem integrable_VMinus :
    Integrable (fun b : B => VMinus rate rewards C_star C_h u t control0 b) mu := by
  apply integrable_of_norm_le_const rate rewards C_star C_h u t
    (measurable_VMinus rate rewards C_star C_h u t control0)
    ((p.m : ℝ) * (2 * Bcap rate rewards C_star C_h u t control0) ^ 2)
  intro b
  have hb := VMinus_bounds rate rewards C_star C_h u t control0 b
  rw [Real.norm_of_nonneg hb.1]
  exact hb.2

/-- Each summand used in conditional energy pull-out is bounded and
integrable; the marginal is kept as its actual incoming product-set weight. -/
theorem integrable_incomingEnergyTerm (j : Fin p.K) :
    Integrable
      (fun b : B => thetaMinus rate rewards C_star C_h u t control0 j b *
        bMinus rate rewards C_star C_h u t control0 j b ^ 2) mu := by
  let f : B → ℝ := fun b =>
    thetaMinus rate rewards C_star C_h u t control0 j b *
      bMinus rate rewards C_star C_h u t control0 j b ^ 2
  have hf : Measurable f := by
    exact (measurable_thetaMinus rate rewards C_star C_h u t control0 j).mul
      ((measurable_bMinus rate rewards C_star C_h u t control0 j).pow_const 2)
  apply integrable_of_norm_le_const rate rewards C_star C_h u t hf
    ((2 * Bcap rate rewards C_star C_h u t control0) ^ 2)
  intro b
  have htheta := thetaMinus_bounds rate rewards C_star C_h u t control0 j b
  have hback := bMinus_le_two_Bcap rate rewards C_star C_h u t control0 j b
  have hback0 := bMinus_nonneg rate rewards C_star C_h u t control0 j b
  have hcap : 0 ≤ 2 * Bcap rate rewards C_star C_h u t control0 := by
    unfold Bcap
    exact mul_nonneg (by norm_num)
      (le_of_lt (one_div_pos.mpr
        (mul_pos (by norm_num) rate.eta.property)))
  have hsq :
      bMinus rate rewards C_star C_h u t control0 j b ^ 2 ≤
        (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by
    nlinarith [mul_nonneg
      (sub_nonneg.mpr hback)
      (add_nonneg hcap hback0)]
  rw [Real.norm_of_nonneg (mul_nonneg htheta.1 (sq_nonneg _))]
  calc
    thetaMinus rate rewards C_star C_h u t control0 j b *
        bMinus rate rewards C_star C_h u t control0 j b ^ 2 ≤
        1 * (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 :=
      mul_le_mul htheta.2 hsq (sq_nonneg _) (by positivity)
    _ = (2 * Bcap rate rewards C_star C_h u t control0) ^ 2 := by ring

end Bandits.Support.ReferenceFirstCollectionRenewalIncomingQueueBounds

end
