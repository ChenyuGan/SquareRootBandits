/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalConditionalWeightedDrift
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureExponentialQueueStep

import Mathlib.Tactic

/-!
# Future-date weighted queue energy on the first-renewal source

The energy readouts use the same actual optional prefix run before and after
one supported future cell. The weighted drift is derived on the original,
possibly zero, renewal-source measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MeasureTheory
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureWeightedEnergyStep

open ReferenceFirstCollectionRenewalFutureNumericalPrefix
open ReferenceFirstCollectionRenewalFutureExponentialQueueStep
open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureQueueReadout
open ReferenceFirstCollectionRenewalFutureExponentialIncrement
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureRecordingLaw
open ReferenceFirstCollectionRenewalFutureFirstReplacementView
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalIncomingQueueBounds
open ReferenceFirstCollectionRenewalIncomingQueueMeasurability
open ReferenceSourcePrefixHistoryFiltration

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
  (control0 : ContinuousLearningRows.TimeControl p)
  (q : Fin p.T) (hfuture : t.val + 1 < q.val)

local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "Q" => _root_.Bandits.Support.ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "β" => CanonicalRecordingRates.beta p rate.eta.val
local notation "Bcap" => 1 / (32 * rate.eta.val)
local notation "Sq" => ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
  rate rewards C_star C_h u t q hfuture
local notation "Fq" => ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
  rate rewards C_star C_h u t control0 q
local notation "Gq" => ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
  rate rewards C_star C_h u t q hfuture

private abbrev FuturePrefixStateReadout (K : ℕ) :=
  (Fin K → ℕ × ℕ) × (Bool × (Fin K → List (Bool × ℕ)))

/-- The incoming register marginal localized to the actual shared future support. -/
def futureThetaMinus (j : Fin p.K) : Z → ℝ :=
  (Sq).indicator (fun z =>
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t q.val z).elim 0
      (fun r => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j r.1))

/-- The incoming normalized backlog localized to the same actual support. -/
def futureBacklogMinus (j : Fin p.K) : Z → ℝ :=
  (Sq).indicator (fun z =>
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t q.val z).elim 0
      (fun r => ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
        rate j r.1))

/-- The post-cell register marginal, read from the actual adjacent optional prefix. -/
def futureThetaPlus (j : Fin p.K) : Z → ℝ :=
  (Sq).indicator (fun z =>
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z).elim 0
      (fun r => ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j r.1))

/-- The post-cell normalized backlog, read from that same actual prefix. -/
def futureBacklogPlus (j : Fin p.K) : Z → ℝ :=
  (Sq).indicator (fun z =>
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z).elim 0
      (fun r => ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
        rate j r.1))

/-- The incoming weighted quadratic energy; absent optional readouts contribute zero. -/
def futureWeightedEnergyMinus : Z → ℝ :=
  (Sq).indicator (fun z =>
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t q.val z).elim 0
      (fun r => ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate r.1))

/-- The energy after the literal adjacent prefix readout, on the original support. -/
def futureWeightedEnergyPlus : Z → ℝ :=
  (Sq).indicator (fun z =>
    (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z).elim 0
      (fun r => ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate r.1))

/-- The incoming weighted backlog appearing in the conditional drift. -/
def futureWeightedBacklog : Z → ℝ :=
  ∑ j : Fin p.K,
    futureThetaMinus rate rewards C_star C_h u t q hfuture j *
      futureBacklogMinus rate rewards C_star C_h u t q hfuture j

/-- The literal current-rate charge, using the same masked register marginals. -/
def futureRecordingCost (z : Z) : ℝ :=
  match ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture with
  | some (_, xi) =>
      ∑ j : Fin p.K,
        futureThetaMinus rate rewards C_star C_h u t q hfuture j z / xi j
  | none => 0

local notation "θ" => futureThetaMinus rate rewards C_star C_h u t q hfuture
local notation "b" => futureBacklogMinus rate rewards C_star C_h u t q hfuture
local notation "a" => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
  rate rewards C_star C_h u t q hfuture
local notation "M₁" => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
  rate rewards C_star C_h u t q hfuture
local notation "M₂" => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentTwo
  rate rewards C_star C_h u t q hfuture
local notation "Vminus" => futureWeightedEnergyMinus rate rewards C_star C_h u t q hfuture
local notation "Vplus" => futureWeightedEnergyPlus rate rewards C_star C_h u t q hfuture

local notation "θplus" => futureThetaPlus rate rewards C_star C_h u t q hfuture
local notation "bplus" => futureBacklogPlus rate rewards C_star C_h u t q hfuture

private theorem measurable_option_elim {X A B : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace B] (f : X → Option A) (hf : Measurable f)
    (g : A → B) (hg : Measurable g) (c : B) :
    Measurable (fun x => (f x).elim c g) := by
  let e := Equiv.optionEquivSumPUnit A
  have hencode : Measurable (fun x => e (f x)) :=
    (comap_measurable e).comp hf
  have hsum : Measurable (Sum.elim g (fun _ : PUnit => c)) :=
    hg.sumElim measurable_const
  have heq : (fun x => (f x).elim c g) =
      fun x => Sum.elim g (fun _ : PUnit => c) (e (f x)) := by
    funext x
    cases f x <;> rfl
  rw [heq]
  exact hsum.comp hencode

local notation "B" => futureWeightedBacklog rate rewards C_star C_h u t q hfuture
local notation "C" => futureRecordingCost rate rewards C_star C_h u t q hfuture

private def futureParameterRate (j : Fin p.K) (z : Z) : ℝ :=
  (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
    rate rewards C_star C_h u t z q hfuture).elim 1 (fun par => par.2 j)

private abbrev futureParametersPresent (z : Z) : Bool :=
  (ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
    rate rewards C_star C_h u t z q hfuture).elim false (fun _ => true)

private theorem measurable_futureParameterRate (j : Fin p.K) :
    Measurable[Fq] (futureParameterRate rate rewards C_star C_h u t q hfuture j) := by
  let : MeasurableSpace Z := Fq
  have hp := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
    rate rewards C_star C_h u t control0 q hfuture
  have hg : Measurable (fun par : Bool × (Fin p.K → ℝ) => par.2 j) :=
    (measurable_pi_apply j).comp measurable_snd
  exact measurable_option_elim _ hp _ hg 1

private theorem measurable_futureParametersPresent :
    Measurable[Fq] (futureParametersPresent rate rewards C_star C_h u t q hfuture) := by
  let : MeasurableSpace Z := Fq
  have hp := ReferenceFirstCollectionRenewalFutureRecordingLaw.measurable_futureParameters
    rate rewards C_star C_h u t control0 q hfuture
  have hg : Measurable (fun _ : Bool × (Fin p.K → ℝ) => true) := measurable_const
  have hm := measurable_option_elim _ hp _ hg false
  simpa only [futureParametersPresent] using hm

private theorem registerWeight_pos (registers : Fin p.K → ℕ × ℕ)
    (j : Fin p.K) :
    ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
      rate j registers > 0 := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
  exact ScoreWeights.scoreWeight_pos
    (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))) _

private theorem registerTheta_bounds (registers : Fin p.K → ℕ × ℕ)
    (j : Fin p.K) :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j registers ∧
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j registers ≤ 1 := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
  constructor
  · exact (ProductSetLaw.theta_pos
      (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
        rate i registers) j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (registerWeight_pos rate registers)).le
  · exact (ProductSetLaw.theta_lt_one
      (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
        rate i registers) j
      (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
      (registerWeight_pos rate registers)).le

private theorem registerTheta_sum (registers : Fin p.K → ℕ × ℕ) :
    (∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
        rate j registers) = (p.m : ℝ) := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
  exact ProductSetLaw.sum_theta_eq_card
    (fun i => ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
      rate i registers)
    (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p)) p.m_lt_K
    (registerWeight_pos rate registers)

private theorem registerBacklog_nonneg (registers : Fin p.K → ℕ × ℕ)
    (j : Fin p.K) :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
      rate j registers := by
  unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
  exact div_nonneg (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr (ReferenceFirstLaunchNumericalCell.queueParameters rate).n_pos).le

private theorem registerEnergy_bounds (registers : Fin p.K → ℕ × ℕ)
    (hback : ∀ j : Fin p.K,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
          rate j registers ∈ Set.Icc (0 : ℝ) (2 * Bcap)) :
    0 ≤ ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate registers ∧
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        rate registers ≤ (p.m : ℝ) * (2 * Bcap) ^ 2 := by
  have hcap : 0 ≤ 2 * Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    positivity
  constructor
  · unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (registerTheta_bounds rate registers j).1 (sq_nonneg _)
  · calc
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
          rate registers ≤
        ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
              rate j registers * (2 * Bcap) ^ 2 := by
        unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
        apply Finset.sum_le_sum
        intro j hj
        have ht := registerTheta_bounds rate registers j
        have hb := (hback j).2
        have hb0 := (hback j).1
        have hsq :
            ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
                rate j registers ^ 2 ≤ (2 * Bcap) ^ 2 :=
          (sq_le_sq₀ hb0 hcap).2 hb
        exact mul_le_mul_of_nonneg_left hsq ht.1
      _ = (p.m : ℝ) * (2 * Bcap) ^ 2 := by
        rw [← Finset.sum_mul, registerTheta_sum rate registers]

private theorem exp_four_eta_bounds : Real.exp (4 * rate.eta.val) ≤ 1 + 8 * rate.eta.val := by
  have heta0 : 0 ≤ rate.eta.val := le_of_lt rate.eta.property
  have hx0 : 0 ≤ 4 * rate.eta.val := mul_nonneg (by norm_num) heta0
  have hsmall := CanonicalQueueProcess.four_mul_eta_le_one p
    rate.eta.property rate.sourceCap
  have hexp := RecordedPotentialStep.exp_le_one_add_add_sq hx0 hsmall
  have hsquare : (4 * rate.eta.val) ^ 2 ≤ 4 * rate.eta.val := by
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 4 * rate.eta.val)]
  nlinarith

private theorem futureScoreWeightBounds
    (state : RecordedQueueRun.RunState p.K)
    (cell : RecordedQueueRun.RoundInput p.K) (j : Fin p.K) :
    RecordedQueueRun.scoreWeight Q state j ≤
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) j ∧
    RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) j ≤
      Real.exp (4 * rate.eta.val) * RecordedQueueRun.scoreWeight Q state j := by
  have hbeforePos := RecordedPotentialStep.scoreWeight_pos Q state j
  have hratio :
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) j /
        RecordedQueueRun.scoreWeight Q state j =
      Real.exp (RecordedPotentialStep.potentialLambda Q *
        RecordedPotentialStep.servedEstimate Q state cell j) :=
    RecordedPotentialStep.step_scoreWeight_ratio_exp Q state cell j
  have hservice := RecordedPotentialStep.servedEstimate_nonneg Q state cell j
  have hservice4 := RecordedPotentialStep.servedEstimate_le_four Q state cell j
  have hlamPos := RecordedPotentialStep.potentialLambda_pos Q
  have hlamLe := RecordedPotentialStep.potentialLambda_le_eta Q
  have hlamLe' : RecordedPotentialStep.potentialLambda Q ≤ rate.eta.val := by
    simpa [ReferenceFirstLaunchNumericalCell.queueParameters] using hlamLe
  have harg :
      RecordedPotentialStep.potentialLambda Q *
        RecordedPotentialStep.servedEstimate Q state cell j ≤ 4 * rate.eta.val := by
    calc
      _ ≤ RecordedPotentialStep.potentialLambda Q * 4 :=
        mul_le_mul_of_nonneg_left hservice4 hlamPos.le
      _ = 4 * RecordedPotentialStep.potentialLambda Q := by ring
      _ ≤ 4 * rate.eta.val := by nlinarith
  have hratioLower : 1 ≤
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) j /
        RecordedQueueRun.scoreWeight Q state j := by
    rw [hratio]
    have hx := mul_nonneg hlamPos.le hservice
    have hlin := Real.add_one_le_exp
      (RecordedPotentialStep.potentialLambda Q *
        RecordedPotentialStep.servedEstimate Q state cell j)
    linarith
  have hratioUpper :
      RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) j /
        RecordedQueueRun.scoreWeight Q state j ≤ Real.exp (4 * rate.eta.val) := by
    rw [hratio]
    exact Real.exp_le_exp.mpr harg
  constructor
  · simpa using (le_div_iff₀ hbeforePos).mp hratioLower
  · exact (div_le_iff₀ hbeforePos).mp hratioUpper

private theorem futureThetaRegisters_upper
    (state : RecordedQueueRun.RunState p.K)
    (cell : RecordedQueueRun.RoundInput p.K) (j : Fin p.K) :
    ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j
        (RecordedQueueRun.step Q state cell).registers ≤
      (1 + 8 * rate.eta.val) *
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j
          state.registers := by
  let v := fun i : Fin p.K => RecordedQueueRun.scoreWeight Q state i
  let w := fun i : Fin p.K =>
    RecordedQueueRun.scoreWeight Q (RecordedQueueRun.step Q state cell) i
  let c := w j / v j
  let mid := Function.update w j (v j)
  have hweight (i : Fin p.K) : v i ≤ w i ∧ w i ≤ Real.exp (4 * rate.eta.val) * v i :=
    futureScoreWeightBounds rate state cell i
  have hvpos (i : Fin p.K) : 0 < v i := by
    dsimp [v]
    exact RecordedPotentialStep.scoreWeight_pos Q state i
  have hwpos (i : Fin p.K) : 0 < w i := by
    dsimp [w]
    exact RecordedPotentialStep.scoreWeight_pos Q (RecordedQueueRun.step Q state cell) i
  have hc1 : 1 ≤ c := by
    rw [le_div_iff₀ (hvpos j)]
    simpa [c, v, w] using (hweight j).1
  have hc2 : c ≤ Real.exp (4 * rate.eta.val) := by
    rw [div_le_iff₀ (hvpos j)]
    simpa [c, v, w] using (hweight j).2
  have hmidpos (i : Fin p.K) : 0 < mid i := by
    by_cases hi : i = j
    · subst i
      simp [mid, hvpos]
    · simp [mid, hi, hwpos]
  have hmidown : v j = mid j := by simp [mid]
  have hmidother (i : Fin p.K) (hij : i ≠ j) : v i ≤ mid i := by
    simpa [mid, hij] using (hweight i).1
  have hother := ProductMarginalStability.theta_antitone_of_other_coord_le
    v mid j p.two_le_m p.m_lt_K hvpos hmidpos hmidown hmidother
  have hvtheta : 0 ≤ ProductSetLaw.theta p.m v j := by
    exact (ProductSetLaw.theta_pos v j (Nat.zero_lt_of_lt (ConstructorDimensions.m_pos p))
      p.m_lt_K hvpos).le
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
  have htheta : ProductSetLaw.theta p.m w j ≤
      Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v j := by
    calc
      ProductSetLaw.theta p.m w j =
          ProductSetLaw.theta p.m (Function.update mid j (c * v j)) j := by rw [← hupdate]
      _ ≤ c * ProductSetLaw.theta p.m mid j := hscaled
      _ ≤ c * ProductSetLaw.theta p.m v j :=
        mul_le_mul_of_nonneg_left hother (by positivity [hc1])
      _ ≤ Real.exp (4 * rate.eta.val) * ProductSetLaw.theta p.m v j :=
        mul_le_mul_of_nonneg_right hc2 hvtheta
  have htheta2 : ProductSetLaw.theta p.m w j ≤
      (1 + 8 * rate.eta.val) * ProductSetLaw.theta p.m v j :=
    htheta.trans (mul_le_mul_of_nonneg_right (exp_four_eta_bounds rate)
      hvtheta)
  simpa [ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters,
    ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters,
    RecordedQueueRun.scoreWeight, v, w,
    ReferenceFirstLaunchNumericalCell.queueParameters] using htheta2

/-- On support, the optional prefix readouts are the actual original-prefix
run and its actual single-cell successor, with all register projections
retained literally. -/
theorem futureReadouts_same_run_step (z : Z) (hz : z ∈ Sq) :
    ∃ inputs : List (RecordedQueueRun.RoundInput p.K),
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
          rate rewards C_star C_h u t q z = some inputs ∧
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
          rate rewards C_star C_h u t z q hfuture = some c ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
          rate rewards C_star C_h u t q z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q inputs)) ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
          rate rewards C_star C_h u t (q.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c)) ∧
      Vminus z =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
          (RecordedQueueRun.run Q inputs).registers ∧
      Vplus z =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers ∧
      (∀ j : Fin p.K,
        θ j z =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j
            (RecordedQueueRun.run Q inputs).registers) ∧
      (∀ j : Fin p.K,
        b j z =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j
            (RecordedQueueRun.run Q inputs).registers) ∧
      (∀ j : Fin p.K,
        θplus j z =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j
            (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers) ∧
      (∀ j : Fin p.K,
        bplus j z =
          ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j
            (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers) := by
  have hK : 0 < p.K := Nat.lt_trans (ConstructorDimensions.m_pos p) p.m_lt_K
  let j0 : Fin p.K := ⟨0, hK⟩
  obtain ⟨inputs, c, hinputs, hcell, hbefore, hafter, _, _⟩ :=
    ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_present
      rate rewards C_star C_h u t q hfuture j0 z hz
  have hbefore' :
      ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q inputs)) := hbefore
  have hbeforeO :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t q.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q inputs)) := by
    simpa only [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using hbefore'
  refine ⟨inputs, c, hinputs, hcell, hbefore', hafter,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [futureWeightedEnergyMinus, hz, hbeforeO,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  · simp [futureWeightedEnergyPlus, hz, hafter,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  · intro j
    simp [futureThetaMinus, hz, hbeforeO,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  · intro j
    simp [futureBacklogMinus, hz, hbeforeO,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  · intro j
    simp [futureThetaPlus, hz, hafter,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
  · intro j
    simp [futureBacklogPlus, hz, hafter,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]

private theorem futureParameters_present_from_cell (z : Z)
    (c : RecordedQueueRun.RoundInput p.K)
    (hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some c) :
    ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (c.enabled, c.rate) := by
  have hr := ReferenceFirstCollectionRenewalFutureFirstReplacementView.firstReplacement_future_readout
    rate rewards C_star C_h u t z q hfuture
  cases hv : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecordingView
      rate rewards C_star C_h u t z q hfuture with
  | none =>
      rw [hv] at hr
      simp only at hr
      have hbad : (some c : Option (RecordedQueueRun.RoundInput p.K)) = none :=
        hc.symm.trans hr.2
      cases hbad
  | some data =>
      rcases data with ⟨parameters, view, code⟩
      rw [hv] at hr
      obtain ⟨cell, snapshot, valid, hcell, hparameters, hrate, _, _, _⟩ := hr
      have hcell_eq : cell = c := Option.some.inj (hcell.symm.trans hc)
      have hparameters' : parameters = some (c.enabled, c.rate) := by
        rw [← hcell_eq]
        exact hparameters
      simp [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters,
        hv, hparameters']

private theorem futureCell_present_of_support (z : Z) (hz : z ∈ Sq) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z q hfuture = some c := by
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
    ⟨_, c, _, hc, _, _, _, _, _, _, _, _⟩
  exact ⟨c, hc⟩

theorem futureBacklogMinus_eq_readout (z : Z) (hz : z ∈ Sq) (j : Fin p.K) :
    b j z =
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
        rate rewards C_star C_h u t q hfuture j z := by
  obtain ⟨inputs, c, hinputs, hcell, hbefore, _, hback, _⟩ :=
    ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_present
      rate rewards C_star C_h u t q hfuture j z hz
  have hbeforeO :
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t q.val z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run Q inputs)) := by
    simpa only [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout] using hbefore
  have hnorm :
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
          rate rewards C_star C_h u t q hfuture j z =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j
          (RecordedQueueRun.run Q inputs).registers := by
    rw [hback]
    rfl
  calc
    _ = ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j
        (RecordedQueueRun.run Q inputs).registers := by
      simp [futureBacklogMinus, hz, hbeforeO,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
    _ = _ := hnorm.symm

theorem futureBacklogPlus_eq_readout (z : Z) (hz : z ∈ Sq) (j : Fin p.K) :
    bplus j z =
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
        rate rewards C_star C_h u t q hfuture j z := by
  obtain ⟨inputs, c, hinputs, hcell, _, hafter, _, hback⟩ :=
    ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_present
      rate rewards C_star C_h u t q hfuture j z hz
  have hnorm :
      ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
          rate rewards C_star C_h u t q hfuture j z =
        ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j
          (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers := by
    rw [hback]
    rfl
  calc
    _ = ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers := by
      simp [futureBacklogPlus, hz, hafter,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout]
    _ = _ := hnorm.symm

theorem futureBacklogMinus_bounds (j : Fin p.K) (z : Z) :
    0 ≤ b j z ∧
      b j z ≤ 2 * Bcap := by
  by_cases hz : z ∈ Sq
  · rw [futureBacklogMinus_eq_readout rate rewards C_star C_h u t q hfuture z hz j]
    exact (ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_bounds
      rate rewards C_star C_h u t q hfuture j z).1
  · constructor
    · simp [futureBacklogMinus, hz]
    · have heta : 0 < rate.eta.val := rate.eta.property
      simp only [futureBacklogMinus, Set.indicator_of_notMem hz]
      positivity

theorem futureBacklogPlus_bounds (j : Fin p.K) (z : Z) :
    0 ≤ bplus j z ∧
      bplus j z ≤ 2 * Bcap := by
  by_cases hz : z ∈ Sq
  · rw [futureBacklogPlus_eq_readout rate rewards C_star C_h u t q hfuture z hz j]
    exact (ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogs_bounds
      rate rewards C_star C_h u t q hfuture j z).2
  · constructor
    · simp [futureBacklogPlus, hz]
    · have heta : 0 < rate.eta.val := rate.eta.property
      simp only [futureBacklogPlus, Set.indicator_of_notMem hz]
      positivity

theorem futureThetaMinus_bounds (j : Fin p.K) (z : Z) :
    0 ≤ θ j z ∧
      θ j z ≤ 1 := by
  by_cases hz : z ∈ Sq
  · rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
      ⟨inputs, c, _, _, _, _, _, _, htheta, _, _, _⟩
    rw [htheta]
    exact registerTheta_bounds rate (RecordedQueueRun.run Q inputs).registers j
  · simp [futureThetaMinus, hz]

theorem futureThetaPlus_bounds (j : Fin p.K) (z : Z) :
    0 ≤ θplus j z ∧
      θplus j z ≤ 1 := by
  by_cases hz : z ∈ Sq
  · rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
      ⟨inputs, c, _, _, _, _, _, _, _, _, htheta, _⟩
    rw [htheta]
    exact registerTheta_bounds rate
      (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers j
  · simp [futureThetaPlus, hz]

theorem futureThetaMinus_sum_eq_m (z : Z) (hz : z ∈ Sq) :
    (∑ j : Fin p.K,
      θ j z) = (p.m : ℝ) := by
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
    ⟨inputs, c, _, _, _, _, _, _, htheta, _, _, _⟩
  calc
    _ = ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
          rate j (RecordedQueueRun.run Q inputs).registers := by
      apply Finset.sum_congr rfl
      intro j hj
      exact htheta j
    _ = (p.m : ℝ) := registerTheta_sum rate _

theorem futureThetaPlus_sum_eq_m (z : Z) (hz : z ∈ Sq) :
    (∑ j : Fin p.K,
      θplus j z) = (p.m : ℝ) := by
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
    ⟨inputs, c, _, _, _, _, _, _, _, _, htheta, _⟩
  calc
    _ = ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters
          rate j (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers := by
      apply Finset.sum_congr rfl
      intro j hj
      exact htheta j
    _ = (p.m : ℝ) := registerTheta_sum rate _

theorem futureThetaPlus_upper_on_support (z : Z) (hz : z ∈ Sq) (j : Fin p.K) :
    θplus j z ≤
      (1 + 8 * rate.eta.val) *
        θ j z := by
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
    ⟨inputs, c, _, _, _, _, _, _, hthetaMinus, _, hthetaPlus, _⟩
  rw [hthetaPlus j, hthetaMinus j]
  exact futureThetaRegisters_upper rate (RecordedQueueRun.run Q inputs) c j

private theorem futureBacklogStepBounds_on_G
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z)
    (hz : z ∈ Gq) (j : Fin p.K) :
    bplus j z ^ 2 - b j z ^ 2 ≤ 2 * b j z * (a j z - 4) + a j z ^ 2 + 16 ∧
      bplus j z ^ 2 ≤ 2 * Bcap * (b j z + a j z) := by
  have hsupport := ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
    rate rewards C_star C_h u t q hfuture hz
  rcases hz with ⟨xi, hparams, hclear⟩
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hsupport with
    ⟨inputs, c, hinputs, hcell, _, _, _, _, _, _, _, _⟩
  have hparamsCell := futureParameters_present_from_cell
    rate rewards C_star C_h u t q hfuture z c hcell
  have hpair : (true, xi) = (c.enabled, c.rate) :=
    Option.some.inj (hparams.symm.trans hparamsCell)
  have henabled : c.enabled = true := (congrArg Prod.fst hpair).symm
  have hrec := ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter_reflected_of_retained
    rate rewards C_star C_h u t q hfuture j z inputs c hinputs hcell hclear henabled
  have hrec' : bplus j z =
      max (b j z +
        a j z - 4) 0 := by
    calc
      _ = ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogAfter
          rate rewards C_star C_h u t q hfuture j z :=
        futureBacklogPlus_eq_readout rate rewards C_star C_h u t q hfuture z hsupport j
      _ = max (ReferenceFirstCollectionRenewalFutureQueueReadout.futureBacklogBefore
          rate rewards C_star C_h u t q hfuture j z +
        a j z - 4) 0 := hrec
      _ = _ := by
        rw [← futureBacklogMinus_eq_readout
          rate rewards C_star C_h u t q hfuture z hsupport j]
  let back := b j z
  let arrival := a j z
  let back' := bplus j z
  have hb := futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z
  have hb' := futureBacklogPlus_bounds rate rewards C_star C_h u t q hfuture j z
  have ha := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_bounds
    rate rewards C_star C_h u t q hfuture control0 j z
  have hmaxsq : max (back + arrival - 4) 0 ^ 2 ≤ (back + arrival - 4) ^ 2 := by
    by_cases hy : 0 ≤ back + arrival - 4
    · simp [max_eq_left hy]
    · have hy' : back + arrival - 4 ≤ 0 := le_of_not_ge hy
      simpa [max_eq_right hy'] using sq_nonneg (back + arrival - 4)
  have hrecB : back' = max (back + arrival - 4) 0 := by
    simpa [back, arrival, back'] using hrec'
  have henergy : back' ^ 2 - back ^ 2 ≤ 2 * back * (arrival - 4) + arrival ^ 2 + 16 := by
    rw [hrecB]
    nlinarith [hmaxsq]
  have hpostle : back' ≤ back + arrival := by
    rw [hrecB]
    apply max_le
    · dsimp [back, arrival]
      linarith
    · exact add_nonneg hb.1 ha.1
  have hcap : 0 ≤ 2 * Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    positivity
  have hquad : back' ^ 2 ≤ 2 * Bcap * (back + arrival) := by
    have hsq : back' ^ 2 ≤ (2 * Bcap) * back' := by
      nlinarith [mul_nonneg hb'.1 (sub_nonneg.mpr hb'.2)]
    calc
      _ ≤ (2 * Bcap) * back' := hsq
      _ ≤ (2 * Bcap) * (back + arrival) := mul_le_mul_of_nonneg_left hpostle hcap
  exact ⟨by simpa [back, arrival, back'] using henergy,
    by simpa [back, arrival, back'] using hquad⟩

theorem futureWeightedEnergyPointwise_on_G
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) (hz : z ∈ Gq) :
    Vplus z - Vminus z ≤ ∑ j : Fin p.K,
      θ j z * (2 * b j z * (a j z - 4) + a j z ^ 2 + 16 +
        8 * rate.eta.val * bplus j z ^ 2) := by
  have hsupport := ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
    rate rewards C_star C_h u t q hfuture hz
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hsupport with
    ⟨inputs, c, _, _, _, _, henergyMinus, henergyPlus,
      hthetaMinus, hbackMinus, hthetaPlus, hbackPlus⟩
  have hidentity :
      Vplus z - Vminus z = ∑ j : Fin p.K,
        (θplus j z * bplus j z ^ 2 - θ j z * b j z ^ 2) := by
    rw [henergyPlus, henergyMinus]
    unfold ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters
    simp_rw [← hthetaPlus, ← hbackPlus, ← hthetaMinus, ← hbackMinus]
    rw [Finset.sum_sub_distrib]
  rw [hidentity]
  apply Finset.sum_le_sum
  intro j hj
  have htheta := futureThetaPlus_upper_on_support
    rate rewards C_star C_h u t q hfuture z hsupport j
  have hstep := futureBacklogStepBounds_on_G rate rewards C_star C_h u t q hfuture
    control0 z hz j
  have htheta0 := futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z
  have hmul := mul_le_mul_of_nonneg_right htheta
    (sq_nonneg (bplus j z))
  have hfirst :
      θplus j z * bplus j z ^ 2 - θ j z * bplus j z ^ 2 ≤
        8 * rate.eta.val * θ j z * bplus j z ^ 2 := by
    nlinarith [hmul]
  have hsecond := mul_le_mul_of_nonneg_left hstep.1 htheta0.1
  calc
    _ = (θplus j z * bplus j z ^ 2 - θ j z * bplus j z ^ 2) +
        θ j z * (bplus j z ^ 2 - b j z ^ 2) := by ring
    _ ≤ _ := add_le_add hfirst hsecond
    _ = _ := by ring_nf

private theorem futurePriorClear_eq_of_inputs (z : Z)
    (inputs : List (RecordedQueueRun.RoundInput p.K))
    (hinputs : ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
      rate rewards C_star C_h u t q z = some inputs) :
    ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = !((RecordedQueueRun.run Q inputs).overflow) := by
  unfold ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
  rw [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout_eq_of_inputs
    rate rewards C_star C_h u t q z inputs hinputs]
  cases hflag : (RecordedQueueRun.run Q inputs).overflow <;>
    simp [ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout, hflag]

theorem futureWeightedEnergyEqual_off_G (z : Z) (hz : z ∉ Gq) :
    Vplus z =
      Vminus z := by
  by_cases hsupport : z ∈ Sq
  · rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hsupport with
      ⟨inputs, c, hinputs, hcell, _, _, henergyMinus, henergyPlus, _, _, _, _⟩
    have hparams := futureParameters_present_from_cell
      rate rewards C_star C_h u t q hfuture z c hcell
    have hinactive : c.enabled = false ∨ (RecordedQueueRun.run Q inputs).overflow = true := by
      by_cases henabled : c.enabled = true
      · by_cases hoverflow : (RecordedQueueRun.run Q inputs).overflow = true
        · exact Or.inr hoverflow
        · have hclear : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
              rate rewards C_star C_h u t q z = true := by
            rw [futurePriorClear_eq_of_inputs rate rewards C_star C_h u t q z
              inputs hinputs]
            cases ho : (RecordedQueueRun.run Q inputs).overflow <;> simp_all
          have hparams' : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
              rate rewards C_star C_h u t z q hfuture = some (true, c.rate) := by
            simpa [henabled] using hparams
          exact False.elim (hz ⟨c.rate, hparams', hclear⟩)
      · cases hcEnabled : c.enabled <;> simp_all
    have hregs :
        (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers =
          (RecordedQueueRun.run Q inputs).registers := by
      funext j
      rcases hinactive with henabled | hoverflow
      · simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
          henabled, QueueReplay.transition]
      · simp [RecordedQueueRun.step, RecordedQueueRun.acceptedRecord,
          hoverflow, QueueReplay.transition]
    rw [henergyPlus, henergyMinus, hregs]
  · have hzeroPlus : Vplus z = 0 := by
      simp [futureWeightedEnergyPlus, hsupport]
    have hzeroMinus : Vminus z = 0 := by
      simp [futureWeightedEnergyMinus, hsupport]
    rw [hzeroPlus, hzeroMinus]

theorem futureWeightedEnergyReduced_on_G
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) (hz : z ∈ Gq) :
    Vplus z - Vminus z ≤ ∑ j : Fin p.K,
      θ j z * ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * a j z + a j z ^ 2 + 16) := by
  have hdetail := futureWeightedEnergyPointwise_on_G rate rewards C_star C_h u t
    q hfuture control0 z hz
  apply hdetail.trans
  apply Finset.sum_le_sum
  intro j hj
  have hstep := futureBacklogStepBounds_on_G rate rewards C_star C_h u t q hfuture
    control0 z hz j
  have htheta := futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z
  have hconstant : 8 * rate.eta.val * (2 * Bcap) = (1 / 2 : ℝ) := by
    field_simp [ne_of_gt rate.eta.property]
    ring
  have hquad := mul_le_mul_of_nonneg_left hstep.2
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) rate.eta.property.le)
  have hquad' :
      8 * rate.eta.val * bplus j z ^ 2 ≤ (1 / 2 : ℝ) * (b j z + a j z) := by
    calc
      _ ≤ 8 * rate.eta.val * (2 * Bcap * (b j z + a j z)) := hquad
      _ = _ := by rw [← mul_assoc, hconstant]
  have hinside :
      2 * b j z * (a j z - 4) + a j z ^ 2 + 16 + 8 * rate.eta.val * bplus j z ^ 2 ≤
        (-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * a j z + a j z ^ 2 + 16 := by
    nlinarith [hquad']
  exact mul_le_mul_of_nonneg_left hinside htheta.1

/-- The reduced one-step expression on the actual future first-invocation gate. -/
def futureReducedWeightedIncrement (z : Z) : ℝ :=
  ∑ j : Fin p.K,
    θ j z *
      ((-15 / 2 : ℝ) *
          b j z +
        (2 * b j z + 1 / 2) *
          a j z +
        (a j z) ^ 2 + 16)

theorem futureWeightedEnergyStep_pointwise
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) :
    Vplus z -
      Vminus z ≤
      Set.indicator Gq (futureReducedWeightedIncrement rate rewards C_star C_h u t q hfuture) z := by
  by_cases hz : z ∈ Gq
  · simpa [futureReducedWeightedIncrement, Set.indicator_of_mem hz] using
      futureWeightedEnergyReduced_on_G rate rewards C_star C_h u t q hfuture control0 z hz
  · rw [futureWeightedEnergyEqual_off_G rate rewards C_star C_h u t q hfuture z hz]
    simp [Set.indicator_of_notMem hz]

theorem futureWeightedEnergyMinus_bounds (z : Z) :
    0 ≤ Vminus z ∧
      Vminus z ≤
        4 * (p.m : ℝ) * Bcap ^ 2 := by
  by_cases hz : z ∈ Sq
  · rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
      ⟨inputs, c, _, _, _, _, henergy, _, _, hback, _, _⟩
    rw [henergy]
    have hback' (j : Fin p.K) :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
            rate j (RecordedQueueRun.run Q inputs).registers ∈
          Set.Icc (0 : ℝ) (2 * Bcap) := by
      rw [← hback j]
      exact ⟨(futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z).1,
        (futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z).2⟩
    have henergy' := registerEnergy_bounds rate
      (RecordedQueueRun.run Q inputs).registers hback'
    refine ⟨henergy'.1, ?_⟩
    calc
      _ ≤ (p.m : ℝ) * (2 * Bcap) ^ 2 := henergy'.2
      _ = 4 * (p.m : ℝ) * Bcap ^ 2 := by ring
  · constructor
    · simp [futureWeightedEnergyMinus, hz]
    · have heta : 0 < rate.eta.val := rate.eta.property
      simp only [futureWeightedEnergyMinus, Set.indicator_of_notMem hz]
      positivity

theorem futureWeightedEnergyPlus_bounds (z : Z) :
    0 ≤ Vplus z ∧
      Vplus z ≤
        4 * (p.m : ℝ) * Bcap ^ 2 := by
  by_cases hz : z ∈ Sq
  · rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hz with
      ⟨inputs, c, _, _, _, _, _, henergy, _, _, _, hback⟩
    rw [henergy]
    have hback' (j : Fin p.K) :
        ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters
            rate j (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers ∈
          Set.Icc (0 : ℝ) (2 * Bcap) := by
      rw [← hback j]
      exact ⟨(futureBacklogPlus_bounds rate rewards C_star C_h u t q hfuture j z).1,
        (futureBacklogPlus_bounds rate rewards C_star C_h u t q hfuture j z).2⟩
    have henergy' := registerEnergy_bounds rate
      (RecordedQueueRun.step Q (RecordedQueueRun.run Q inputs) c).registers hback'
    refine ⟨henergy'.1, ?_⟩
    calc
      _ ≤ (p.m : ℝ) * (2 * Bcap) ^ 2 := henergy'.2
      _ = 4 * (p.m : ℝ) * Bcap ^ 2 := by ring
  · constructor
    · simp [futureWeightedEnergyPlus, hz]
    · have heta : 0 < rate.eta.val := rate.eta.property
      simp only [futureWeightedEnergyPlus, Set.indicator_of_notMem hz]
      positivity

private theorem integrable_of_measurable_norm_le_const
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (c : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ c) : Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

theorem measurable_futureThetaMinus (j : Fin p.K) :
    Measurable[Fq] (θ j) := by
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
    rate rewards C_star C_h u t control0 q.val (by omega)
  have hproj : Measurable (fun o : Option (FuturePrefixStateReadout p.K) => o.elim 0 (fun r =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j r.1)) :=
    measurable_of_countable _
  change Measurable[Fq] ((Sq).indicator _)
  exact (hproj.comp hread).indicator
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurableSet_futureQueueSupport
      rate rewards C_star C_h u t q hfuture control0)

theorem measurable_futureBacklogMinus (j : Fin p.K) :
    Measurable[Fq] (b j) := by
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
    rate rewards C_star C_h u t control0 q.val (by omega)
  have hproj : Measurable (fun o : Option (FuturePrefixStateReadout p.K) => o.elim 0 (fun r =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j r.1)) :=
    measurable_of_countable _
  change Measurable[Fq] ((Sq).indicator _)
  exact (hproj.comp hread).indicator
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurableSet_futureQueueSupport
      rate rewards C_star C_h u t q hfuture control0)

theorem measurable_futureThetaPlus (control : ContinuousLearningRows.TimeControl p)
    (j : Fin p.K) :
    Measurable (θplus j) := by
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout_ambient
    rate rewards C_star C_h u t control (q.val + 1) (by omega)
  have hproj : Measurable (fun o : Option (FuturePrefixStateReadout p.K) => o.elim 0 (fun r =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters rate j r.1)) :=
    measurable_of_countable _
  change Measurable ((Sq).indicator _)
  exact (hproj.comp hread).indicator
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurableSet_futureQueueSupport_ambient
      rate rewards C_star C_h u t q hfuture control)

theorem measurable_futureBacklogPlus (control : ContinuousLearningRows.TimeControl p)
    (j : Fin p.K) :
    Measurable (bplus j) := by
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout_ambient
    rate rewards C_star C_h u t control (q.val + 1) (by omega)
  have hproj : Measurable (fun o : Option (FuturePrefixStateReadout p.K) => o.elim 0 (fun r =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters rate j r.1)) :=
    measurable_of_countable _
  change Measurable ((Sq).indicator _)
  exact (hproj.comp hread).indicator
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurableSet_futureQueueSupport_ambient
      rate rewards C_star C_h u t q hfuture control)

theorem measurable_futureWeightedEnergyMinus :
    Measurable[Fq] (Vminus) := by
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout
    rate rewards C_star C_h u t control0 q.val (by omega)
  have hproj : Measurable (fun o : Option (FuturePrefixStateReadout p.K) => o.elim 0 (fun r =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate r.1)) :=
    measurable_of_countable _
  change Measurable[Fq] ((Sq).indicator _)
  exact (hproj.comp hread).indicator
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurableSet_futureQueueSupport
      rate rewards C_star C_h u t q hfuture control0)

theorem measurable_futureWeightedEnergyPlus (control : ContinuousLearningRows.TimeControl p) :
    Measurable (Vplus) := by
  have hread := ReferenceFirstCollectionRenewalFutureNumericalPrefix.measurable_futurePrefixReadout_ambient
    rate rewards C_star C_h u t control (q.val + 1) (by omega)
  have hproj : Measurable (fun o : Option (FuturePrefixStateReadout p.K) => o.elim 0 (fun r =>
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters rate r.1)) :=
    measurable_of_countable _
  change Measurable ((Sq).indicator _)
  exact (hproj.comp hread).indicator
    (ReferenceFirstCollectionRenewalFutureExponentialQueueStep.measurableSet_futureQueueSupport_ambient
      rate rewards C_star C_h u t q hfuture control)

theorem measurable_futureWeightedBacklog :
    Measurable[Fq] (B) := by
  unfold futureWeightedBacklog
  simpa only [← Finset.sum_apply] using
    (Finset.measurable_fun_sum Finset.univ (fun j _ =>
      (measurable_futureThetaMinus rate rewards C_star C_h u t control0 q hfuture j).mul
        (measurable_futureBacklogMinus rate rewards C_star C_h u t control0 q hfuture j)))

theorem measurable_futureRecordingCost :
    Measurable[Fq] (C) := by
  let : MeasurableSpace Z := Fq
  let costTerms : Z → ℝ := fun z =>
    ∑ j : Fin p.K,
      (θ j /
        futureParameterRate rate rewards C_star C_h u t q hfuture j) z
  have hsum : Measurable[Fq] costTerms := by
    dsimp [costTerms]
    exact Finset.measurable_fun_sum Finset.univ (fun j _ =>
      (measurable_futureThetaMinus rate rewards C_star C_h u t control0 q hfuture j).div
        (measurable_futureParameterRate rate rewards C_star C_h u t control0 q hfuture j))
  have hpresent := measurable_futureParametersPresent
    rate rewards C_star C_h u t control0 q hfuture
  have hset : MeasurableSet[Fq]
      ((fun z : Z => futureParametersPresent rate rewards C_star C_h u t q hfuture z) ⁻¹'
        {true}) := hpresent (measurableSet_singleton _)
  have hformula : C =
      fun z => if futureParametersPresent rate rewards C_star C_h u t q hfuture z then
        costTerms z
        else 0 := by
    funext z
    cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
        rate rewards C_star C_h u t z q hfuture with
    | none => simp [futureRecordingCost, futureParametersPresent, hp]
    | some par =>
        rcases par with ⟨enabled, xi⟩
        simp [futureRecordingCost, futureParametersPresent, futureParameterRate, costTerms, hp,
          Pi.div_apply]
  rw [hformula]
  exact Measurable.ite hset hsum measurable_const

theorem futureRecordingCost_bounds (z : Z) :
    0 ≤ C z ∧
      C z ≤
        (p.m : ℝ) / β := by
  by_cases hz : z ∈ Sq
  · obtain ⟨c, hc⟩ := futureCell_present_of_support rate rewards C_star C_h u t q hfuture z hz
    have hparams := futureParameters_present_from_cell rate rewards C_star C_h u t q hfuture z c hc
    have hrate := ReferenceFirstCollectionRenewalFutureQueueReadout.futureCell_present_rate_bounds
      rate rewards C_star C_h u t q hfuture z c hc
    have hbeta : 0 < β := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hxiPos (j : Fin p.K) : 0 < c.rate j :=
      lt_of_lt_of_le hbeta (hrate.1 j)
    have htheta0 (j : Fin p.K) :
        0 ≤ θ j z :=
      (futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z).1
    have hterm (j : Fin p.K) :
        0 ≤ θ j z / c.rate j :=
      div_nonneg (htheta0 j) (hxiPos j).le
    have htermUpper (j : Fin p.K) :
        θ j z / c.rate j ≤
          θ j z / β := by
      rw [div_le_div_iff₀ (hxiPos j) hbeta]
      nlinarith [mul_nonneg (htheta0 j)
        (sub_nonneg.mpr (hrate.1 j))]
    have hcost : C z =
        ∑ j : Fin p.K,
          θ j z / c.rate j := by
      simp [futureRecordingCost, hparams]
    constructor
    · rw [hcost]
      exact Finset.sum_nonneg (fun j hj => hterm j)
    · rw [hcost]
      calc
        _ ≤ ∑ j : Fin p.K,
            θ j z / β :=
          Finset.sum_le_sum (fun j hj => htermUpper j)
        _ = (∑ j : Fin p.K,
            θ j z) / β := by
          rw [Finset.sum_div]
        _ = (p.m : ℝ) / β := by
          rw [futureThetaMinus_sum_eq_m rate rewards C_star C_h u t q hfuture z hz]
  · have htheta0 (j : Fin p.K) :
        θ j z = 0 := by
      simp [futureThetaMinus, hz]
    have hcost : C z = 0 := by
      cases hp : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
          rate rewards C_star C_h u t z q hfuture with
      | none => simp [futureRecordingCost, hp]
      | some par =>
          rcases par with ⟨enabled, xi⟩
          simp [futureRecordingCost, hp, htheta0]
    have hbound0 : 0 ≤ (p.m : ℝ) / β :=
      div_nonneg (Nat.cast_nonneg _) (CanonicalRecordingRates.beta_pos p rate.eta.property).le
    rw [hcost]
    exact ⟨le_rfl, hbound0⟩

theorem futureMoments_present_gate_bounds
    (control0 : ContinuousLearningRows.TimeControl p) (z : Z) (xi : Fin p.K → ℝ)
    (hparams : ReferenceFirstCollectionRenewalFutureRecordingLaw.futureParameters
      rate rewards C_star C_h u t z q hfuture = some (true, xi))
    (hclear : ReferenceFirstCollectionRenewalFutureRetainedMoments.priorClear
      rate rewards C_star C_h u t q z = true) (j : Fin p.K) :
    0 ≤ ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z ≤ 1 ∧
      0 ≤ ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentTwo
        rate rewards C_star C_h u t q hfuture j z ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentTwo
        rate rewards C_star C_h u t q hfuture j z ≤ 1 / xi j := by
  have hzG : z ∈ Gq := ⟨xi, hparams, hclear⟩
  have hsupport := ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
    rate rewards C_star C_h u t q hfuture hzG
  rcases futureReadouts_same_run_step rate rewards C_star C_h u t q hfuture z hsupport with
    ⟨inputs, c, hinputs, hcell, _, _, _, _, _, _, _, _⟩
  have hparamsCell := futureParameters_present_from_cell
    rate rewards C_star C_h u t q hfuture z c hcell
  have hpair : (true, xi) = (c.enabled, c.rate) :=
    Option.some.inj (hparams.symm.trans hparamsCell)
  have henabled : c.enabled = true := (congrArg Prod.fst hpair).symm
  have hxi : c.rate = xi := (congrArg Prod.snd hpair).symm
  have hclearRun : (RecordedQueueRun.run Q inputs).overflow = false := by
    have hclear' := futurePriorClear_eq_of_inputs rate rewards C_star C_h u t q z inputs hinputs
    rw [hclear'] at hclear
    cases ho : (RecordedQueueRun.run Q inputs).overflow <;> simp_all
  have hmom := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMoments_present_enabled_bounds
    rate rewards C_star C_h u t q hfuture control0 j z inputs c hinputs hcell henabled hclearRun
  have hreward :
      ((rewards q j).val : ℝ) / (D p : ℝ) ≤ 1 := by
    change RealRewardGridCount.realRewardGridValue (D p) (D_pos p) (rewards q j) ≤ 1
    exact (RealRewardGridCount.realRewardGridValue_mem_Icc
      (D p) (D_pos p) (rewards q j)).2
  have hxiPos : 0 < xi j := by
    rw [← hxi]
    have hfloor := (ReferenceFirstCollectionRenewalFutureQueueReadout.futureCell_present_rate_bounds
      rate rewards C_star C_h u t q hfuture z c hcell).1 j
    exact lt_of_lt_of_le (CanonicalRecordingRates.beta_pos p rate.eta.property) hfloor
  have hsecond :
      (((rewards q j).val : ℝ) / (D p : ℝ)) ^ 2 / c.rate j ≤ 1 / xi j := by
    rw [hxi]
    have hreward0 : 0 ≤ ((rewards q j).val : ℝ) / (D p : ℝ) := by positivity
    have hrewardSq : (((rewards q j).val : ℝ) / (D p : ℝ)) ^ 2 ≤ 1 := by
      nlinarith
    exact div_le_div_of_nonneg_right hrewardSq hxiPos.le
  have hm1nonneg := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne_bounds
    rate rewards C_star C_h u t q hfuture control0 j z
  refine ⟨hm1nonneg.1, le_trans hmom.2.1 hreward, hmom.2.2.1, ?_⟩
  exact le_trans hmom.2.2.2 hsecond

theorem futureWeightedBacklog_bounds (z : Z) :
    0 ≤ B z ∧
      B z ≤
        2 * (p.m : ℝ) * Bcap := by
  have hcap : 0 ≤ 2 * Bcap := by
    have heta : 0 < rate.eta.val := rate.eta.property
    positivity
  by_cases hz : z ∈ Sq
  · unfold futureWeightedBacklog
    simp only [Finset.sum_apply]
    refine ⟨Finset.sum_nonneg (fun j hj => mul_nonneg
      (futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z).1
      (futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z).1), ?_⟩
    calc
      _ ≤ ∑ j : Fin p.K,
          θ j z * (2 * Bcap) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z).2
          (futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z).1
      _ = (∑ j : Fin p.K,
          θ j z) * (2 * Bcap) := by
        rw [Finset.sum_mul]
      _ = 2 * (p.m : ℝ) * Bcap := by
        rw [futureThetaMinus_sum_eq_m rate rewards C_star C_h u t q hfuture z hz]
        ring
  · constructor
    · simp [futureWeightedBacklog, futureThetaMinus, hz]
    · simp [futureWeightedBacklog, futureThetaMinus, hz]
      have heta : 0 < rate.eta.val := rate.eta.property
      positivity

theorem integrable_futureRecordingCost (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (C) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hbound : 0 ≤ (p.m : ℝ) / β := by
    exact div_nonneg (Nat.cast_nonneg _)
      (CanonicalRecordingRates.beta_pos p rate.eta.property).le
  apply integrable_of_measurable_norm_le_const _
    ((measurable_futureRecordingCost rate rewards C_star C_h u t control0 q hfuture).mono
      hfield le_rfl)
    ((p.m : ℝ) / β)
  intro z
  rw [Real.norm_of_nonneg (futureRecordingCost_bounds
    rate rewards C_star C_h u t q hfuture z).1]
  exact (futureRecordingCost_bounds rate rewards C_star C_h u t q hfuture z).2

theorem integrable_futureWeightedBacklog (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (B) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  apply integrable_of_measurable_norm_le_const _
    ((measurable_futureWeightedBacklog rate rewards C_star C_h u t control0 q hfuture).mono
      hfield le_rfl)
    (2 * (p.m : ℝ) * Bcap)
  intro z
  rw [Real.norm_of_nonneg (futureWeightedBacklog_bounds
    rate rewards C_star C_h u t q hfuture z).1]
  exact (futureWeightedBacklog_bounds rate rewards C_star C_h u t q hfuture z).2

theorem integrable_futureWeightedEnergyMinus (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (Vminus) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  apply integrable_of_measurable_norm_le_const _
    ((measurable_futureWeightedEnergyMinus rate rewards C_star C_h u t control0 q hfuture).mono
      hfield le_rfl)
    (4 * (p.m : ℝ) * Bcap ^ 2)
  intro z
  rw [Real.norm_of_nonneg (futureWeightedEnergyMinus_bounds
    rate rewards C_star C_h u t q hfuture z).1]
  exact (futureWeightedEnergyMinus_bounds rate rewards C_star C_h u t q hfuture z).2

theorem integrable_futureWeightedEnergyPlus (control : ContinuousLearningRows.TimeControl p) :
    Integrable (Vplus) ν := by
  apply integrable_of_measurable_norm_le_const _
    (measurable_futureWeightedEnergyPlus rate rewards C_star C_h u t q hfuture control)
    (4 * (p.m : ℝ) * Bcap ^ 2)
  intro z
  rw [Real.norm_of_nonneg (futureWeightedEnergyPlus_bounds
    rate rewards C_star C_h u t q hfuture z).1]
  exact (futureWeightedEnergyPlus_bounds rate rewards C_star C_h u t q hfuture z).2

private theorem futureArm_condExp (j : Fin p.K) :
    Integrable (fun z => θ j z *
      ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * a j z + a j z ^ 2 + 16)) ν ∧
    ν[(fun z => θ j z *
      ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * a j z + a j z ^ 2 + 16)) | Fq]
      =ᵐ[ν] fun z => θ j z *
        ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * M₁ j z + M₂ j z + 16) := by
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have ht := measurable_futureThetaMinus rate rewards C_star C_h u t control0 q hfuture j
  have hb := measurable_futureBacklogMinus rate rewards C_star C_h u t control0 q hfuture j
  let coeff : Z → ℝ := fun z => θ j z * (2 * b j z + 1 / 2)
  let base : Z → ℝ := fun z => θ j z * ((-15 / 2 : ℝ) * b j z + 16)
  have hc : Measurable[Fq] coeff := ht.mul ((measurable_const.mul hb).add_const _)
  have hbase : Measurable[Fq] base := ht.mul ((measurable_const.mul hb).add_const _)
  have htbound : ∀ᵐ z ∂ν, ‖θ j z‖ ≤ 1 := by
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z).1]
    exact (futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z).2
  have hcbound : ∀ᵐ z ∂ν, ‖coeff z‖ ≤ 4 * Bcap + 1 / 2 := by
    filter_upwards [] with z
    have ht' := futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z
    have hb' := futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z
    dsimp [coeff]
    rw [abs_of_nonneg (mul_nonneg ht'.1 (by linarith))]
    calc
      _ ≤ 1 * (2 * b j z + 1 / 2) := mul_le_mul_of_nonneg_right ht'.2 (by linarith)
      _ ≤ 4 * Bcap + 1 / 2 := by linarith
  have hbaseInt : Integrable base ν := by
    apply integrable_of_measurable_norm_le_const _ (hbase.mono hle le_rfl)
      (15 * Bcap + 16)
    intro z
    have ht' := futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z
    have hb' := futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z
    rw [Real.norm_eq_abs, abs_le]
    have hlow := mul_le_mul_of_nonneg_left hb'.2 ht'.1
    have hhigh := mul_nonneg ht'.1 hb'.1
    dsimp [base]
    constructor <;> nlinarith
  have ha := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
    rate rewards C_star C_h u t q hfuture control0 j
  have ha2 := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_sq_integrable
    rate rewards C_star C_h u t q hfuture control0 j
  have hca := ha.bdd_mul (hc.mono hle le_rfl).aestronglyMeasurable hcbound
  have hta2 := ha2.bdd_mul (ht.mono hle le_rfl).aestronglyMeasurable htbound
  have hshape : (fun z => θ j z *
      ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * a j z + a j z ^ 2 + 16)) =
      ((fun z => coeff z * a j z) + (fun z => θ j z * a j z ^ 2)) + base := by
    funext z
    dsimp [coeff, base]
    ring
  refine ⟨by rw [hshape]; exact (hca.add hta2).add hbaseInt, ?_⟩
  rw [hshape]
  have hpull := condExp_mul_of_stronglyMeasurable_left hc.stronglyMeasurable hca ha
  have hpull2 := condExp_mul_of_stronglyMeasurable_left ht.stronglyMeasurable hta2 ha2
  have hfix := condExp_of_stronglyMeasurable hle hbase.stronglyMeasurable hbaseInt
  have hm1 := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_condExp
    rate rewards C_star C_h u t q hfuture control0 j
  have hm2 := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_sq_condExp
    rate rewards C_star C_h u t q hfuture control0 j
  filter_upwards [condExp_add (hca.add hta2) hbaseInt Fq, condExp_add hca hta2 Fq,
    hpull, hpull2, hm1, hm2] with z hsum hsum' hp hp2 hm hm'
  simp only [Pi.add_apply, Pi.mul_apply] at hsum hsum' hp hp2
  change ν[(fun x => coeff x * a j x) | Fq] z = coeff z * ν[(fun x => a j x) | Fq] z at hp
  change ν[(fun x => θ j x * a j x ^ 2) | Fq] z =
    θ j z * ν[(fun x => a j x ^ 2) | Fq] z at hp2
  rw [hsum, hsum', hp, hp2, hm, hm', hfix]
  dsimp [coeff, base]
  ring

/-- Conditional quadratic drift at a supported future date on the original
finite renewal law. The charge is the literal current marginal/rate sum. -/
theorem futureWeightedEnergy_condExp :
    ν[(fun z => Vplus z - Vminus z) | Fq] ≤ᵐ[ν]
      (Gq).indicator (fun z => -(11 / 2 : ℝ) * B z + C z + (33 / 2 : ℝ) * p.m) := by
  let arm := fun j (z : Z) => θ j z *
    ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * a j z + a j z ^ 2 + 16)
  let armM := fun j (z : Z) => θ j z *
    ((-15 / 2 : ℝ) * b j z + (2 * b j z + 1 / 2) * M₁ j z + M₂ j z + 16)
  have har (j : Fin p.K) := futureArm_condExp rate rewards C_star C_h u t control0 q hfuture j
  have hi : Integrable (∑ j : Fin p.K, arm j) ν :=
    integrable_finsetSum' _ (fun j _ => (har j).1)
  have hG := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hred : futureReducedWeightedIncrement rate rewards C_star C_h u t q hfuture =
      ∑ j : Fin p.K, arm j := by
    funext z
    simp only [Finset.sum_apply]
    rfl
  have hmasked := hi.indicator (hle _ hG)
  have hmono := condExp_mono (m := Fq)
    ((integrable_futureWeightedEnergyPlus rate rewards C_star C_h u t q hfuture control0).sub
      (integrable_futureWeightedEnergyMinus rate rewards C_star C_h u t q hfuture control0))
    hmasked (Filter.Eventually.of_forall fun z => by
      have hz := futureWeightedEnergyStep_pointwise rate rewards C_star C_h u t q hfuture control0 z
      rw [hred] at hz
      exact hz)
  have hsum := condExp_finsetSum (s := Finset.univ) (f := arm) (fun j _ => (har j).1) Fq
  have harm : ∀ᵐ z ∂ν, ∀ j : Fin p.K, ν[arm j | Fq] z = armM j z :=
    ae_all_iff.mpr (fun j => (har j).2)
  filter_upwards [hmono, condExp_indicator hi hG, hsum, harm] with z hz hmask hs ha
  apply hz.trans
  rw [hmask]
  by_cases hzg : z ∈ Gq
  · simp only [Set.indicator_of_mem hzg, Finset.sum_apply] at hs ⊢
    rw [hs]
    simp_rw [ha]
    obtain ⟨xi, hp, hclear⟩ := hzg
    have hsupport := ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
      rate rewards C_star C_h u t q hfuture ⟨xi, hp, hclear⟩
    have hterms (j : Fin p.K) : armM j z ≤
        -(11 / 2 : ℝ) * (θ j z * b j z) + θ j z / xi j + (33 / 2 : ℝ) * θ j z := by
      have hm := futureMoments_present_gate_bounds rate rewards C_star C_h u t q hfuture
        control0 z xi hp hclear j
      have ht := futureThetaMinus_bounds rate rewards C_star C_h u t q hfuture j z
      have hb := futureBacklogMinus_bounds rate rewards C_star C_h u t q hfuture j z
      have hfirst := mul_le_mul_of_nonneg_left hm.2.1
        (mul_nonneg ht.1 (by linarith : 0 ≤ 2 * b j z + 1 / 2))
      have hsecond := mul_le_mul_of_nonneg_left hm.2.2.2 ht.1
      dsimp [armM]
      simp only [div_eq_mul_inv] at hsecond ⊢
      nlinarith only [hfirst, hsecond]
    calc
      _ ≤ ∑ j : Fin p.K, (-(11 / 2 : ℝ) * (θ j z * b j z) +
          θ j z / xi j + (33 / 2 : ℝ) * θ j z) := Finset.sum_le_sum (fun j _ => hterms j)
      _ = -(11 / 2 : ℝ) * B z + C z + (33 / 2 : ℝ) * p.m := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [futureThetaMinus_sum_eq_m rate rewards C_star C_h u t q hfuture z hsupport]
        simp only [futureWeightedBacklog, futureRecordingCost, hp, Finset.sum_apply, Pi.mul_apply]
  · simp only [Set.indicator_of_notMem hzg, le_refl]

/-- Integrated supported-date accounting, with both actual endpoint energies. -/
theorem futureWeightedEnergy_integral (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) * (∫ z, (Gq).indicator B z ∂ν) ≤
      (∫ z, (Gq).indicator (fun z => C z + (33 / 2 : ℝ) * p.m) z ∂ν) +
        (∫ z, Vminus z ∂ν) - ∫ z, Vplus z ∂ν := by
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hG := hle _ (ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0)
  have hb := (integrable_futureWeightedBacklog rate rewards C_star C_h u t q hfuture control0).indicator hG
  have hc := ((integrable_futureRecordingCost rate rewards C_star C_h u t q hfuture control0).add
    (integrable_const ((33 / 2 : ℝ) * p.m))).indicator hG
  change Integrable ((Gq).indicator (fun z => C z + (33 / 2 : ℝ) * p.m)) ν at hc
  have hshape : (Gq).indicator (fun z => -(11 / 2 : ℝ) * B z + C z + (33 / 2 : ℝ) * p.m) =
      (fun z => (Gq).indicator (fun z => C z + (33 / 2 : ℝ) * p.m) z -
        (11 / 2 : ℝ) * (Gq).indicator B z) := by
    funext z
    by_cases hz : z ∈ Gq
    · simp only [Set.indicator_of_mem hz]
      ring
    · simp only [Set.indicator_of_notMem hz, mul_zero, sub_self]
  have hright : Integrable ((Gq).indicator
      (fun z => -(11 / 2 : ℝ) * B z + C z + (33 / 2 : ℝ) * p.m)) ν := by
    rw [hshape]
    exact hc.sub (hb.const_mul _)
  have hineq := integral_mono_ae integrable_condExp hright
    (futureWeightedEnergy_condExp rate rewards C_star C_h u t control0 q hfuture)
  rw [integral_condExp hle, integral_sub
    (integrable_futureWeightedEnergyPlus rate rewards C_star C_h u t q hfuture control0)
    (integrable_futureWeightedEnergyMinus rate rewards C_star C_h u t q hfuture control0),
    hshape, integral_sub hc (hb.const_mul _), integral_const_mul] at hineq
  linarith only [hineq]

/-- The same one-cell accounting with the proved literal cost bound `m / beta`.
The original measure mass is retained; it is never normalized. -/
theorem futureWeightedEnergy_integral_beta (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) * (∫ z, (Gq).indicator B z ∂ν) ≤
      (ν).real Gq * ((p.m : ℝ) / β + (33 / 2 : ℝ) * p.m) +
        (∫ z, Vminus z ∂ν) - ∫ z, Vplus z ∂ν := by
  have hle := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hG := hle _ (ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0)
  have hc := ((integrable_futureRecordingCost rate rewards C_star C_h u t q hfuture control0).add
    (integrable_const ((33 / 2 : ℝ) * p.m))).indicator hG
  have hi := (integrable_const ((p.m : ℝ) / β + (33 / 2 : ℝ) * p.m) (μ := ν)).indicator hG
  have hcost := integral_mono_ae hc hi (Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ Gq
    · simp only [Set.indicator_of_mem hz]
      change C z + (33 / 2 : ℝ) * p.m ≤ (p.m : ℝ) / β + (33 / 2 : ℝ) * p.m
      linarith only [(futureRecordingCost_bounds rate rewards C_star C_h u t q hfuture z).2]
    · simp only [Set.indicator_of_notMem hz, le_refl])
  rw [integral_indicator_const _ hG, smul_eq_mul] at hcost
  change (∫ z, (Gq).indicator (fun z => C z + (33 / 2 : ℝ) * p.m) z ∂ν) ≤ _ at hcost
  have hstep := futureWeightedEnergy_integral rate rewards C_star C_h u t q hfuture control0
  linarith only [hstep, hcost]

/-- Adjacent support can only be lost: presence at the next date forces the
current date into the same original continuing slice, before its endpoint. -/
theorem futureQueueSupport_adjacent_subset (q' : Fin p.T)
    (hadj : q'.val = q.val + 1) (hfuture' : t.val + 1 < q'.val) :
    ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t q' hfuture' ⊆ Sq := by
  intro z hz
  obtain ⟨c', hc'⟩ := futureCell_present_of_support rate rewards C_star C_h u t q' hfuture' z hz
  have hk : q.val - (t.val + 1) < (continuingRecords rate rewards C_star C_h u t z).length := by
    cases hbranch : sliceBranch rate rewards C_star C_h u t z q' hfuture' with
    | none =>
        simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell,
          hbranch, Option.isSome_none, Bool.false_eq_true, ite_false] at hc'
        cases hc'
    | some branch =>
        have hg := sliceBranch_geometry rate rewards C_star C_h u t z q' hfuture' branch hbranch
        cases branch
        · have := hg.1 rfl
          omega
        · have := hg.2 rfl
          omega
  have hr := futureRecord_eq_continuing rate rewards C_star C_h u t z q hfuture hk
  have hcont : ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen
      (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture) = true := by
    rw [hr]
    exact ReferenceFirstReplacementLiveFollowerPrefix.continuingTail_mem _ _ _ (List.get_mem ..)
  have hbranch : sliceBranch rate rewards C_star C_h u t z q hfuture = some false := by
    rw [sliceBranch, ite_eq_left hk.le, futureTag_eq]
    cases hcoord : (ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureRecord
        rate rewards C_star C_h u t z q hfuture).output.preparation.coordinator
      <;> simp only [ReferenceFirstReplacementLiveFollowerPrefix.isContinuingChosen, hcoord] at hcont ⊢
      <;> try contradiction
    rename_i out
    cases out <;> simp_all [ReferenceFirstCollectionRenewalNextRecordingPriorView.eraseArm,
      ReferenceLiveDispatchOutputMeasurability.outcomeData]
  obtain ⟨live, _, hread, _⟩ := firstReplacement_future_live_readout
    rate rewards C_star C_h u t z q hfuture hk
  have hc : ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
      rate rewards C_star C_h u t z q hfuture = some live.input := by
    simp only [ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell,
      hbranch, Option.isSome_some, ite_true, hread, Option.some_or]
  have hp := futureParameters_present_from_cell rate rewards C_star C_h u t q hfuture z live.input hc
  refine ⟨by rw [hp]; rfl, ?_⟩
  have hn : (ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
      rate rewards C_star C_h u t (q.val + 1) z).isSome = true := by
    simpa only [ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout, hadj] using hz.2
  rw [ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout_succ
    rate rewards C_star C_h u t q z hfuture] at hn
  cases hi : ReferenceFirstCollectionRenewalFutureNumericalPrefix.optionalPrefixCells
      (ReferenceFirstCollectionRenewalFutureNumericalPrefix.calendarCells
        rate rewards C_star C_h u t q.val z) with
  | none => simp only [hi, Option.isSome_none, Bool.false_eq_true] at hn
  | some inputs =>
      have hip : prefixInputs rate rewards C_star C_h u t q z = some inputs := hi
      rw [priorReadout_eq_of_inputs rate rewards C_star C_h u t q z inputs hip]
      rfl

/-- On next-date support the adjacent optional readout is literally shared. -/
theorem futureWeightedEnergy_adjacent (q' : Fin p.T)
    (hadj : q'.val = q.val + 1) (hfuture' : t.val + 1 < q'.val) (z : Z)
    (hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t q' hfuture') :
    futureWeightedEnergyMinus rate rewards C_star C_h u t q' hfuture' z = Vplus z := by
  have hq := futureQueueSupport_adjacent_subset rate rewards C_star C_h u t q hfuture q' hadj hfuture' hz
  simp only [futureWeightedEnergyMinus, futureWeightedEnergyPlus,
    Set.indicator_of_mem hz, Set.indicator_of_mem hq, hadj]

/-- Losing support pays a nonnegative energy drop, without an assertion about
preserving the unlocalized physical run beyond the first cutoff. -/
theorem futureWeightedEnergy_adjacent_le (q' : Fin p.T)
    (hadj : q'.val = q.val + 1) (hfuture' : t.val + 1 < q'.val) (z : Z) :
    futureWeightedEnergyMinus rate rewards C_star C_h u t q' hfuture' z ≤ Vplus z := by
  by_cases hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t q' hfuture'
  · exact (futureWeightedEnergy_adjacent rate rewards C_star C_h u t q hfuture q' hadj hfuture' z hz).le
  · simp only [futureWeightedEnergyMinus, Set.indicator_of_notMem hz]
    exact (futureWeightedEnergyPlus_bounds rate rewards C_star C_h u t q hfuture z).1

end Bandits.Support.ReferenceFirstCollectionRenewalFutureWeightedEnergyStep

end
