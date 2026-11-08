/-
Copyright (c) 2026 Bandits formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.QuantizedRecordingMoments
public import Bandits.Support.RecordedQueueRun
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The logical recording-outcome law and raw queue arrivals

The finite law here is the logical learner's prescribed input law in
`sources/zip4/manuscript/04_slow_fast_learner.tex:151-155`. It is one shared
`Option (Fin K)` outcome, not independent arm indicators, and it does not
assert that a physical protocol realizes the conditional law. The raw moment
bounds follow the manuscript's rounding calculation in `:256-264`. The queue
input and step are the accepted definitions in `RecordedQueueRun`, which model
the update in `:157-174` and retain its first overflowing update as described
in `:182-187`.
-/

@[expose] public section

namespace Bandits.Support.RecordedRoundMoments

open MeasureTheory
open scoped BigOperators

variable {K : ℕ}

/-- A finite outcome space has its discrete measurable structure. -/
instance optionFinMeasurableSpace (K : ℕ) : MeasurableSpace (Option (Fin K)) := ⊤

/-- Recording rates with the exact probability-validity data needed to define
the learner's single recorded-arm-or-none outcome law. -/
structure RecordingRates (K : ℕ) where
  rate : Fin K → ℝ
  rate_pos : ∀ i, 0 < rate i
  rate_sum_le_one : ∑ i, rate i ≤ 1

theorem RecordingRates.rate_nonneg (rates : RecordingRates K) (i : Fin K) :
    0 ≤ rates.rate i := (rates.rate_pos i).le

theorem RecordingRates.none_mass_nonneg (rates : RecordingRates K) :
    0 ≤ 1 - ∑ i, rates.rate i := by
  have h := rates.rate_sum_le_one
  linarith

theorem RecordingRates.rate_le_one (rates : RecordingRates K) (i : Fin K) :
    rates.rate i ≤ 1 := by
  have hsum : rates.rate i ≤ ∑ j, rates.rate j :=
    Finset.single_le_sum (fun j _ => rates.rate_nonneg j) (Finset.mem_univ i)
  exact hsum.trans rates.rate_sum_le_one

/-- The prescribed mass at one shared recording outcome. -/
def outcomeMass (rates : RecordingRates K) : Option (Fin K) → ENNReal
  | none => ENNReal.ofReal (1 - ∑ i, rates.rate i)
  | some i => ENNReal.ofReal (rates.rate i)

theorem outcomeMass_nonneg (rates : RecordingRates K) (outcome : Option (Fin K)) :
    0 ≤ outcomeMass rates outcome := by
  cases outcome with
  | none => exact bot_le
  | some i => exact bot_le

theorem outcomeMass_sum_eq_one (rates : RecordingRates K) :
    (∑ outcome : Option (Fin K), outcomeMass rates outcome) = 1 := by
  have hsum_nonneg : 0 ≤ ∑ i, rates.rate i :=
    Finset.sum_nonneg fun i _ => rates.rate_nonneg i
  have hnone_nonneg : 0 ≤ 1 - ∑ i, rates.rate i :=
    rates.none_mass_nonneg
  have hsum_ofReal : ENNReal.ofReal (∑ i : Fin K, rates.rate i) =
      ∑ i : Fin K, ENNReal.ofReal (rates.rate i) := by
    simpa using (ENNReal.ofReal_sum_of_nonneg
      (s := Finset.univ) (f := rates.rate)
      (fun i _ => rates.rate_nonneg i))
  rw [Fintype.sum_option]
  simp only [outcomeMass]
  rw [← hsum_ofReal, ← ENNReal.ofReal_add hnone_nonneg hsum_nonneg]
  rw [sub_add_cancel]
  simp

/-- The Mathlib PMF for the logical recorded-arm-or-none input law. -/
noncomputable def recordingOutcomePMF (rates : RecordingRates K) :
    PMF (Option (Fin K)) :=
  PMF.ofFintype (outcomeMass rates) (outcomeMass_sum_eq_one rates)

@[simp] theorem recordingOutcomePMF_some (rates : RecordingRates K) (i : Fin K) :
    recordingOutcomePMF rates (some i) = ENNReal.ofReal (rates.rate i) := by
  simp [recordingOutcomePMF, outcomeMass]

@[simp] theorem recordingOutcomePMF_none (rates : RecordingRates K) :
    recordingOutcomePMF rates none = ENNReal.ofReal (1 - ∑ i, rates.rate i) := by
  simp [recordingOutcomePMF, outcomeMass]

theorem recordingOutcomePMF_none_eq_zero_of_rate_sum_eq_one
    (rates : RecordingRates K) (hsum : ∑ i, rates.rate i = 1) :
    recordingOutcomePMF rates none = 0 := by
  simp [hsum]

@[simp] theorem recordingOutcomePMF_toMeasure_some (rates : RecordingRates K)
    (i : Fin K) :
    (recordingOutcomePMF rates).toMeasure {some i} =
      ENNReal.ofReal (rates.rate i) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact recordingOutcomePMF_some rates i

@[simp] theorem recordingOutcomePMF_toMeasure_none (rates : RecordingRates K) :
    (recordingOutcomePMF rates).toMeasure {none} =
      ENNReal.ofReal (1 - ∑ i, rates.rate i) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  exact recordingOutcomePMF_none rates

/-- The manuscript's fixed-round input, using the accepted queue API. -/
def fixedRoundInput (_p : RecordedQueueRun.Parameters)
    (rates : RecordingRates K) (reward : Fin K → ℝ)
    (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (outcome : Option (Fin K)) : RecordedQueueRun.RoundInput K :=
  ⟨enabled, outcome, reward,
    rates.rate,
    fun i => (reward_mem i).1,
    fun i => (reward_mem i).2,
    rates.rate_pos⟩

/-- The existing nominal quantized arrival divided by the queue denominator. -/
noncomputable def normalizedQuantizedArrival
    (p : RecordedQueueRun.Parameters) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) : ℝ :=
  (RecordedQueueRun.quantizedArrival p round i : ℝ) / (p.n : ℝ)

/-- The existing accepted raw arrival divided by the queue denominator. This
is the unserved arrival; it does not use `recordService` or the score update. -/
noncomputable def rawEstimate (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) : ℝ :=
  (RecordedQueueRun.acceptedArrival
    (RecordedQueueRun.acceptedRecord p state round i) : ℝ) / (p.n : ℝ)

theorem normalizedQuantizedArrival_eq_quantizedValue_of_recorded
    (p : RecordedQueueRun.Parameters) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) (hrecorded : round.recordedArm = some i) :
    normalizedQuantizedArrival p round i =
      QuantizedRecordingMoments.quantizedValue p.D p.eta (round.rate i) (round.reward i) := by
  unfold normalizedQuantizedArrival
  rw [RecordedQueueRun.quantizedArrival_eq_floor p round i hrecorded]
  have hnum : (p.n : ℝ) * round.reward i / round.rate i =
      ((p.D : ℝ) * p.eta * round.reward i) / round.rate i := by
    rw [p.n_eq_eta_mul_D]
    ring
  have hden : (p.n : ℝ) = p.eta * (p.D : ℝ) := p.n_eq_eta_mul_D
  change
    (Nat.floor ((p.n : ℝ) * round.reward i / round.rate i) : ℝ) / (p.n : ℝ) =
      (Nat.floor (((p.D : ℝ) * p.eta * round.reward i) / round.rate i) : ℝ) /
        (p.eta * (p.D : ℝ))
  rw [hnum, hden]

theorem rawEstimate_eq_normalizedQuantizedArrival_of_enabled
    (p : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState K)
    (round : RecordedQueueRun.RoundInput K) (i : Fin K)
    (henabled : round.enabled = true) (hnotOverflow : state.overflow = false) :
    rawEstimate p state round i = normalizedQuantizedArrival p round i := by
  simp [rawEstimate, normalizedQuantizedArrival,
    RecordedQueueRun.acceptedRecord, RecordedQueueRun.acceptedArrival,
    henabled, hnotOverflow]

theorem rawEstimate_eq_quantizedValue_of_enabled
    (p : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState K)
    (rates : RecordingRates K) (reward : Fin K → ℝ)
    (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Option (Fin K)) (i : Fin K)
    (hnotOverflow : state.overflow = false) :
    rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i =
        if outcome = some i then
          QuantizedRecordingMoments.quantizedValue p.D p.eta
            (rates.rate i) (reward i)
        else 0 := by
  rw [rawEstimate_eq_normalizedQuantizedArrival_of_enabled p state
    (fixedRoundInput p rates reward reward_mem true outcome) i (by rfl) hnotOverflow]
  by_cases hrecorded : outcome = some i
  · simpa [hrecorded, fixedRoundInput] using
      normalizedQuantizedArrival_eq_quantizedValue_of_recorded p
        (fixedRoundInput p rates reward reward_mem true outcome) i hrecorded
  · simp [normalizedQuantizedArrival, RecordedQueueRun.quantizedArrival,
      fixedRoundInput, hrecorded]

theorem rawEstimate_eq_zero_of_disabled
    (p : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState K)
    (round : RecordedQueueRun.RoundInput K) (i : Fin K)
    (hdisabled : round.enabled = false) :
    rawEstimate p state round i = 0 := by
  simp [rawEstimate, RecordedQueueRun.acceptedRecord,
    RecordedQueueRun.acceptedArrival, hdisabled]

theorem rawEstimate_eq_zero_after_overflow
    (p : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState K)
    (round : RecordedQueueRun.RoundInput K) (i : Fin K)
    (hoverflow : state.overflow = true) :
    rawEstimate p state round i = 0 := by
  simp [rawEstimate, RecordedQueueRun.acceptedRecord,
    RecordedQueueRun.acceptedArrival, hoverflow]

theorem rawEstimate_nonneg (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (round : RecordedQueueRun.RoundInput K)
    (i : Fin K) : 0 ≤ rawEstimate p state round i := by
  unfold rawEstimate
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- Every outcome can have at most one arm with a nonzero accepted raw arrival. -/
theorem rawEstimate_at_most_one_arm
    (p : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState K)
    (rates : RecordingRates K) (reward : Fin K → ℝ)
    (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (outcome : Option (Fin K)) (i j : Fin K) (hij : i ≠ j) :
    rawEstimate p state (fixedRoundInput p rates reward reward_mem enabled outcome) i ≠ 0 →
      rawEstimate p state (fixedRoundInput p rates reward reward_mem enabled outcome) j = 0 := by
  intro hi
  by_contra hj
  have hji : outcome = some i := by
    by_contra hnot
    have hzero : rawEstimate p state
        (fixedRoundInput p rates reward reward_mem enabled outcome) i = 0 := by
      cases hoverflow : state.overflow <;> cases enabled <;>
        simp [rawEstimate, RecordedQueueRun.acceptedRecord,
          RecordedQueueRun.acceptedArrival, RecordedQueueRun.quantizedArrival,
          fixedRoundInput, hoverflow, hnot]
    exact hi hzero
  have hjj : outcome = some j := by
    by_contra hnot
    have hzero : rawEstimate p state
        (fixedRoundInput p rates reward reward_mem enabled outcome) j = 0 := by
      cases hoverflow : state.overflow <;> cases enabled <;>
        simp [rawEstimate, RecordedQueueRun.acceptedRecord,
          RecordedQueueRun.acceptedArrival, RecordedQueueRun.quantizedArrival,
          fixedRoundInput, hoverflow, hnot]
    exact hj hzero
  rw [hji] at hjj
  injection hjj with hij'
  exact hij hij'

/-- Every function on this finite discrete outcome space is measurable. -/
theorem measurable_on_recording_outcomes {α : Type*} [MeasurableSpace α]
    (f : Option (Fin K) → α) : Measurable f := Measurable.of_discrete

theorem rawEstimate_measurable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (i : Fin K) :
    Measurable (fun outcome => rawEstimate p state
      (fixedRoundInput p rates reward reward_mem enabled outcome) i) :=
  measurable_on_recording_outcomes _

theorem rawEstimate_sq_measurable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (i : Fin K) :
    Measurable (fun outcome =>
      (rawEstimate p state
        (fixedRoundInput p rates reward reward_mem enabled outcome) i) ^ 2) :=
  measurable_on_recording_outcomes _

theorem rawEstimate_integrable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (i : Fin K) :
    Integrable (fun outcome => rawEstimate p state
      (fixedRoundInput p rates reward reward_mem enabled outcome) i)
      (recordingOutcomePMF rates).toMeasure := by
  exact Integrable.of_finite

theorem rawEstimate_sq_integrable (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) (i : Fin K) :
    Integrable (fun outcome =>
      (rawEstimate p state
        (fixedRoundInput p rates reward reward_mem enabled outcome) i) ^ 2)
      (recordingOutcomePMF rates).toMeasure := by
  exact Integrable.of_finite

theorem rawEstimate_firstMoment_eq (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (hnotOverflow : state.overflow = false) :
    ∫ outcome, rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i
      ∂(recordingOutcomePMF rates).toMeasure =
        rates.rate i * QuantizedRecordingMoments.quantizedValue p.D p.eta
          (rates.rate i) (reward i) := by
  rw [PMF.integral_eq_sum]
  simp [rawEstimate_eq_quantizedValue_of_enabled, recordingOutcomePMF,
    outcomeMass, hnotOverflow, ENNReal.toReal_ofReal,
    RecordingRates.rate_nonneg, smul_eq_mul]

theorem rawEstimate_secondMoment_eq (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (hnotOverflow : state.overflow = false) :
    ∫ outcome, (rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i) ^ 2
      ∂(recordingOutcomePMF rates).toMeasure =
        rates.rate i *
          (QuantizedRecordingMoments.quantizedValue p.D p.eta
            (rates.rate i) (reward i)) ^ 2 := by
  rw [PMF.integral_eq_sum]
  simp [rawEstimate_eq_quantizedValue_of_enabled, recordingOutcomePMF,
    outcomeMass, hnotOverflow, ENNReal.toReal_ofReal,
    RecordingRates.rate_nonneg, smul_eq_mul]

/-- The PMF first moment obeys the manuscript's rounding-error and upper bounds. -/
theorem rawEstimate_firstMoment_bounds (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (hnotOverflow : state.overflow = false) :
    reward i - rates.rate i / (p.eta * (p.D : ℝ)) ≤
        ∫ outcome, rawEstimate p state
          (fixedRoundInput p rates reward reward_mem true outcome) i
          ∂(recordingOutcomePMF rates).toMeasure ∧
      ∫ outcome, rawEstimate p state
        (fixedRoundInput p rates reward reward_mem true outcome) i
        ∂(recordingOutcomePMF rates).toMeasure ≤ reward i ∧
      reward i ≤ 1 := by
  rw [rawEstimate_firstMoment_eq p state rates reward reward_mem i hnotOverflow]
  refine ⟨?_, ?_, (reward_mem i).2⟩
  · exact QuantizedRecordingMoments.quantizedValue_roundingError p.D p.eta
      (rates.rate i) (reward i) p.D_pos p.eta_pos (rates.rate_pos i) (reward_mem i)
  · exact QuantizedRecordingMoments.quantizedValue_firstMoment_le p.D p.eta
      (rates.rate i) (reward i) p.D_pos p.eta_pos (rates.rate_pos i) (reward_mem i)

/-- The PMF second moment obeys the manuscript's inverse-rate bound. -/
theorem rawEstimate_secondMoment_bounds (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (hnotOverflow : state.overflow = false) :
    ∫ outcome, (rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i) ^ 2
      ∂(recordingOutcomePMF rates).toMeasure ≤ reward i ^ 2 / rates.rate i ∧
    ∫ outcome, (rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i) ^ 2
      ∂(recordingOutcomePMF rates).toMeasure ≤ 1 / rates.rate i := by
  rw [rawEstimate_secondMoment_eq p state rates reward reward_mem i hnotOverflow]
  have hquant := QuantizedRecordingMoments.quantizedValue_secondMoment_le p.D p.eta
    (rates.rate i) (reward i) p.D_pos p.eta_pos (rates.rate_pos i) (reward_mem i)
  have hreward_sq : reward i ^ 2 ≤ 1 := by nlinarith [(reward_mem i).1, (reward_mem i).2]
  exact ⟨hquant, (hquant.trans <| div_le_div_of_nonneg_right hreward_sq
    (rates.rate_pos i).le)⟩

/-- On an enabled pre-overflow outcome, the pointwise raw estimate is in the
source range, for any explicit positive `beta ≤ xi_i`. -/
theorem rawEstimate_pointwise_bounds (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin K) (hnotOverflow : state.overflow = false)
    (beta : ℝ) (hbeta_pos : 0 < beta) (hbeta_le : beta ≤ rates.rate i)
    (outcome : Option (Fin K)) :
    0 ≤ rawEstimate p state
        (fixedRoundInput p rates reward reward_mem true outcome) i ∧
      rawEstimate p state
        (fixedRoundInput p rates reward reward_mem true outcome) i ≤ 1 / beta := by
  rw [rawEstimate_eq_quantizedValue_of_enabled p state rates reward reward_mem
    outcome i hnotOverflow]
  by_cases hrecorded : outcome = some i
  · simpa [hrecorded] using
      (And.intro
        (QuantizedRecordingMoments.quantizedValue_nonneg p.D p.eta
          (rates.rate i) (reward i) p.eta_pos)
        (QuantizedRecordingMoments.quantizedValue_le_inv_of_beta_le p.D p.eta
          (rates.rate i) (reward i) beta p.D_pos p.eta_pos (rates.rate_pos i)
          (reward_mem i) hbeta_pos hbeta_le))
  · simpa [hrecorded] using
      (show 0 ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ 1 / beta from
        ⟨le_rfl, one_div_nonneg.mpr hbeta_pos.le⟩)

/-- The convex chord bound for the exponential on the unit interval. -/
theorem exp_le_unit_chord {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + (Real.exp 1 - 1) * x := by
  calc
    Real.exp x = Real.exp (x • (1 : ℝ) + (1 - x) • (0 : ℝ)) := by simp
    _ ≤ x • Real.exp 1 + (1 - x) • Real.exp 0 :=
      convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) hx0
        (by linarith) (by ring)
    _ = 1 + (Real.exp 1 - 1) * x := by
      simp only [smul_eq_mul, Real.exp_zero]
      ring

/-- The immediate one-round exponential estimate under the finite logical
recording law. The proof uses the already established pointwise and first
moment bounds; it makes no claim about a physical conditional law. -/
theorem rawEstimate_exponentialMoment_le_one
    (p : RecordedQueueRun.Parameters) (state : RecordedQueueRun.RunState K)
    (rates : RecordingRates K) (reward : Fin K → ℝ)
    (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1) (i : Fin K)
    (hnotOverflow : state.overflow = false) (beta : ℝ)
    (hbeta_pos : 0 < beta) (hbeta_le : beta ≤ rates.rate i) :
    ∫ outcome, Real.exp (beta * (rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i - 4))
      ∂(recordingOutcomePMF rates).toMeasure ≤ 1 := by
  let μ := (recordingOutcomePMF rates).toMeasure
  let raw : Option (Fin K) → ℝ := fun outcome =>
    rawEstimate p state (fixedRoundInput p rates reward reward_mem true outcome) i
  let c : ℝ := Real.exp (-4 * beta)
  let d : ℝ := Real.exp 1 - 1
  have hpoint : ∀ outcome,
      Real.exp (beta * (raw outcome - 4)) ≤ c * (1 + d * beta * raw outcome) := by
    intro outcome
    have hraw := rawEstimate_pointwise_bounds p state rates reward reward_mem i
      hnotOverflow beta hbeta_pos hbeta_le outcome
    have hx0 : 0 ≤ beta * raw outcome := mul_nonneg hbeta_pos.le hraw.1
    have hx1 : beta * raw outcome ≤ 1 := by
      calc
        beta * raw outcome ≤ beta * (1 / beta) :=
          mul_le_mul_of_nonneg_left hraw.2 hbeta_pos.le
        _ = 1 := by field_simp [ne_of_gt hbeta_pos]
    have hchord := exp_le_unit_chord hx0 hx1
    calc
      Real.exp (beta * (raw outcome - 4)) =
          Real.exp (-4 * beta) * Real.exp (beta * raw outcome) := by
        rw [show beta * (raw outcome - 4) = -4 * beta + beta * raw outcome by ring,
          Real.exp_add]
      _ ≤ Real.exp (-4 * beta) *
          (1 + (Real.exp 1 - 1) * (beta * raw outcome)) :=
        mul_le_mul_of_nonneg_left hchord (Real.exp_nonneg _)
      _ = c * (1 + d * beta * raw outcome) := by
        dsimp [c, d]
        ring
  have hrawInt : Integrable raw μ := by
    exact Integrable.of_finite
  have hexpInt : Integrable (fun outcome => Real.exp (beta * (raw outcome - 4))) μ := by
    exact Integrable.of_finite
  have hlineInt : Integrable (fun outcome => c * (1 + d * beta * raw outcome)) μ := by
    exact Integrable.of_finite
  have hmono := integral_mono hexpInt hlineInt hpoint
  have hline :
      ∫ outcome, c * (1 + d * beta * raw outcome) ∂μ =
        c * (1 + d * beta * (∫ outcome, raw outcome ∂μ)) := by
    rw [integral_const_mul, integral_add (integrable_const _) (hrawInt.const_mul (d * beta)),
      integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hmean := rawEstimate_firstMoment_bounds p state rates reward reward_mem i hnotOverflow
  have hmean_le_one : (∫ outcome, raw outcome ∂μ) ≤ 1 := by
    exact hmean.2.1.trans (reward_mem i).2
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    linarith [Real.exp_one_gt_two]
  have hcoef_nonneg : 0 ≤ d * beta := mul_nonneg hd_nonneg hbeta_pos.le
  have hbracket : 1 + d * beta * (∫ outcome, raw outcome ∂μ) ≤ Real.exp (d * beta) := by
    calc
      1 + d * beta * (∫ outcome, raw outcome ∂μ) ≤ 1 + d * beta := by
        have hmul := mul_le_mul_of_nonneg_left hmean_le_one hcoef_nonneg
        linarith
      _ ≤ Real.exp (d * beta) := by
        simpa [add_comm] using Real.add_one_le_exp (d * beta)
  have hexpExponent_nonpos : (d - 4) * beta ≤ 0 := by
    dsimp [d]
    have hExp : Real.exp 1 < 3 := Real.exp_one_lt_three
    nlinarith
  calc
    ∫ outcome, Real.exp (beta * (raw outcome - 4)) ∂μ ≤
        ∫ outcome, c * (1 + d * beta * raw outcome) ∂μ := hmono
    _ = c * (1 + d * beta * (∫ outcome, raw outcome ∂μ)) := hline
    _ ≤ c * Real.exp (d * beta) :=
      mul_le_mul_of_nonneg_left hbracket (Real.exp_nonneg _)
    _ = Real.exp ((d - 4) * beta) := by
      dsimp [c]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ 1 := Real.exp_le_one_iff.mpr hexpExponent_nonpos

/-- A disabled input emits zero raw arrivals and the accepted queue step
preserves every score/backlog register. -/
theorem disabledRound_zero_and_preserves (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Option (Fin K)) :
    (∀ i, rawEstimate p state
      (fixedRoundInput p rates reward reward_mem false outcome) i = 0) ∧
      (∀ i, (RecordedQueueRun.step p state
        (fixedRoundInput p rates reward reward_mem false outcome)).registers i =
          state.registers i) := by
  constructor
  · intro i
    exact rawEstimate_eq_zero_of_disabled p state
      (fixedRoundInput p rates reward reward_mem false outcome) i rfl
  · intro i
    exact (RecordedQueueRun.step_disabled_preserves p state
      (fixedRoundInput p rates reward reward_mem false outcome) rfl i).1

/-- A post-overflow input emits zero raw arrivals and the accepted queue step
preserves every score/backlog register. -/
theorem overflowedRound_zero_and_preserves (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Option (Fin K)) (hoverflow : state.overflow = true) :
    (∀ i, rawEstimate p state
      (fixedRoundInput p rates reward reward_mem true outcome) i = 0) ∧
      (∀ i, (RecordedQueueRun.step p state
        (fixedRoundInput p rates reward reward_mem true outcome)).registers i =
          state.registers i) := by
  constructor
  · intro i
    exact rawEstimate_eq_zero_after_overflow p state
      (fixedRoundInput p rates reward reward_mem true outcome) i hoverflow
  · intro i
    exact (RecordedQueueRun.step_after_overflow_preserves p state
      (fixedRoundInput p rates reward reward_mem true outcome) hoverflow i).1

/-- The first overflowing update is still evaluated from its pre-overflow
state, so it receives the same pointwise and moment bounds as any other
enabled round. -/
theorem firstOverflowStep_raw_bounds (p : RecordedQueueRun.Parameters)
    (state : RecordedQueueRun.RunState K) (rates : RecordingRates K)
    (reward : Fin K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Option (Fin K)) (hnotOverflow : state.overflow = false)
    (hfirstOverflow :
      (RecordedQueueRun.step p state
        (fixedRoundInput p rates reward reward_mem true outcome)).overflow = true)
    (beta : ℝ) (hbeta_pos : 0 < beta)
    (hbeta_le : ∀ i, beta ≤ rates.rate i) :
    (∃ i, 32 * ((RecordedQueueRun.step p state
      (fixedRoundInput p rates reward reward_mem true outcome)).registers i).2 > p.D) ∧
      (∀ i,
        (0 ≤ rawEstimate p state
          (fixedRoundInput p rates reward reward_mem true outcome) i ∧
          rawEstimate p state
            (fixedRoundInput p rates reward reward_mem true outcome) i ≤ 1 / beta) ∧
        (reward i - rates.rate i / (p.eta * (p.D : ℝ)) ≤
          ∫ draw, rawEstimate p state
            (fixedRoundInput p rates reward reward_mem true draw) i
            ∂(recordingOutcomePMF rates).toMeasure ∧
          ∫ draw, rawEstimate p state
            (fixedRoundInput p rates reward reward_mem true draw) i
            ∂(recordingOutcomePMF rates).toMeasure ≤ reward i ∧
          reward i ≤ 1) ∧
        (∫ draw, (rawEstimate p state
          (fixedRoundInput p rates reward reward_mem true draw) i) ^ 2
            ∂(recordingOutcomePMF rates).toMeasure ≤ reward i ^ 2 / rates.rate i ∧
          ∫ draw, (rawEstimate p state
            (fixedRoundInput p rates reward reward_mem true draw) i) ^ 2
              ∂(recordingOutcomePMF rates).toMeasure ≤ 1 / rates.rate i)) := by
  refine ⟨(RecordedQueueRun.step_retains_first_overflow_update p state
    (fixedRoundInput p rates reward reward_mem true outcome) hnotOverflow
    hfirstOverflow).1, ?_⟩
  intro i
  exact ⟨rawEstimate_pointwise_bounds p state rates reward reward_mem i
      hnotOverflow beta hbeta_pos (hbeta_le i) outcome,
    rawEstimate_firstMoment_bounds p state rates reward reward_mem i hnotOverflow,
    rawEstimate_secondMoment_bounds p state rates reward reward_mem i hnotOverflow⟩

end Bandits.Support.RecordedRoundMoments

end
