/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedMarginalGrowth
public import Bandits.Support.RecordedRoundMoments
public import Bandits.Support.StoppedQueueBound
public import Bandits.Support.CanonicalRecordingRates
public import Bandits.Support.RecordedEpisodeStability
public import Bandits.Support.QueueSquareDrift

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-step expected weighted-square drift of the recorded queue

The literal potential is `∑ i, θ_m(scoreWeight(state), i) * b(state,i)^2`.
The final theorem integrates the existing finite recording-outcome PMF and
applies the existing queue transition to a genuinely executed chronological
prefix. Its anchor is an actual earlier prefix within the episode horizon.
The canonical-rate adapter is explicit: this module does not construct the
canonical process or assert its physical conditional recording law.

Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:96-174,182-187,245-318`.
In particular, only the incoming overflow flag controls retention. Every
outcome of the first crossing update remains in the expectation, and enabled
zero-arrival outcomes still serve queues. Disabled and previously overflowed
steps preserve the potential. This is internal one-step mathematics, not a
manuscript closure or a finite-tree iteration/telescoping result.
-/

@[expose] public section

namespace Bandits.Support.RecordedWeightedDrift

open MeasureTheory
open RecordedQueueRun RecordedRoundMoments StoppedQueueBound
open scoped BigOperators

variable {K : ℕ}

/-- The source weighted-square queue potential, with current score weights. -/
noncomputable def weightedSquarePotential (m : ℕ) (q : Parameters)
    (state : RunState K) : ℝ :=
  ∑ i : Fin K, ProductSetLaw.theta m (scoreWeight q state) i *
    normalizedBacklog q state i ^ 2

/-- The source weighted backlog, using the same current inclusion marginals. -/
noncomputable def weightedBacklog (m : ℕ) (q : Parameters)
    (state : RunState K) : ℝ :=
  ∑ i : Fin K, ProductSetLaw.theta m (scoreWeight q state) i *
    normalizedBacklog q state i

/-- The literal source learning-rate cap implies the numerical cap used by
the accepted marginal-growth producer. No additional small-rate input occurs. -/
theorem eta_le_one_div_sixtyFour (p : ConstructorDimensions.Parameters)
    (q : Parameters)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ))) :
    q.eta ≤ 1 / 64 := by
  have hm : (1 : ℝ) ≤ (p.m : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.m_pos p)
  have hK : (1 : ℝ) ≤ (p.K : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (ConstructorDimensions.K_pos p)
  have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
    exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
  have hmk : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) :=
    one_le_mul_of_one_le_of_one_le hm hK
  have hprod : (1 : ℝ) ≤ (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ) :=
    one_le_mul_of_one_le_of_one_le hmk hL
  have hden : (64 : ℝ) ≤
      1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
    nlinarith only [hprod]
  exact hcap.trans (one_div_le_one_div_of_le (by norm_num) hden)

/-- The actual anchor/current weight envelope comes from execution of the
actual suffix. It is not an extra condition on the incoming state. -/
theorem actual_anchor_envelope (q : Parameters) (past : List (RoundInput K))
    (a : ℕ) (ha : a ≤ past.length)
    (hlen : past.length - a ≤ ReplayWeightStability.episodeHorizon q.eta)
    (i : Fin K) :
    0 < scoreWeight q (run q (past.take a)) i ∧
      scoreWeight q (run q (past.take a)) i ≤ scoreWeight q (run q past) i ∧
      scoreWeight q (run q past) i < 2 * scoreWeight q (run q (past.take a)) i := by
  have hexec := RecordedEpisodeStability.run_take_eq_execute_drop q past
    a past.length ha
  simp only [List.take_length] at hexec
  have hsuffix : ((past.drop a).take (past.length - a)).length ≤
      ReplayWeightStability.episodeHorizon q.eta := by
    exact (List.length_take_le _ _).trans hlen
  have henv := RecordedEpisodeStability.execute_source_weight_envelope q
    (run q (past.take a)) ((past.drop a).take (past.length - a)) i hsuffix
  rw [← hexec] at henv
  exact ⟨RecordedMarginalGrowth.state_scoreWeight_pos q _ i, henv.1, henv.2.1⟩

/-- Both lower bounds on canonical recording rates are derived from the
explicit rate-field equality, including the source `β = 32 η L_stab`. -/
theorem canonical_rate_lower_bounds (p : ConstructorDimensions.Parameters)
    (q : Parameters) (anchor : Fin p.K → ℝ) (rates : RecordingRates p.K)
    (hrates : rates.rate = CanonicalRecordingRates.xi p q.eta anchor)
    (i : Fin p.K) :
    CanonicalRecordingRates.beta p q.eta ≤ rates.rate i ∧
      32 * q.eta ≤ rates.rate i := by
  rw [hrates]
  exact ⟨CanonicalRecordingRates.beta_le_xi p q.eta_pos anchor i,
    CanonicalRecordingRates.thirtyTwo_mul_eta_le_xi p q.eta_pos anchor i⟩

private theorem normalized_residual (q : Parameters) (b r : ℕ) :
    (((b + r - 4 * q.n : ℕ) : ℝ) / (q.n : ℝ)) =
      max 0 ((b : ℝ) / (q.n : ℝ) + (r : ℝ) / (q.n : ℝ) - 4) := by
  have hn : (0 : ℝ) < (q.n : ℝ) := Nat.cast_pos.mpr q.n_pos
  by_cases h : 4 * q.n ≤ b + r
  · have hreal : (4 : ℝ) * (q.n : ℝ) ≤ (b : ℝ) + (r : ℝ) := by
      exact_mod_cast h
    have hpos : 0 ≤ (b : ℝ) / (q.n : ℝ) + (r : ℝ) / (q.n : ℝ) - 4 := by
      apply (nonneg_of_mul_nonneg_right ?_ hn)
      field_simp
      linarith only [hreal]
    rw [Nat.cast_sub h, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      max_eq_right hpos]
    field_simp
  · have hle : b + r ≤ 4 * q.n := Nat.le_of_not_ge h
    have hreal : (b : ℝ) + (r : ℝ) ≤ (4 : ℝ) * (q.n : ℝ) := by
      exact_mod_cast hle
    have hneg : (b : ℝ) / (q.n : ℝ) + (r : ℝ) / (q.n : ℝ) - 4 ≤ 0 := by
      apply (nonpos_of_mul_nonpos_right ?_ hn)
      field_simp
      linarith only [hreal]
    rw [Nat.sub_eq_zero_of_le hle, Nat.cast_zero, zero_div, max_eq_left hneg]

/-- The actual enabled, retained natural queue update gives exactly the source
normalized recursion. The outgoing flag and the recorded-arm value are unrestricted. -/
theorem normalizedBacklog_step_eq_queueNext (q : Parameters) (state : RunState K)
    (round : RoundInput K) (henabled : round.enabled = true)
    (hnotOverflow : state.overflow = false) (i : Fin K) :
    normalizedBacklog q (step q state round) i =
      QueueSquareDrift.queueNext (normalizedBacklog q state i)
        (rawEstimate q state round i) := by
  have hreg : ((step q state round).registers i).2 =
      CappedService.residual (4 * q.n) (state.registers i).2
        (quantizedArrival q round i) := by
    simp only [step, acceptedRecord, hnotOverflow, Bool.false_eq_true, ite_false,
      henabled, ite_true, QueueReplay.transition, CappedService.residual,
      CappedService.service]
  rw [normalizedBacklog, hreg, CappedService.residual_eq_sub_capacity,
    rawEstimate_eq_normalizedQuantizedArrival_of_enabled q state round i
      henabled hnotOverflow]
  exact normalized_residual q _ _

/-- The accepted stopped-queue theorem applied to the actual appended prefix
bounds every successor outcome, including a first overflow crossing. -/
theorem successor_normalizedBacklog_le (q : Parameters) (past : List (RoundInput K))
    (hpast : ∀ round ∈ past, ∀ i, 32 * q.eta ≤ round.rate i)
    (round : RoundInput K) (hrate : ∀ i, 32 * q.eta ≤ round.rate i) (i : Fin K) :
    normalizedBacklog q (step q (run q past) round) i ≤ 2 * (1 / (32 * q.eta)) := by
  have hall : ∀ r ∈ past ++ [round], ∀ j, 32 * q.eta ≤ r.rate j := by
    intro r hr j
    rcases List.mem_append.mp hr with hp | hc
    · exact hpast r hp j
    · have heq : r = round := List.mem_singleton.mp hc
      subst r
      exact hrate j
  have h := run_prefix_normalized_backlog_le_twice_threshold q (past ++ [round])
    hall (past ++ [round]).length i
  simpa only [List.take_length, run, RecordedEpisodeStability.execute_append,
    execute] using h

/-- The cap coefficient in the manuscript calculation is an exact identity. -/
theorem sixteen_eta_mul_backlogCap (q : Parameters) :
    16 * q.eta * (1 / (32 * q.eta)) = (1 / 2 : ℝ) := by
  field_simp [ne_of_gt q.eta_pos]
  ring

/-- Disabled and incoming-overflowed rounds preserve the literal potential;
the record-history field may still grow, but is absent from the potential. -/
theorem weightedSquarePotential_step_eq_of_disabled_or_overflowed
    (m : ℕ) (q : Parameters) (state : RunState K) (round : RoundInput K)
    (hstop : round.enabled = false ∨ state.overflow = true) :
    weightedSquarePotential m q (step q state round) =
      weightedSquarePotential m q state := by
  have hreg : ∀ i, (step q state round).registers i = state.registers i := by
    intro i
    rcases hstop with hd | ho
    · exact (step_disabled_preserves q state round hd i).1
    · exact (step_after_overflow_preserves q state round ho i).1
  have hw : scoreWeight q (step q state round) = scoreWeight q state := by
    funext i
    simp only [scoreWeight, hreg]
  unfold weightedSquarePotential
  rw [hw]
  apply Finset.sum_congr rfl
  intro i _
  simp only [normalizedBacklog, hreg]

private theorem integral_affine_square (rates : RecordingRates K)
    (r : Option (Fin K) → ℝ) (c d : ℝ) :
    (∫ outcome, c * r outcome + r outcome ^ 2 + d
      ∂(recordingOutcomePMF rates).toMeasure) =
      c * (∫ outcome, r outcome ∂(recordingOutcomePMF rates).toMeasure) +
      (∫ outcome, r outcome ^ 2 ∂(recordingOutcomePMF rates).toMeasure) + d := by
  rw [integral_add (Integrable.of_finite) (integrable_const d),
    integral_add (Integrable.of_finite) (Integrable.of_finite), integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul]

/-- Each coordinate's genuine finite-outcome expectation obeys the source
drift calculation. Growth, square comparison, successor cap, and moments are
all produced in the proof rather than supplied as premises. -/
theorem expected_coordinate_drift (p : ConstructorDimensions.Parameters)
    (q : Parameters) (past : List (RoundInput p.K))
    (hpast : ∀ round ∈ past, ∀ i, 32 * q.eta ≤ round.rate i)
    (heta : q.eta ≤ 1 / 64) (rates : RecordingRates p.K)
    (hrate : ∀ i, 32 * q.eta ≤ rates.rate i)
    (reward : Fin p.K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (hnotOverflow : (run q past).overflow = false) (i : Fin p.K) :
    (∫ outcome,
      ProductSetLaw.theta p.m (scoreWeight q
        (step q (run q past) (fixedRoundInput q rates reward reward_mem true outcome))) i *
        normalizedBacklog q
          (step q (run q past) (fixedRoundInput q rates reward reward_mem true outcome)) i ^ 2 -
        ProductSetLaw.theta p.m (scoreWeight q (run q past)) i *
          normalizedBacklog q (run q past) i ^ 2
      ∂(recordingOutcomePMF rates).toMeasure) ≤
      ProductSetLaw.theta p.m (scoreWeight q (run q past)) i *
        (-(11 / 2 : ℝ) * normalizedBacklog q (run q past) i +
          1 / rates.rate i + 33 / 2) := by
  let state := run q past
  let theta := ProductSetLaw.theta p.m (scoreWeight q state) i
  let b := normalizedBacklog q state i
  let r := fun outcome => rawEstimate q state
    (fixedRoundInput q rates reward reward_mem true outcome) i
  let next := fun outcome => step q state
    (fixedRoundInput q rates reward reward_mem true outcome)
  have hb : 0 ≤ b := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have ht : 0 ≤ theta := (RecordedMarginalGrowth.state_theta_pos q state i
    (ConstructorDimensions.m_pos p) p.m_lt_K).le
  have hpoint (outcome : Option (Fin p.K)) :
      ProductSetLaw.theta p.m (scoreWeight q (next outcome)) i *
          normalizedBacklog q (next outcome) i ^ 2 - theta * b ^ 2 ≤
        theta * ((2 * b + 1 / 2) * r outcome + r outcome ^ 2 +
          (-(15 / 2 : ℝ) * b + 16)) := by
    let bNext := normalizedBacklog q (next outcome) i
    have hr : 0 ≤ r outcome := rawEstimate_nonneg q state _ i
    have hrec : bNext = QueueSquareDrift.queueNext b (r outcome) :=
      normalizedBacklog_step_eq_queueNext q state _ rfl hnotOverflow i
    have hnext : bNext ≤ 2 * (1 / (32 * q.eta)) :=
      successor_normalizedBacklog_le q past hpast _ hrate i
    have hsq := QueueSquareDrift.queueNext_sq_sub_le b (r outcome) hb hr
    have hcap := QueueSquareDrift.queueNext_sq_le_cap_mul b (r outcome)
      (1 / (32 * q.eta)) hb hr (by positivity [q.eta_pos]) (by rwa [← hrec])
    rw [← hrec] at hsq hcap
    have hscaled := mul_le_mul_of_nonneg_left hcap
      (show 0 ≤ 8 * q.eta by positivity [q.eta_pos])
    have hcoef := sixteen_eta_mul_backlogCap q
    have hscaled' : 8 * q.eta * bNext ^ 2 ≤ (1 / 2 : ℝ) * (b + r outcome) := by
      calc
        8 * q.eta * bNext ^ 2 ≤
            8 * q.eta * (2 * (1 / (32 * q.eta)) * (b + r outcome)) := hscaled
        _ = (1 / 2 : ℝ) * (b + r outcome) := by
          calc
            _ = (16 * q.eta * (1 / (32 * q.eta))) * (b + r outcome) := by ring
            _ = _ := by rw [hcoef]
    have hinner : bNext ^ 2 - b ^ 2 + 8 * q.eta * bNext ^ 2 ≤
        (2 * b + 1 / 2) * r outcome + r outcome ^ 2 + (-(15 / 2 : ℝ) * b + 16) := by
      nlinarith only [hsq, hscaled']
    have hgrowth := RecordedMarginalGrowth.step_theta_growth q state
      (fixedRoundInput q rates reward reward_mem true outcome) i p.two_le_m p.m_lt_K heta
    exact (QueueSquareDrift.weighted_square_step _ theta q.eta bNext b ht q.eta_pos.le
      (hgrowth.1.trans hgrowth.2)).trans (mul_le_mul_of_nonneg_left hinner ht)
  have hmean : (∫ outcome, r outcome ∂(recordingOutcomePMF rates).toMeasure) ≤ 1 :=
    (rawEstimate_firstMoment_bounds q state rates reward reward_mem i hnotOverflow).2.1.trans
      (reward_mem i).2
  have hsecond : (∫ outcome, r outcome ^ 2 ∂(recordingOutcomePMF rates).toMeasure) ≤
      1 / rates.rate i :=
    (rawEstimate_secondMoment_bounds q state rates reward reward_mem i hnotOverflow).2
  have hmono := integral_mono
    (show Integrable (fun outcome =>
      ProductSetLaw.theta p.m (scoreWeight q (next outcome)) i *
        normalizedBacklog q (next outcome) i ^ 2 - theta * b ^ 2)
      (recordingOutcomePMF rates).toMeasure from Integrable.of_finite)
    (show Integrable (fun outcome => theta *
      ((2 * b + 1 / 2) * r outcome + r outcome ^ 2 + (-(15 / 2 : ℝ) * b + 16)))
      (recordingOutcomePMF rates).toMeasure from Integrable.of_finite) hpoint
  rw [integral_const_mul, integral_affine_square] at hmono
  have hmeanScaled := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ 2 * b + 1 / 2 by linarith only [hb])
  have hinnerMean :
      (2 * b + 1 / 2) * (∫ outcome, r outcome ∂(recordingOutcomePMF rates).toMeasure) +
        (∫ outcome, r outcome ^ 2 ∂(recordingOutcomePMF rates).toMeasure) +
        (-(15 / 2 : ℝ) * b + 16) ≤ -(11 / 2 : ℝ) * b + 1 / rates.rate i + 33 / 2 := by
    linarith only [hmeanScaled, hsecond]
  exact hmono.trans (mul_le_mul_of_nonneg_left hinnerMean ht)

/-- The actual one-step finite recording-outcome drift, with canonical rates
at an actual earlier anchor. The input `q.D = D p` records constructor identity;
the calculation itself uses the inherited exact `n = ηD` parameter relation.

The only adapter inputs are the typed chronological past and its visible rate
lower bound, an anchor index within the horizon, a valid rate object whose
field equals the literal canonical rates, a reward row in `[0,1]`, and the
enabled bit. There are no assumed drift, growth, moment, envelope, marginal-sum,
successor-backlog, or `R` bounds. Incoming overflow alone controls retention.
Source: `04_slow_fast_learner.tex:292-318`; this does not iterate the kernel. -/
theorem expected_weightedSquarePotential_drift
    (p : ConstructorDimensions.Parameters) (q : Parameters)
    (_hD : q.D = ConstructorDimensions.D p)
    (hcap : q.eta ≤ 1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
      (CanonicalRecordingRates.L_stab p : ℝ)))
    (past : List (RoundInput p.K))
    (hpast : ∀ round ∈ past, ∀ i, 32 * q.eta ≤ round.rate i)
    (a : ℕ) (ha : a ≤ past.length)
    (hlen : past.length - a ≤ ReplayWeightStability.episodeHorizon q.eta)
    (rates : RecordingRates p.K)
    (hrates : rates.rate = CanonicalRecordingRates.xi p q.eta
      (scoreWeight q (run q (past.take a))))
    (reward : Fin p.K → ℝ) (reward_mem : ∀ i, reward i ∈ Set.Icc (0 : ℝ) 1)
    (enabled : Bool) :
    (∫ outcome,
      weightedSquarePotential p.m q
        (step q (run q past) (fixedRoundInput q rates reward reward_mem enabled outcome)) -
        weightedSquarePotential p.m q (run q past)
      ∂(recordingOutcomePMF rates).toMeasure) ≤
      if enabled = true ∧ (run q past).overflow = false then
        -(11 / 2 : ℝ) * weightedBacklog p.m q (run q past) +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
      else 0 := by
  by_cases hretained : enabled = true ∧ (run q past).overflow = false
  · rw [ite_eq_left hretained, hretained.1]
    have heta := eta_le_one_div_sixtyFour p q hcap
    have hrate : ∀ i, 32 * q.eta ≤ rates.rate i := fun i =>
      (canonical_rate_lower_bounds p q _ rates hrates i).2
    have henvelope := fun i => actual_anchor_envelope q past a ha hlen i
    have hR : (∑ i : Fin p.K,
        ProductSetLaw.theta p.m (scoreWeight q (run q past)) i / rates.rate i) ≤
        CanonicalRecordingRates.R p := by
      rw [hrates]
      exact CanonicalRecordingRates.sum_theta_div_xi_le_R p q.eta_pos _ _
        (fun i => (henvelope i).1)
        (fun i => ⟨(henvelope i).2.1, (henvelope i).2.2.le⟩)
    have hsumtheta := RecordedMarginalGrowth.state_sum_theta_eq_m q (run q past)
      (ConstructorDimensions.m_pos p) p.m_lt_K
    have hexpand (outcome : Option (Fin p.K)) :
        weightedSquarePotential p.m q
          (step q (run q past) (fixedRoundInput q rates reward reward_mem true outcome)) -
            weightedSquarePotential p.m q (run q past) =
          ∑ i : Fin p.K,
            (ProductSetLaw.theta p.m (scoreWeight q
              (step q (run q past) (fixedRoundInput q rates reward reward_mem true outcome))) i *
              normalizedBacklog q
                (step q (run q past) (fixedRoundInput q rates reward reward_mem true outcome)) i ^ 2 -
              ProductSetLaw.theta p.m (scoreWeight q (run q past)) i *
                normalizedBacklog q (run q past) i ^ 2) := by
      exact (Finset.sum_sub_distrib _ _).symm
    simp_rw [hexpand]
    rw [integral_finsetSum Finset.univ (fun _ _ => Integrable.of_finite)]
    calc
      _ ≤ ∑ i : Fin p.K, ProductSetLaw.theta p.m (scoreWeight q (run q past)) i *
          (-(11 / 2 : ℝ) * normalizedBacklog q (run q past) i +
            1 / rates.rate i + 33 / 2) := by
        exact Finset.sum_le_sum fun i _ => expected_coordinate_drift p q past hpast
          heta rates hrate reward reward_mem hretained.2 i
      _ = -(11 / 2 : ℝ) * weightedBacklog p.m q (run q past) +
          (∑ i : Fin p.K,
            ProductSetLaw.theta p.m (scoreWeight q (run q past)) i / rates.rate i) +
          (33 / 2 : ℝ) * (p.m : ℝ) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hleft : (∑ i : Fin p.K,
            ProductSetLaw.theta p.m (scoreWeight q (run q past)) i *
              (-(11 / 2 : ℝ) * normalizedBacklog q (run q past) i)) =
            -(11 / 2 : ℝ) * weightedBacklog p.m q (run q past) := by
          unfold weightedBacklog
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [hleft, ← Finset.sum_mul, hsumtheta]
        simp only [div_eq_mul_inv, one_mul]
        ring
      _ ≤ _ := by linarith only [hR]
  · rw [ite_eq_right hretained]
    have hstop : enabled = false ∨ (run q past).overflow = true := by
      cases enabled <;> cases hflag : (run q past).overflow <;> simp_all
    have hzero (outcome : Option (Fin p.K)) :
        weightedSquarePotential p.m q
          (step q (run q past) (fixedRoundInput q rates reward reward_mem enabled outcome)) -
          weightedSquarePotential p.m q (run q past) = 0 := by
      rw [weightedSquarePotential_step_eq_of_disabled_or_overflowed p.m q _ _ hstop,
        sub_self]
    simp_rw [hzero]
    simp only [integral_zero, le_refl]

end Bandits.Support.RecordedWeightedDrift

end
