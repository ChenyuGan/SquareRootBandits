/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedQueueRun
public import Bandits.Support.ScoreWeightLogBounds
public import Bandits.Support.ProductSetDistribution

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-step potential of the actual recorded queue run

The served estimate is the literal service of `RecordedQueueRun.step`, divided
by its integer denominator. The exponential update, normalization, first moment,
and second moment below are derived from that machine and the accepted product
set law. No recording law or queue bound is an input.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`
(service and scores), `:182-215` (retain the first overflow update), and
`:393-412` (one-step log-normalizer comparison). These are internal results;
no cumulative learning, conditional expectation, or manuscript closure is claimed.
-/

public section

open scoped BigOperators

namespace Bandits.Support.RecordedPotentialStep

open RecordedQueueRun ProductSetLaw

variable {K m : ℕ}

/-- Actual served integer increment, in units of `n = eta * D`. -/
@[expose] noncomputable def servedEstimate (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) : ℝ :=
  (recordService (4 * p.n) (state.registers i)
    (acceptedRecord p state round i) : ℝ) / (p.n : ℝ)

/-- The literal logarithmic scale of the source score weights. -/
@[expose] noncomputable def potentialLambda (p : Parameters) : ℝ :=
  (p.D : ℝ) * Real.log (1 + 1 / (p.D : ℝ)) * p.eta

theorem servedEstimate_nonneg (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) : 0 ≤ servedEstimate p state round i :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem servedEstimate_le_four (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) : servedEstimate p state round i ≤ 4 := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr p.n_pos : (0 : ℝ) < p.n)).2
  exact_mod_cast step_service_le_capacity p state round i

theorem potentialLambda_le_eta (p : Parameters) : potentialLambda p ≤ p.eta := by
  have hD : (0 : ℝ) < p.D := Nat.cast_pos.mpr p.D_pos
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (ScoreWeightLogBounds.source_base_log_upper hD)
      hD.le) p.eta_pos.le
  simpa only [potentialLambda, mul_one_div_cancel hD.ne', one_mul] using h

theorem eta_div_two_le_potentialLambda (p : Parameters) :
    p.eta / 2 ≤ potentialLambda p := by
  have hD : (0 : ℝ) < p.D := Nat.cast_pos.mpr p.D_pos
  have hD1 : (1 : ℝ) ≤ p.D := by exact_mod_cast p.D_pos
  have hfrac : (1 : ℝ) / 2 ≤ (p.D : ℝ) * (1 / ((p.D : ℝ) + 1)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < p.D + 1)]
    linarith only [hD1]
  calc
    p.eta / 2 = (1 / 2 : ℝ) * p.eta := by ring
    _ ≤ ((p.D : ℝ) * (1 / ((p.D : ℝ) + 1))) * p.eta :=
      mul_le_mul_of_nonneg_right hfrac p.eta_pos.le
    _ ≤ potentialLambda p := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (ScoreWeightLogBounds.source_base_log_lower hD)
        hD.le) p.eta_pos.le

theorem potentialLambda_pos (p : Parameters) : 0 < potentialLambda p :=
  (half_pos p.eta_pos).trans_le (eta_div_two_le_potentialLambda p)

theorem scoreWeight_pos (p : Parameters) (state : RunState K) (i : Fin K) :
    0 < RecordedQueueRun.scoreWeight p state i :=
  ScoreWeights.scoreWeight_pos
    (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr p.D_pos)) _

/-- Exact actual weight ratio; the only scale identity used is `n = eta * D`. -/
theorem step_scoreWeight_ratio_exp (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) :
    RecordedQueueRun.scoreWeight p (step p state round) i /
        RecordedQueueRun.scoreWeight p state i =
      Real.exp (potentialLambda p * servedEstimate p state round i) := by
  rw [RecordedQueueRun.step_scoreWeight_ratio]
  have hscale : potentialLambda p * servedEstimate p state round i =
      (recordService (4 * p.n) (state.registers i)
        (acceptedRecord p state round i) : ℝ) *
          Real.log (1 + 1 / (p.D : ℝ)) := by
    unfold potentialLambda servedEstimate
    rw [p.n_eq_eta_mul_D]
    field_simp [p.eta_pos.ne', (Nat.cast_pos.mpr p.D_pos : (0 : ℝ) < p.D).ne']
  rw [hscale, Real.exp_nat_mul,
    Real.exp_log (ScoreWeights.sourceBase_pos (Nat.cast_pos.mpr p.D_pos))]

theorem step_scoreWeight_eq_mul_exp (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) :
    RecordedQueueRun.scoreWeight p (step p state round) i =
      RecordedQueueRun.scoreWeight p state i *
        Real.exp (potentialLambda p * servedEstimate p state round i) := by
  have h := (div_eq_iff (scoreWeight_pos p state i).ne').mp
    (step_scoreWeight_ratio_exp p state round i)
  exact h.trans (mul_comm _ _)

/-- Product weights are updated on the existing finite sets, with no new law. -/
theorem step_setWeight_eq_mul_exp (p : Parameters) (state : RunState K)
    (round : RoundInput K) (S : Finset (Fin K)) :
    setWeight (RecordedQueueRun.scoreWeight p (step p state round)) S =
      setWeight (RecordedQueueRun.scoreWeight p state) S *
        Real.exp (potentialLambda p * ∑ i ∈ S, servedEstimate p state round i) := by
  classical
  unfold setWeight
  simp_rw [step_scoreWeight_eq_mul_exp]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum]

private theorem normalizer_eq_productSet_sum (w : Fin K → ℝ) :
    normalizer m w = ∑ S : ProductSet K m, setWeight w S.1 := by
  rw [normalizer_eq_support_sum]
  exact Finset.sum_subtype (support K m) (by intro S; rfl) (setWeight w)

/-- The normalizer ratio is the exponential moment under the actual `Q`. -/
theorem normalizer_ratio_eq_exp_sum (p : Parameters) (state : RunState K)
    (round : RoundInput K) :
    normalizer m (RecordedQueueRun.scoreWeight p (step p state round)) /
        normalizer m (RecordedQueueRun.scoreWeight p state) =
      ∑ S : ProductSet K m, Q m (RecordedQueueRun.scoreWeight p state) S *
        Real.exp (potentialLambda p * ∑ i ∈ S.1, servedEstimate p state round i) := by
  classical
  rw [normalizer_eq_productSet_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  rw [step_setWeight_eq_mul_exp]
  change _ / _ = (setWeight _ S.1 / normalizer m _) * _
  ring

theorem servedEstimate_sum_bounds (p : Parameters) (state : RunState K)
    (round : RoundInput K) (S : ProductSet K m) :
    0 ≤ ∑ i ∈ S.1, servedEstimate p state round i ∧
      (∑ i ∈ S.1, servedEstimate p state round i) ≤ 4 * (m : ℝ) := by
  classical
  have hcard : S.1.card = m := (Finset.mem_powersetCard.mp S.2).2
  constructor
  · exact Finset.sum_nonneg fun i _ => servedEstimate_nonneg p state round i
  · calc
      _ ≤ ∑ _i ∈ S.1, (4 : ℝ) :=
        Finset.sum_le_sum fun i _ => servedEstimate_le_four p state round i
      _ = 4 * (m : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        ring

/-- The source smallness premise gives the full interval `[0,1]`. -/
theorem exponent_bounds (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hsmall : 4 * (m : ℝ) * p.eta ≤ 1)
    (S : ProductSet K m) :
    0 ≤ potentialLambda p * (∑ i ∈ S.1, servedEstimate p state round i) ∧
      potentialLambda p * (∑ i ∈ S.1, servedEstimate p state round i) ≤ 1 := by
  have hs := servedEstimate_sum_bounds p state round S
  constructor
  · exact mul_nonneg (potentialLambda_pos p).le hs.1
  · calc
      _ ≤ potentialLambda p * (4 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hs.2 (potentialLambda_pos p).le
      _ ≤ p.eta * (4 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_right (potentialLambda_le_eta p) (by positivity)
      _ ≤ 1 := by nlinarith only [hsmall]

/-- The real quadratic bound on the entire source interval, from Mathlib's
exponential remainder bound, without a smaller interval or changed constant. -/
theorem exp_le_one_add_add_sq {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hxnorm : ‖x‖ = x := Real.norm_of_nonneg hx0
  have h := Real.norm_exp_sub_one_sub_id_le (hxnorm ▸ hx1)
  rw [hxnorm, Real.norm_eq_abs] at h
  have hle := (le_abs_self (Real.exp x - 1 - x)).trans h
  linarith only [hle]

/-- Reindexing the first moment uses exactly the accepted inclusion marginal. -/
theorem servedEstimate_first_moment (p : Parameters) (state : RunState K)
    (round : RoundInput K) :
    (∑ S : ProductSet K m, Q m (RecordedQueueRun.scoreWeight p state) S *
        ∑ i ∈ S.1, servedEstimate p state round i) =
      ∑ i, theta m (RecordedQueueRun.scoreWeight p state) i *
        servedEstimate p state round i := by
  classical
  simp_rw [ProductSetDistribution.theta_eq_sum_productSet_Q, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  simp only [ite_mul, zero_mul, Finset.sum_ite_mem_eq, Finset.mul_sum]

/-- The second moment is bounded using actual service and normalized `Q`. -/
theorem servedEstimate_second_moment_le (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hm : 2 ≤ m) (hmK : m < K) :
    (∑ S : ProductSet K m, Q m (RecordedQueueRun.scoreWeight p state) S *
      (∑ i ∈ S.1, servedEstimate p state round i) ^ 2) ≤ 16 * (m : ℝ) ^ 2 := by
  classical
  have hm0 : 0 < m := by omega
  calc
    _ ≤ ∑ S : ProductSet K m,
        Q m (RecordedQueueRun.scoreWeight p state) S * (16 * (m : ℝ) ^ 2) := by
      apply Finset.sum_le_sum
      intro S _
      apply mul_le_mul_of_nonneg_left _
        (Q_pos _ hm0 hmK (scoreWeight_pos p state) S).le
      have hs := servedEstimate_sum_bounds p state round S
      have hsq := (sq_le_sq₀ hs.1 (by positivity)).2 hs.2
      nlinarith only [hsq]
    _ = 16 * (m : ℝ) ^ 2 := by
      rw [← Finset.sum_mul, Q_sum_eq_one _ hm0 hmK (scoreWeight_pos p state), one_mul]

/-- One-step log-normalizer inequality for the actual accepted queue step.
It has no restriction on the incoming or outgoing overflow flag, and therefore
includes the update which first triggers overflow.
Source: `sources/zip4/manuscript/04_slow_fast_learner.tex:393-408`. -/
theorem step_log_normalizer_le (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hm : 2 ≤ m) (hmK : m < K)
    (hsmall : 4 * (m : ℝ) * p.eta ≤ 1) :
    Real.log (normalizer m (RecordedQueueRun.scoreWeight p (step p state round)) /
        normalizer m (RecordedQueueRun.scoreWeight p state)) ≤
      potentialLambda p * (∑ i, theta m (RecordedQueueRun.scoreWeight p state) i *
        servedEstimate p state round i) +
      potentialLambda p ^ 2 * (∑ S : ProductSet K m,
        Q m (RecordedQueueRun.scoreWeight p state) S *
          (∑ i ∈ S.1, servedEstimate p state round i) ^ 2) := by
  classical
  have hm0 : 0 < m := by omega
  have hratio : 0 < normalizer m
      (RecordedQueueRun.scoreWeight p (step p state round)) /
        normalizer m (RecordedQueueRun.scoreWeight p state) :=
    div_pos (normalizer_pos _ hm0 hmK (scoreWeight_pos p (step p state round)))
      (normalizer_pos _ hm0 hmK (scoreWeight_pos p state))
  have hquad := Finset.sum_le_sum (s := (Finset.univ : Finset (ProductSet K m)))
    (fun S _ => mul_le_mul_of_nonneg_left
      (exp_le_one_add_add_sq (exponent_bounds p state round hsmall S).1
        (exponent_bounds p state round hsmall S).2)
      (Q_pos _ hm0 hmK (scoreWeight_pos p state) S).le)
  have halgebra :
      (∑ S : ProductSet K m, Q m (RecordedQueueRun.scoreWeight p state) S *
        (1 + potentialLambda p * (∑ i ∈ S.1, servedEstimate p state round i) +
          (potentialLambda p * (∑ i ∈ S.1, servedEstimate p state round i)) ^ 2)) =
      1 + potentialLambda p * (∑ i, theta m (RecordedQueueRun.scoreWeight p state) i *
        servedEstimate p state round i) + potentialLambda p ^ 2 *
          (∑ S : ProductSet K m, Q m (RecordedQueueRun.scoreWeight p state) S *
            (∑ i ∈ S.1, servedEstimate p state round i) ^ 2) := by
    simp_rw [mul_add, mul_one, mul_pow]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Q_sum_eq_one _ hm0 hmK (scoreWeight_pos p state)]
    simp_rw [← mul_assoc, mul_comm (Q m (RecordedQueueRun.scoreWeight p state) _)
      (potentialLambda p)]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, servedEstimate_first_moment]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S _
    ring
  rw [halgebra] at hquad
  rw [← normalizer_ratio_eq_exp_sum] at hquad
  have hlog := Real.log_le_sub_one_of_pos hratio
  linarith only [hquad, hlog]

/-- The source's coarser one-step bound, with the literal constant `16*m^2`. -/
theorem step_log_normalizer_le_coarse (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hm : 2 ≤ m) (hmK : m < K)
    (hsmall : 4 * (m : ℝ) * p.eta ≤ 1) :
    Real.log (normalizer m (RecordedQueueRun.scoreWeight p (step p state round)) /
        normalizer m (RecordedQueueRun.scoreWeight p state)) ≤
      potentialLambda p * (∑ i, theta m (RecordedQueueRun.scoreWeight p state) i *
        servedEstimate p state round i) + 16 * (m : ℝ) ^ 2 * potentialLambda p ^ 2 := by
  calc
    _ ≤ _ := step_log_normalizer_le p state round hm hmK hsmall
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left
        (servedEstimate_second_moment_le p state round hm hmK)
        (sq_nonneg (potentialLambda p))
      nlinarith only [h]

/-- Disabled or already-overflowed steps have zero actual service. The outgoing
overflow flag is deliberately absent: the first crossing update is retained. -/
theorem servedEstimate_eq_zero (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hstop : round.enabled = false ∨ state.overflow = true)
    (i : Fin K) : servedEstimate p state round i = 0 := by
  rcases hstop with hdisabled | hoverflow
  · simp [servedEstimate, recordService, acceptedRecord, hdisabled]
  · simp [servedEstimate, recordService, acceptedRecord, hoverflow]

theorem step_log_normalizer_eq_zero (p : Parameters) (state : RunState K)
    (round : RoundInput K) (hm : 2 ≤ m) (hmK : m < K)
    (hstop : round.enabled = false ∨ state.overflow = true) :
    Real.log (normalizer m (RecordedQueueRun.scoreWeight p (step p state round)) /
      normalizer m (RecordedQueueRun.scoreWeight p state)) = 0 := by
  have hw : RecordedQueueRun.scoreWeight p (step p state round) =
      RecordedQueueRun.scoreWeight p state := by
    funext i
    rw [step_scoreWeight_eq_mul_exp, servedEstimate_eq_zero p state round hstop,
      mul_zero, Real.exp_zero, mul_one]
  rw [hw, div_self (normalizer_pos _ (by omega) hmK (scoreWeight_pos p state)).ne',
    Real.log_one]

private theorem execute_append (p : Parameters) (xs ys : List (RoundInput K))
    (state : RunState K) : execute p (xs ++ ys) state = execute p ys (execute p xs state) := by
  induction xs generalizing state with
  | nil => rfl
  | cons x xs ih => exact ih (step p state x)

/-- Consecutive constructed prefixes use exactly the accepted machine step. -/
theorem run_take_succ_eq_step (p : Parameters) (rounds : List (RoundInput K))
    (t : ℕ) (ht : t < rounds.length) :
    run p (rounds.take (t + 1)) = step p (run p (rounds.take t)) rounds[t] := by
  rw [← List.take_append_getElem ht]
  unfold run
  rw [execute_append]
  rfl

/-- The sharp one-step comparison at every actually constructed run prefix,
including the prefix which first overflows. No rate/recording/queue premise. -/
theorem run_prefix_log_normalizer_le (p : Parameters) (rounds : List (RoundInput K))
    (t : ℕ) (ht : t < rounds.length) (hm : 2 ≤ m) (hmK : m < K)
    (hsmall : 4 * (m : ℝ) * p.eta ≤ 1) :
    Real.log (normalizer m (RecordedQueueRun.scoreWeight p (run p (rounds.take (t + 1)))) /
        normalizer m (RecordedQueueRun.scoreWeight p (run p (rounds.take t)))) ≤
      potentialLambda p * (∑ i, theta m (RecordedQueueRun.scoreWeight p
        (run p (rounds.take t))) i * servedEstimate p (run p (rounds.take t)) rounds[t] i) +
      potentialLambda p ^ 2 * (∑ S : ProductSet K m,
        Q m (RecordedQueueRun.scoreWeight p (run p (rounds.take t))) S *
          (∑ i ∈ S.1, servedEstimate p (run p (rounds.take t)) rounds[t] i) ^ 2) := by
  rw [run_take_succ_eq_step p rounds t ht]
  exact step_log_normalizer_le p _ _ hm hmK hsmall

theorem run_prefix_log_normalizer_le_coarse (p : Parameters) (rounds : List (RoundInput K))
    (t : ℕ) (ht : t < rounds.length) (hm : 2 ≤ m) (hmK : m < K)
    (hsmall : 4 * (m : ℝ) * p.eta ≤ 1) :
    Real.log (normalizer m (RecordedQueueRun.scoreWeight p (run p (rounds.take (t + 1)))) /
        normalizer m (RecordedQueueRun.scoreWeight p (run p (rounds.take t)))) ≤
      potentialLambda p * (∑ i, theta m (RecordedQueueRun.scoreWeight p
        (run p (rounds.take t))) i * servedEstimate p (run p (rounds.take t)) rounds[t] i) +
      16 * (m : ℝ) ^ 2 * potentialLambda p ^ 2 := by
  rw [run_take_succ_eq_step p rounds t ht]
  exact step_log_normalizer_le_coarse p _ _ hm hmK hsmall

theorem run_prefix_log_normalizer_eq_zero (p : Parameters) (rounds : List (RoundInput K))
    (t : ℕ) (ht : t < rounds.length) (hm : 2 ≤ m) (hmK : m < K)
    (hstop : rounds[t].enabled = false ∨ (run p (rounds.take t)).overflow = true) :
    Real.log (normalizer m (RecordedQueueRun.scoreWeight p (run p (rounds.take (t + 1)))) /
      normalizer m (RecordedQueueRun.scoreWeight p (run p (rounds.take t)))) = 0 := by
  rw [run_take_succ_eq_step p rounds t ht]
  exact step_log_normalizer_eq_zero p _ _ hm hmK hstop

end Bandits.Support.RecordedPotentialStep
