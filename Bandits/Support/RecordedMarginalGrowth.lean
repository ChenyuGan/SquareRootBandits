/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ProductSetLaw
public import Bandits.Support.RecordedQueueRun
public import Mathlib.Analysis.Complex.Exponential

import Bandits.Support.ProductMarginalStability
import Bandits.Support.RecordedEpisodeStability
import Bandits.Support.RecordedPotentialStep
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Inclusion marginal growth on the actual recorded queue run

For each actual accepted `RecordedQueueRun.step`, the emitted-record/replay
log cap bounds score-weight growth. The product-set marginal then grows by at
most the same coordinate factor, using the own-coordinate update and
other-coordinate antitonicity argument.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-89`
(coordinate marginal comparison), `:140-174` (accepted queue step and score
update), `:182-187` (retention of the first overflow update), and `:292-318`
(the one-step inclusion-marginal growth bound). These are fully proved internal
inequalities; they do not establish recording moments, expected drift, or
closure of a manuscript lemma.
-/

public section

open scoped BigOperators

namespace Bandits.Support.RecordedMarginalGrowth

open Bandits.Support.ProductSetLaw
open Bandits.Support.RecordedQueueRun

variable {K m : ℕ}

/-- On `[0,1]`, the exponential is bounded by the chord estimate
`exp x ≤ 1 + 2x`. The interval premises are explicit. -/
theorem exp_le_one_add_two_mul_of_mem_unit_interval (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + 2 * x := by
  have hx2 : x < 2 := by linarith
  have hden : 0 < 2 - x := by linarith
  have hprod : 0 ≤ x * (1 - x) := mul_nonneg hx0 (by linarith)
  have hrat : 2 + x ≤ (1 + 2 * x) * (2 - x) := by nlinarith
  calc
    Real.exp x ≤ (2 + x) / (2 - x) :=
      Real.exp_le_two_add_div_two_sub hx0 hx2
    _ ≤ 1 + 2 * x := (div_le_iff₀ hden).2 hrat

/-- The own-coordinate update and other-coordinate antitonicity argument for
an arbitrary common factor `c ≥ 1`. -/
theorem theta_le_factor_of_coordinatewise_bounds (v w : Fin K → ℝ)
    (i : Fin K) (factor : ℝ) (hmlo : 2 ≤ m) (hmhi : m < K)
    (hvpos : ∀ j, 0 < v j) (hwpos : ∀ j, 0 < w j)
    (_hfactor : 1 ≤ factor)
    (hbounds : ∀ j, v j ≤ w j ∧ w j ≤ factor * v j) :
    theta m w i ≤ factor * theta m v i := by
  let u : Fin K → ℝ := Function.update w i (v i)
  have hu_pos : ∀ j, 0 < u j := by
    intro j
    by_cases hji : j = i
    · subst j
      simp [u, hvpos i]
    · simp [u, hji, hwpos j]
  have huown : v i = u i := by simp [u]
  have huother : ∀ j, j ≠ i → v j ≤ u j := by
    intro j hji
    simpa [u, hji] using (hbounds j).1
  have hother := ProductMarginalStability.theta_antitone_of_other_coord_le
    v u i hmlo hmhi hvpos hu_pos huown huother
  let c : ℝ := w i / v i
  have hc : 1 ≤ c := by
    dsimp [c]
    rw [le_div_iff₀ (hvpos i)]
    simpa using (hbounds i).1
  have hcfactor : c ≤ factor := by
    dsimp [c]
    exact (div_le_iff₀ (hvpos i)).2 (hbounds i).2
  have hmul : c * v i = w i := by
    dsimp [c]
    field_simp [ne_of_gt (hvpos i)]
  have hupdate : Function.update u i (c * u i) = w := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      rw [show u i = v i by simp [u], hmul]
    · simp [u, hji]
  have hscaled := ProductMarginalStability.theta_update_le u i c
    (Nat.zero_lt_of_lt hmlo) hmhi hu_pos hc
  have hscaled' : theta m w i ≤ c * theta m u i := by
    simpa only [hupdate] using hscaled
  have htheta_nonneg : 0 ≤ theta m v i :=
    (ProductSetLaw.theta_pos v i (Nat.zero_lt_of_lt hmlo) hmhi hvpos).le
  have hc_nonneg : 0 ≤ c := le_trans (by norm_num) hc
  calc
    theta m w i ≤ c * theta m u i := hscaled'
    _ ≤ c * theta m v i := mul_le_mul_of_nonneg_left hother hc_nonneg
    _ ≤ factor * theta m v i := mul_le_mul_of_nonneg_right hcfactor htheta_nonneg

/-- Actual score weights are strictly positive at every recorded run state. -/
theorem state_scoreWeight_pos (p : Parameters) (state : RunState K) (i : Fin K) :
    0 < scoreWeight p state i :=
  RecordedPotentialStep.scoreWeight_pos p state i

/-- The actual product-set inclusion marginal is positive at every recorded
run state. -/
theorem state_theta_pos (p : Parameters) (state : RunState K) (i : Fin K)
    (hm : 0 < m) (hmK : m < K) :
    0 < theta m (scoreWeight p state) i :=
  ProductSetLaw.theta_pos (scoreWeight p state) i hm hmK
    (fun j => state_scoreWeight_pos p state j)

/-- The sum of actual inclusion marginals is the product-set cardinality. -/
theorem state_sum_theta_eq_m (p : Parameters) (state : RunState K)
    (hm : 0 < m) (hmK : m < K) :
    (∑ i : Fin K, theta m (scoreWeight p state) i) = (m : ℝ) :=
  ProductSetLaw.sum_theta_eq_card (scoreWeight p state) hm hmK
    (fun j => state_scoreWeight_pos p state j)

/-- The score weight of each arm is nondecreasing at the actual accepted
one-step queue update and has the source exponential upper factor. The bounds
come from the emitted-record/replay envelope, including at the first
overflowing update. -/
theorem step_scoreWeight_bounds (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) (heta : p.eta ≤ 1 / 64) :
    scoreWeight p state i ≤ scoreWeight p (step p state round) i ∧
      scoreWeight p (step p state round) i ≤
        Real.exp (4 * p.eta) * scoreWeight p state i := by
  have hHpos := RecordedEpisodeStability.episodeHorizon_pos_of_eta_le
    (p := p) heta
  have hlen : ([round] : List (RoundInput K)).length ≤
      ReplayWeightStability.episodeHorizon p.eta := by
    simp
    omega
  have henv := RecordedEpisodeStability.execute_source_weight_envelope
    p state [round] i hlen
  have hlower : scoreWeight p state i ≤ scoreWeight p (step p state round) i := by
    simpa [execute] using henv.1
  have hlog :
      Real.log (scoreWeight p (step p state round) i / scoreWeight p state i) ≤
        4 * p.eta := by
    simpa [execute] using henv.2.2.1
  have hstartPos : 0 < scoreWeight p state i := state_scoreWeight_pos p state i
  have hnextPos : 0 < scoreWeight p (step p state round) i :=
    state_scoreWeight_pos p (step p state round) i
  have hratioPos : 0 < scoreWeight p (step p state round) i / scoreWeight p state i :=
    div_pos hnextPos hstartPos
  have hratio : scoreWeight p (step p state round) i / scoreWeight p state i ≤
      Real.exp (4 * p.eta) :=
    (Real.log_le_iff_le_exp hratioPos).mp hlog
  exact ⟨hlower, (div_le_iff₀ hstartPos).mp hratio⟩

/-- The source small-rate hypothesis supplies the interval needed for
`exp (4 eta) ≤ 1 + 8 eta`. -/
theorem exp_four_eta_le_one_add_eight_eta (p : Parameters)
    (heta : p.eta ≤ 1 / 64) :
    Real.exp (4 * p.eta) ≤ 1 + 8 * p.eta := by
  have hx0 : 0 ≤ 4 * p.eta := by positivity [p.eta_pos]
  have hx1 : 4 * p.eta ≤ 1 := by nlinarith [heta]
  calc
    Real.exp (4 * p.eta) ≤ 1 + 2 * (4 * p.eta) :=
      exp_le_one_add_two_mul_of_mem_unit_interval (4 * p.eta) hx0 hx1
    _ = 1 + 8 * p.eta := by ring

/-- One actual queue step grows the canonical inclusion marginal by at most
`exp (4 eta)`, and hence by at most the source factor `1 + 8 eta`. The outgoing
overflow flag is not used: the first crossing update satisfies this bound. -/
theorem step_theta_growth (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) (hmlo : 2 ≤ m) (hmhi : m < K)
    (heta : p.eta ≤ 1 / 64) :
    theta m (scoreWeight p (step p state round)) i ≤
        Real.exp (4 * p.eta) * theta m (scoreWeight p state) i ∧
      Real.exp (4 * p.eta) * theta m (scoreWeight p state) i ≤
        (1 + 8 * p.eta) * theta m (scoreWeight p state) i := by
  have hbounds : ∀ j, scoreWeight p state j ≤
      scoreWeight p (step p state round) j ∧
        scoreWeight p (step p state round) j ≤
          Real.exp (4 * p.eta) * scoreWeight p state j := by
    intro j
    exact step_scoreWeight_bounds p state round j heta
  have htheta := theta_le_factor_of_coordinatewise_bounds
    (scoreWeight p state) (scoreWeight p (step p state round)) i
    (Real.exp (4 * p.eta)) hmlo hmhi
    (fun j => state_scoreWeight_pos p state j)
    (fun j => state_scoreWeight_pos p (step p state round) j)
    (Real.one_le_exp_iff.mpr (by positivity [p.eta_pos]))
    hbounds
  have htheta_pos := state_theta_pos p state i (Nat.zero_lt_of_lt hmlo) hmhi
  have hexp := exp_four_eta_le_one_add_eight_eta p heta
  exact ⟨htheta, mul_le_mul_of_nonneg_right hexp (le_of_lt htheta_pos)⟩

/-- Disabled and already-overflowed actual steps preserve every inclusion
marginal exactly. -/
theorem step_theta_eq_of_disabled_or_overflowed (p : Parameters)
    (state : RunState K) (round : RoundInput K) (i : Fin K)
    (hstop : round.enabled = false ∨ state.overflow = true) :
    theta m (scoreWeight p (step p state round)) i =
      theta m (scoreWeight p state) i := by
  have hweight (j : Fin K) :
      scoreWeight p (step p state round) j = scoreWeight p state j := by
    rcases hstop with hdisabled | hoverflow
    · have hreg := (RecordedQueueRun.step_disabled_preserves
        p state round hdisabled j).1
      unfold RecordedQueueRun.scoreWeight
      rw [hreg]
    · have hreg := (RecordedQueueRun.step_after_overflow_preserves
        p state round hoverflow j).1
      unfold RecordedQueueRun.scoreWeight
      rw [hreg]
  exact congrArg (fun w : Fin K → ℝ => theta m w i) (funext hweight)

/-- Consecutive chronological run prefixes obey the actual one-step marginal
growth estimate, via the exact run/step prefix identity. -/
theorem run_prefix_theta_growth (p : Parameters)
    (rounds : List (RoundInput K)) (t : ℕ) (ht : t < rounds.length)
    (i : Fin K) (hmlo : 2 ≤ m) (hmhi : m < K)
    (heta : p.eta ≤ 1 / 64) :
    theta m (scoreWeight p (run p (rounds.take (t + 1)))) i ≤
        Real.exp (4 * p.eta) *
          theta m (scoreWeight p (run p (rounds.take t))) i ∧
      Real.exp (4 * p.eta) *
          theta m (scoreWeight p (run p (rounds.take t))) i ≤
        (1 + 8 * p.eta) * theta m (scoreWeight p (run p (rounds.take t))) i := by
  rw [RecordedPotentialStep.run_take_succ_eq_step p rounds t ht]
  exact step_theta_growth p _ _ i hmlo hmhi heta

/-- Consecutive chronological prefixes have exactly equal marginals when the
input disables learning or the incoming run has already overflowed. -/
theorem run_prefix_theta_eq_of_disabled_or_overflowed (p : Parameters)
    (rounds : List (RoundInput K)) (t : ℕ) (ht : t < rounds.length)
    (i : Fin K)
    (hstop : rounds[t].enabled = false ∨
      (run p (rounds.take t)).overflow = true) :
    theta m (scoreWeight p (run p (rounds.take (t + 1)))) i =
      theta m (scoreWeight p (run p (rounds.take t))) i := by
  rw [RecordedPotentialStep.run_take_succ_eq_step p rounds t ht]
  exact step_theta_eq_of_disabled_or_overflowed p
    (run p (rounds.take t)) rounds[t] i hstop

end Bandits.Support.RecordedMarginalGrowth

end
