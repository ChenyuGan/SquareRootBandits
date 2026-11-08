/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.QueueReplay
public import Bandits.Support.ScoreWeights
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Bandits.Support.ScoreWeightLogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Weight stability for literal queue replay

This module bounds score increments by unfolding the integrated
`QueueReplay.transition` and inducting over `QueueReplay.replay`. The queue and
score updates are from `sources/zip4/manuscript/04_slow_fast_learner.tex:140-174`;
the episode horizon is from `:96-104`, and the source weight-stability target is
from `:218-240`. Arrival records are unrestricted. Disabled records contribute
no service, while enabled zero-arrival records continue to serve existing
backlog as specified by the integrated transition.

These are internal facts about the already-defined register replay. They do not
define another run semantics or establish equality with a recorded queue run.
-/

public section

namespace Bandits.Support.ReplayWeightStability

/-- The manuscript's weight base for a natural denominator `D`. -/
@[expose] noncomputable def sourceBase (D : ℕ) : ℝ := 1 + 1 / (D : ℝ)

/-- The manuscript's episode length `floor (1 / (64 * eta))`. -/
@[expose] noncomputable def episodeHorizon (eta : ℝ) : ℕ := Nat.floor (1 / (64 * eta))

/-- Positivity of the real denominator used in the source weight base. -/
theorem source_denominator_pos {D : ℕ} (hD : 0 < D) : 0 < (D : ℝ) := by
  exact Nat.cast_pos.mpr hD

/-- The source weight base is positive for a positive natural denominator. -/
theorem source_base_pos {D : ℕ} (hD : 0 < D) : 0 < sourceBase D := by
  simpa only [sourceBase] using
    Bandits.Support.ScoreWeights.sourceBase_pos (source_denominator_pos hD)

/-- Every source score weight is positive when its denominator is positive. -/
theorem source_weight_pos {D score : ℕ} (hD : 0 < D) :
    0 < Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score := by
  exact Bandits.Support.ScoreWeights.scoreWeight_pos (source_base_pos hD) score

/-- One literal queue transition increases score by a value between zero and
the service capacity. In the enabled branch the service is exactly the
integrated `min capacity (backlog + arrival)`, including when `arrival = 0`. -/
theorem transition_score_envelope (capacity score backlog : ℕ)
    (record : Bool × ℕ) :
    score ≤ (Bandits.Support.QueueReplay.transition capacity (score, backlog) record).1 ∧
      (Bandits.Support.QueueReplay.transition capacity (score, backlog) record).1 ≤
        score + capacity := by
  cases record with
  | mk enabled arrival =>
    cases enabled with
    | false =>
        change score ≤ score ∧ score ≤ score + capacity
        exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
    | true =>
        change score ≤ score + min capacity (backlog + arrival) ∧
          score + min capacity (backlog + arrival) ≤ score + capacity
        exact ⟨Nat.le_add_right _ _,
          Nat.add_le_add_left (Nat.min_le_left capacity (backlog + arrival)) score⟩

/-- A disabled replay record preserves both registers. -/
theorem transition_disabled_preserves_registers (capacity score backlog arrival : ℕ) :
    Bandits.Support.QueueReplay.transition capacity (score, backlog) (false, arrival) =
      (score, backlog) := rfl

/-- An enabled zero-arrival record still serves the existing backlog. -/
theorem transition_enabled_zero_arrival_serves_backlog
    (capacity score backlog : ℕ) :
    Bandits.Support.QueueReplay.transition capacity (score, backlog) (true, 0) =
      (score + min capacity backlog, backlog - min capacity backlog) :=
  Bandits.Support.QueueReplay.transition_enabled_zero_arrival capacity score backlog

/-- The score envelope for every finite chronological list, proved by induction
on the fold that defines `QueueReplay.replay`. -/
theorem replay_score_envelope (capacity score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    score ≤ (Bandits.Support.QueueReplay.replay capacity (score, backlog) records).1 ∧
      (Bandits.Support.QueueReplay.replay capacity (score, backlog) records).1 ≤
        score + capacity * records.length := by
  induction records generalizing score backlog with
  | nil =>
      simp [Bandits.Support.QueueReplay.replay]
  | cons record records ih =>
      have hstep := transition_score_envelope capacity score backlog record
      have htail :=
        ih (Bandits.Support.QueueReplay.transition capacity (score, backlog) record).1
          (Bandits.Support.QueueReplay.transition capacity (score, backlog) record).2
      change
        score ≤ (Bandits.Support.QueueReplay.replay capacity
          (Bandits.Support.QueueReplay.transition capacity (score, backlog) record)
          records).1 ∧
        (Bandits.Support.QueueReplay.replay capacity
          (Bandits.Support.QueueReplay.transition capacity (score, backlog) record)
          records).1 ≤ score + capacity * (records.length + 1)
      constructor
      · exact hstep.1.trans htail.1
      · calc
          (Bandits.Support.QueueReplay.replay capacity
            (Bandits.Support.QueueReplay.transition capacity (score, backlog) record)
            records).1 ≤
              (Bandits.Support.QueueReplay.transition capacity (score, backlog) record).1 +
                capacity * records.length := htail.2
          _ ≤ (score + capacity) + capacity * records.length :=
                Nat.add_le_add_right hstep.2 (capacity * records.length)
          _ = score + capacity * (records.length + 1) := by
                rw [Nat.mul_succ]
                ac_rfl

/-- Every chronological prefix has the same score envelope, and replay of the
whole list factors through the register state at that prefix. -/
theorem replay_prefix_score_envelope (capacity score backlog : ℕ)
    (records pre suffix : List (Bool × ℕ))
    (hdecomp : records = pre ++ suffix) :
    score ≤ (Bandits.Support.QueueReplay.replay capacity (score, backlog) pre).1 ∧
      (Bandits.Support.QueueReplay.replay capacity (score, backlog) pre).1 ≤
        score + capacity * pre.length ∧
      Bandits.Support.QueueReplay.replay capacity (score, backlog) records =
        Bandits.Support.QueueReplay.replay capacity
          (Bandits.Support.QueueReplay.replay capacity (score, backlog) pre) suffix := by
  have hpre := replay_score_envelope capacity score backlog pre
  refine ⟨hpre.1, hpre.2, ?_⟩
  rw [hdecomp, Bandits.Support.QueueReplay.replay_append]

/-- The score envelope for an episode whose literal replay capacity is `4*n`.
No positivity assumption on `n` is needed for this internal bound. -/
theorem replay_episode_score_envelope (n score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    score ≤ (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 ∧
      (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 ≤
        score + 4 * n * records.length :=
  replay_score_envelope (4 * n) score backlog records

/-- Every prefix of a `4*n`-capacity episode obeys the same score envelope. -/
theorem replay_episode_prefix_score_envelope (n score backlog : ℕ)
    (records pre suffix : List (Bool × ℕ))
    (hdecomp : records = pre ++ suffix) :
    score ≤ (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) pre).1 ∧
      (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) pre).1 ≤
        score + 4 * n * pre.length ∧
      Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records =
        Bandits.Support.QueueReplay.replay (4 * n)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) pre) suffix :=
  replay_prefix_score_envelope (4 * n) score backlog records pre suffix hdecomp

/-- The episode horizon is at most its unrounded real value. -/
theorem episodeHorizon_cast_le {eta : ℝ} (heta : 0 < eta) :
    (episodeHorizon eta : ℝ) ≤ 1 / (64 * eta) := by
  unfold episodeHorizon
  exact Nat.floor_le (by positivity)

/-- The episode-length condition gives the exact source threshold `1/16`. -/
theorem four_eta_mul_length_le_one_sixteenth {eta : ℝ}
    (heta : 0 < eta) (records : List (Bool × ℕ))
    (hlen : records.length ≤ episodeHorizon eta) :
    4 * eta * (records.length : ℝ) ≤ 1 / 16 := by
  have hlenReal : (records.length : ℝ) ≤ (episodeHorizon eta : ℝ) :=
    Nat.cast_le.mpr hlen
  calc
    4 * eta * (records.length : ℝ) = (4 * eta) * (records.length : ℝ) := by ring
    _ ≤ (4 * eta) * (episodeHorizon eta : ℝ) :=
      mul_le_mul_of_nonneg_left hlenReal (by positivity)
    _ ≤ (4 * eta) * (1 / (64 * eta)) :=
      mul_le_mul_of_nonneg_left (episodeHorizon_cast_le heta) (by positivity)
    _ = 1 / 16 := by
      field_simp [ne_of_gt heta]
      norm_num

/-- A direct Mathlib logarithm bound establishes the episode comparison
`1/16 < log 2`. -/
theorem one_sixteenth_lt_log_two : (1 : ℝ) / 16 < Real.log 2 := by
  have hlog := Real.le_log_one_add_of_nonneg (x := (1 : ℝ)) (by norm_num)
  have hrat : (1 : ℝ) / 16 < 2 * 1 / (1 + 2) := by norm_num
  calc
    (1 : ℝ) / 16 < 2 * 1 / (1 + 2) := hrat
    _ ≤ Real.log (1 + 1) := hlog
    _ = Real.log 2 := by congr 1; norm_num

/-- The exact multiplicative source-weight ratio after replay. The score
addition in the exponent follows from the lower half of the replay envelope. -/
theorem replay_source_weight_ratio {D n score backlog : ℕ}
    (hD : 0 < D) (records : List (Bool × ℕ)) :
    Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
        (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 /
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score =
    sourceBase D ^
      ((Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 - score) := by
  have hscore := replay_score_envelope (4 * n) score backlog records
  have hadd :
      score +
          ((Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 - score) =
        (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 :=
    Nat.add_sub_of_le hscore.1
  have hratio :=
    Bandits.Support.ScoreWeights.sourceWeight_update_ratio
      (D := (D : ℝ)) (source_denominator_pos hD) score
      ((Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 - score)
  simpa only [sourceBase, hadd] using hratio

/-- The assumed denominator relation turns the score-cap contribution divided
by `D` into the source learning-rate contribution. -/
theorem replay_source_scale_identity {D n : ℕ} (hD : 0 < D)
    (eta : ℝ) (h_etaD : eta * (D : ℝ) = (n : ℝ))
    (records : List (Bool × ℕ)) :
    ((4 * n * records.length : ℕ) : ℝ) / (D : ℝ) =
      4 * eta * (records.length : ℝ) := by
  calc
    ((4 * n * records.length : ℕ) : ℝ) / (D : ℝ) =
        (4 : ℝ) * (n : ℝ) * (records.length : ℝ) / (D : ℝ) := by
          simp only [Nat.cast_mul, Nat.cast_ofNat]
    _ = 4 * eta * (records.length : ℝ) := by
          rw [← h_etaD]
          field_simp [ne_of_gt (source_denominator_pos hD)]

/-- The logarithm of the exact source-weight ratio is at most `4 * eta` per
record, using only the actual service-cap envelope and the integrated accepted
base-logarithm bound. -/
theorem replay_source_weight_log_le {D n score backlog : ℕ}
    (hD : 0 < D) (eta : ℝ)
    (h_etaD : eta * (D : ℝ) = (n : ℝ))
    (records : List (Bool × ℕ)) :
    Real.log (
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 /
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score) ≤
      4 * eta * (records.length : ℝ) := by
  let finalScore :=
    (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1
  have hscore := replay_score_envelope (4 * n) score backlog records
  have hdelta : finalScore - score ≤ 4 * n * records.length := by
    dsimp [finalScore]
    rw [Nat.sub_le_iff_le_add']
    exact hscore.2
  have hdeltaReal : ((finalScore - score : ℕ) : ℝ) ≤
      ((4 * n * records.length : ℕ) : ℝ) :=
    Nat.cast_le.mpr hdelta
  have hbase :=
    Bandits.Support.ScoreWeightLogBounds.source_base_log_pow_le
      (source_denominator_pos hD) (finalScore - score)
  have hscale := replay_source_scale_identity hD eta h_etaD records
  calc
    Real.log (
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) finalScore /
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score) =
        Real.log (sourceBase D ^ (finalScore - score)) := by
          rw [replay_source_weight_ratio hD records]
    _ ≤ ((finalScore - score : ℕ) : ℝ) / (D : ℝ) := by
          simpa only [sourceBase] using hbase
    _ ≤ ((4 * n * records.length : ℕ) : ℝ) / (D : ℝ) :=
          div_le_div_of_nonneg_right hdeltaReal (source_denominator_pos hD).le
    _ = 4 * eta * (records.length : ℝ) := hscale

/-- Within the literal episode horizon, the source-weight ratio has logarithm
at most `1/16`. -/
theorem replay_source_weight_log_le_one_sixteenth {D n score backlog : ℕ}
    (hD : 0 < D) (eta : ℝ) (heta : 0 < eta)
    (h_etaD : eta * (D : ℝ) = (n : ℝ))
    (records : List (Bool × ℕ))
    (hlen : records.length ≤ episodeHorizon eta) :
    Real.log (
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 /
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score) ≤
      (1 : ℝ) / 16 := by
  exact (replay_source_weight_log_le hD eta h_etaD records).trans
    (four_eta_mul_length_le_one_sixteenth heta records hlen)

/-- Source weights are nondecreasing over replay and grow by at most a factor
of two during one episode of length at most `floor (1 / (64 * eta))`. -/
theorem replay_source_weight_envelope {D n score backlog : ℕ}
    (hD : 0 < D) (eta : ℝ) (heta : 0 < eta)
    (h_etaD : eta * (D : ℝ) = (n : ℝ))
    (records : List (Bool × ℕ))
    (hlen : records.length ≤ episodeHorizon eta) :
    Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score ≤
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 ∧
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 ≤
        2 * Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score := by
  have hscore := replay_score_envelope (4 * n) score backlog records
  have hinitialPos := source_weight_pos (D := D) (score := score) hD
  have hfinalPos := source_weight_pos (D := D)
    (score := (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1) hD
  have hnondecreasing :=
    Bandits.Support.ScoreWeights.sourceWeight_mono (source_denominator_pos hD) hscore.1
  have hlog := replay_source_weight_log_le_one_sixteenth
    (D := D) (n := n) (score := score) (backlog := backlog)
    hD eta heta h_etaD records hlen
  have hratioPos : 0 <
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 /
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score :=
    div_pos hfinalPos hinitialPos
  have hlogTwo :
      Real.log (
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
            (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 /
          Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score) ≤ Real.log 2 :=
    hlog.trans one_sixteenth_lt_log_two.le
  have hratioLe :
      Bandits.Support.ScoreWeights.scoreWeight (sourceBase D)
          (Bandits.Support.QueueReplay.replay (4 * n) (score, backlog) records).1 /
        Bandits.Support.ScoreWeights.scoreWeight (sourceBase D) score ≤ 2 :=
    (Real.log_le_log_iff hratioPos (by norm_num)).mp hlogTwo
  have hupper := (div_le_iff₀ hinitialPos).mp hratioLe
  exact ⟨by simpa only [sourceBase] using hnondecreasing, hupper⟩

end Bandits.Support.ReplayWeightStability

end
