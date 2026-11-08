/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedQueueRun
public import Bandits.Support.ReplayWeightStability

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Stability of weights in constructed recorded queue runs

Every call to `RecordedQueueRun.step` emits one queue record for every arm,
including disabled and post-overflow calls.  This module identifies the exact
suffix emitted by `execute`, proves that its registers are replay of that
suffix from the actual incoming registers, and transfers the already checked
replay weight estimates to those constructed executions.  The source-calendar
specialization uses one-based round labels as in
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-104`; the queue semantics
and first retained overflow update are from `:140-174` and `:182-215`, and the
weight target is from `:219-240`.

The round schedule and all `RoundInput` data are explicit.  This module does
not produce the schedule, rates, or recorded arms.
-/

@[expose] public section

namespace Bandits.Support.RecordedEpisodeStability

open Bandits.Support.RecordedQueueRun

variable {K : ℕ}

/-- The chronological records actually emitted while executing these rounds.
The head record is computed by `acceptedRecord` at the actual current state;
the tail is emitted by the recursive execution from the actual next state. -/
noncomputable def emittedRecords (p : Parameters) :
    (rounds : List (RoundInput K)) → RunState K → Fin K → List (Bool × ℕ)
  | [], _state, _i => []
  | round :: rounds, state, i =>
      acceptedRecord p state round i :: emittedRecords p rounds (step p state round) i

/-- The history recorded by `execute` is its incoming history followed by the
suffix computed from its actual successive machine states. -/
theorem execute_records_eq_append_emitted (p : Parameters)
    (rounds : List (RoundInput K)) (state : RunState K) (i : Fin K) :
    (execute p rounds state).records i =
      state.records i ++ emittedRecords p rounds state i := by
  induction rounds generalizing state with
  | nil => simp [execute, emittedRecords]
  | cons round rounds ih =>
      simpa [execute, emittedRecords, step, List.append_assoc] using
        ih (step p state round)

/-- Each processed calendar round contributes exactly one record to each
arm's actually emitted suffix. -/
theorem emittedRecords_length (p : Parameters) (rounds : List (RoundInput K))
    (state : RunState K) (i : Fin K) :
    (emittedRecords p rounds state i).length = rounds.length := by
  induction rounds generalizing state with
  | nil => rfl
  | cons round rounds ih =>
      simp only [emittedRecords, List.length_cons, List.length_cons]
      exact congrArg Nat.succ (ih (step p state round))

/-- The final per-arm history has exactly its incoming length plus one entry
per processed calendar round. -/
theorem execute_records_length (p : Parameters) (rounds : List (RoundInput K))
    (state : RunState K) (i : Fin K) :
    ((execute p rounds state).records i).length =
      (state.records i).length + rounds.length := by
  rw [execute_records_eq_append_emitted]
  simp [emittedRecords_length]

/-- Registers after execution are replay of the exact suffix emitted by those
steps, starting from the actual incoming registers. -/
theorem execute_registers_eq_replay_emitted (p : Parameters)
    (rounds : List (RoundInput K)) (state : RunState K) (i : Fin K) :
    (execute p rounds state).registers i =
      QueueReplay.replay (4 * p.n) (state.registers i)
        (emittedRecords p rounds state i) := by
  induction rounds generalizing state with
  | nil => simp [execute, emittedRecords, QueueReplay.replay]
  | cons round rounds ih =>
      rw [show (execute p (round :: rounds) state).registers i =
        (execute p rounds (step p state round)).registers i by rfl]
      rw [ih (step p state round)]
      change QueueReplay.replay (4 * p.n)
          (QueueReplay.transition (4 * p.n) (state.registers i)
            (acceptedRecord p state round i))
          (emittedRecords p rounds (step p state round) i) =
        QueueReplay.replay (4 * p.n) (state.registers i)
          ([acceptedRecord p state round i] ++ emittedRecords p rounds
            (step p state round) i)
      rw [QueueReplay.replay_append]
      rfl

/-- The integrated whole-run replay projection, expressed through the suffix
actually emitted from the all-zero initial state. -/
theorem run_registers_eq_replay_emitted (p : Parameters)
    (rounds : List (RoundInput K)) (i : Fin K) :
    (run p rounds).registers i =
      QueueReplay.replay (4 * p.n) (0, 0)
        (emittedRecords p rounds (initialState K) i) := by
  have hrecords : (run p rounds).records i =
      emittedRecords p rounds (initialState K) i := by
    simpa [run, initialState] using
      execute_records_eq_append_emitted p rounds (initialState K) i
  calc
    (run p rounds).registers i =
        QueueReplay.replay (4 * p.n) (0, 0) ((run p rounds).records i) :=
      RecordedQueueRun.run_replay_projection p rounds i
    _ = QueueReplay.replay (4 * p.n) (0, 0)
        (emittedRecords p rounds (initialState K) i) := by rw [hrecords]

/-- Executing an appended chronological list means executing its first part,
then its second part from the resulting actual state. -/
theorem execute_append (p : Parameters) (first second : List (RoundInput K))
    (state : RunState K) :
    execute p (first ++ second) state = execute p second (execute p first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons round first ih =>
      simpa only [List.cons_append, execute] using ih (step p state round)

/-- Splitting a finite list at ordered prefix indices gives the intervening
calendar segment, including when either index lies beyond the list length. -/
theorem take_eq_take_append_drop_take (rounds : List (RoundInput K))
    (start finish : ℕ) (hstart : start ≤ finish) :
    rounds.take finish = rounds.take start ++ (rounds.drop start).take (finish - start) := by
  by_cases hlen : start ≤ rounds.length
  · have htakeLength : (rounds.take start).length = start := by
      rw [List.length_take, Nat.min_eq_left hlen]
    calc
      rounds.take finish = (rounds.take start ++ rounds.drop start).take finish := by
        rw [List.take_append_drop]
      _ = rounds.take start ++ (rounds.drop start).take (finish - start) := by
        rw [List.take_append]
        rw [List.take_of_length_le (by rw [htakeLength]; exact hstart), htakeLength]
  · have hlen' : rounds.length ≤ start := Nat.le_of_not_ge hlen
    have htakeStart : rounds.take start = rounds := List.take_of_length_le hlen'
    have htakeFinish : rounds.take finish = rounds :=
      List.take_of_length_le (hlen'.trans hstart)
    have hdrop : rounds.drop start = [] := List.drop_eq_nil_of_le hlen'
    simp [htakeStart, htakeFinish, hdrop]

/-- The actual run through a prefix factors as execution of its actual
intervening suffix from the actual incoming prefix state. -/
theorem run_take_eq_execute_drop (p : Parameters)
    (rounds : List (RoundInput K)) (start finish : ℕ) (hstart : start ≤ finish) :
    run p (rounds.take finish) =
      execute p ((rounds.drop start).take (finish - start))
        (run p (rounds.take start)) := by
  rw [run, take_eq_take_append_drop_take rounds start finish hstart,
    execute_append]
  rfl

/-- The source episode endpoint formula.  Here `tau / H` is natural division,
which is the source's `floor (tau/H)` for the one-based round label `tau`. -/
def sourceEpisodeEnd (T H tau : ℕ) : ℕ :=
  min (T + 1) (H * (tau / H + 1))

/-- The source horizon is positive under the source small-rate bound. -/
theorem episodeHorizon_pos_of_eta_le {p : Parameters}
    (heta : p.eta ≤ 1 / 64) :
    0 < ReplayWeightStability.episodeHorizon p.eta := by
  have hden : 0 < 64 * p.eta := by positivity [p.eta_pos]
  have hprod : 64 * p.eta ≤ 1 := by nlinarith
  have hone : (1 : ℝ) ≤ 1 / (64 * p.eta) :=
    (le_div_iff₀ hden).2 (by simpa using hprod)
  simpa [ReplayWeightStability.episodeHorizon] using
    (Nat.floor_pos.mpr hone)

/-- Bounds for the one-based source episode calendar. -/
theorem sourceEpisodeEnd_bounds (T H tau : ℕ) (hH : 0 < H)
    (htau : 1 ≤ tau) (htauT : tau ≤ T + 1) :
    1 ≤ tau ∧ tau ≤ sourceEpisodeEnd T H tau ∧
      sourceEpisodeEnd T H tau - tau ≤ H := by
  have hdecomp : tau % H + H * (tau / H) = tau := Nat.mod_add_div tau H
  have hrem : tau % H < H := Nat.mod_lt tau hH
  have hgrid : tau ≤ H * (tau / H + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hle : tau ≤ min (T + 1) (H * (tau / H + 1)) :=
    Nat.le_min.mpr ⟨htauT, hgrid⟩
  have hgap : H * (tau / H + 1) - tau ≤ H := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  refine ⟨htau, ?_, ?_⟩
  · simpa [sourceEpisodeEnd] using hle
  · unfold sourceEpisodeEnd
    exact (Nat.sub_le_sub_right (Nat.min_le_right _ _) tau).trans hgap

/-- The actual run through the source episode's last included round is the
execution of `rounds.drop (tau-1).take (g-tau)` from the actual incoming run
at `tau`. -/
theorem source_episode_execution (p : Parameters)
    (rounds : List (RoundInput K)) (tau : ℕ)
    (htau : 1 ≤ tau)
    (hcalendar : tau ≤ sourceEpisodeEnd rounds.length
      (ReplayWeightStability.episodeHorizon p.eta) tau) :
    run p (rounds.take
        (sourceEpisodeEnd rounds.length (ReplayWeightStability.episodeHorizon p.eta) tau - 1)) =
      execute p
        ((rounds.drop (tau - 1)).take
          (sourceEpisodeEnd rounds.length (ReplayWeightStability.episodeHorizon p.eta) tau - tau))
        (run p (rounds.take (tau - 1))) := by
  let g := sourceEpisodeEnd rounds.length
    (ReplayWeightStability.episodeHorizon p.eta) tau
  have hg : tau ≤ g := by simpa [g] using hcalendar
  have hstart : tau - 1 ≤ g - 1 := by omega
  have hfactor := run_take_eq_execute_drop p rounds (tau - 1) (g - 1) hstart
  have hsub : (g - 1) - (tau - 1) = g - tau := by omega
  simpa [g, hsub] using hfactor

/-- The actual run at any one-based source prefix `t` factors through the
actual run entering round `tau` and the chronological segment between them. -/
theorem source_prefix_execution (p : Parameters)
    (rounds : List (RoundInput K)) (tau t : ℕ)
    (htauPos : 1 ≤ tau) (htau : tau ≤ t) :
    run p (rounds.take (t - 1)) =
      execute p ((rounds.drop (tau - 1)).take (t - tau))
        (run p (rounds.take (tau - 1))) := by
  have hstart : tau - 1 ≤ t - 1 := by omega
  have hfactor := run_take_eq_execute_drop p rounds (tau - 1) (t - 1) hstart
  have hsub : (t - 1) - (tau - 1) = t - tau := by omega
  simpa [hsub] using hfactor

/-- A genuinely executed recorded suffix has the source weight envelope and
the per-round source logarithm bound for every arm.  The only length premise
is the actual episode horizon bound; no replay or score estimate is assumed. -/
theorem execute_source_weight_log_le (p : Parameters) (state : RunState K)
    (rounds : List (RoundInput K)) (i : Fin K) :
    Real.log (scoreWeight p (execute p rounds state) i / scoreWeight p state i) ≤
      4 * p.eta * (rounds.length : ℝ) := by
  have hproject := execute_registers_eq_replay_emitted p rounds state i
  have hrecords := emittedRecords_length p rounds state i
  change Real.log (
      ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ))
        ((execute p rounds state).registers i).1 /
        ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ)) (state.registers i).1) ≤ _
  rw [hproject]
  have hReplay := ReplayWeightStability.replay_source_weight_log_le
    (D := p.D) (n := p.n) (score := (state.registers i).1)
    (backlog := (state.registers i).2) p.D_pos p.eta p.n_eq_eta_mul_D.symm
    (emittedRecords p rounds state i)
  simpa [ReplayWeightStability.sourceBase, hrecords] using hReplay

/-- A genuinely executed suffix has nondecreasing weights, a strict factor-two
upper bound, and a log-ratio bound at most `1/16` over an episode. -/
theorem execute_source_weight_envelope (p : Parameters) (state : RunState K)
    (rounds : List (RoundInput K)) (i : Fin K)
    (hlen : rounds.length ≤ ReplayWeightStability.episodeHorizon p.eta) :
    scoreWeight p state i ≤ scoreWeight p (execute p rounds state) i ∧
      scoreWeight p (execute p rounds state) i < 2 * scoreWeight p state i ∧
      Real.log (scoreWeight p (execute p rounds state) i / scoreWeight p state i) ≤
        4 * p.eta * (rounds.length : ℝ) ∧
      4 * p.eta * (rounds.length : ℝ) ≤ 1 / 16 := by
  have hproject := execute_registers_eq_replay_emitted p rounds state i
  have hrecords := emittedRecords_length p rounds state i
  have hlen' : (emittedRecords p rounds state i).length ≤
      ReplayWeightStability.episodeHorizon p.eta := by simpa [hrecords] using hlen
  have hscore := ReplayWeightStability.replay_score_envelope (4 * p.n)
    (state.registers i).1 (state.registers i).2 (emittedRecords p rounds state i)
  have hD : 0 < (p.D : ℝ) := Nat.cast_pos.mpr p.D_pos
  have hbasePos : 0 < 1 + 1 / (p.D : ℝ) :=
    add_pos zero_lt_one (one_div_pos.mpr hD)
  have hstartPos : 0 < scoreWeight p state i := by
    change 0 < ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ)) (state.registers i).1
    exact ScoreWeights.scoreWeight_pos (b := 1 + 1 / (p.D : ℝ)) hbasePos _
  have hfinalPos : 0 < scoreWeight p (execute p rounds state) i := by
    change 0 < ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ))
      ((execute p rounds state).registers i).1
    rw [hproject]
    exact ScoreWeights.scoreWeight_pos (b := 1 + 1 / (p.D : ℝ)) hbasePos _
  have hratioPos : 0 < scoreWeight p (execute p rounds state) i / scoreWeight p state i :=
    div_pos hfinalPos hstartPos
  have hlog := execute_source_weight_log_le p state rounds i
  have hscaleRecords := ReplayWeightStability.four_eta_mul_length_le_one_sixteenth
    p.eta_pos (emittedRecords p rounds state i) hlen'
  have hscale : 4 * p.eta * (rounds.length : ℝ) ≤ 1 / 16 := by
    simpa only [hrecords] using hscaleRecords
  have hlogBound : Real.log (scoreWeight p (execute p rounds state) i /
      scoreWeight p state i) ≤ 1 / 16 := hlog.trans hscale
  have hlogStrict : Real.log (scoreWeight p (execute p rounds state) i /
      scoreWeight p state i) < Real.log 2 :=
    hlogBound.trans_lt ReplayWeightStability.one_sixteenth_lt_log_two
  have hratioStrict : scoreWeight p (execute p rounds state) i /
      scoreWeight p state i < 2 :=
    (Real.log_lt_log_iff hratioPos (by norm_num : (0 : ℝ) < 2)).mp hlogStrict
  have hupper := (div_lt_iff₀ hstartPos).mp hratioStrict
  have hlogActual := execute_source_weight_log_le p state rounds i
  refine ⟨?_, hupper, hlogActual, hscale⟩
  change ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ)) (state.registers i).1 ≤
    ScoreWeights.scoreWeight (1 + 1 / (p.D : ℝ))
      ((execute p rounds state).registers i).1
  rw [hproject]
  exact ScoreWeights.sourceWeight_mono (Nat.cast_pos.mpr p.D_pos) hscore.1

/-- Every single actual machine step obeys the source logarithmic increment
bound, with no enabled, overflow, or arrival case excluded. -/
theorem step_source_weight_log_le (p : Parameters) (state : RunState K)
    (round : RoundInput K) (i : Fin K) :
    Real.log (scoreWeight p (step p state round) i / scoreWeight p state i) ≤
      4 * p.eta := by
  have h := execute_source_weight_log_le p state [round] i
  simpa [execute, List.length_singleton] using h

/-- Exact one-based source episode endpoint and gap bounds for the actual
calendar length `T = rounds.length`. -/
theorem source_calendar_bounds (p : Parameters) (rounds : List (RoundInput K))
    (tau : ℕ) (heta : p.eta ≤ 1 / 64)
    (htau : 1 ≤ tau) (htauT : tau ≤ rounds.length + 1) :
    0 < ReplayWeightStability.episodeHorizon p.eta ∧
      1 ≤ tau ∧ tau ≤ sourceEpisodeEnd rounds.length
        (ReplayWeightStability.episodeHorizon p.eta) tau ∧
      sourceEpisodeEnd rounds.length (ReplayWeightStability.episodeHorizon p.eta) tau - tau ≤
        ReplayWeightStability.episodeHorizon p.eta := by
  have hH := episodeHorizon_pos_of_eta_le heta
  have hbounds := sourceEpisodeEnd_bounds rounds.length
    (ReplayWeightStability.episodeHorizon p.eta) tau hH htau htauT
  exact ⟨hH, hbounds.1, hbounds.2.1, hbounds.2.2⟩

/-- The actual constructed run through the source episode endpoint is exactly
the actual suffix execution from the run at one-based round `tau`. -/
theorem source_calendar_execution (p : Parameters)
    (rounds : List (RoundInput K)) (tau : ℕ)
    (heta : p.eta ≤ 1 / 64) (htau : 1 ≤ tau)
    (htauT : tau ≤ rounds.length + 1) :
    run p (rounds.take
        (sourceEpisodeEnd rounds.length (ReplayWeightStability.episodeHorizon p.eta) tau - 1)) =
      execute p
        ((rounds.drop (tau - 1)).take
          (sourceEpisodeEnd rounds.length (ReplayWeightStability.episodeHorizon p.eta) tau - tau))
        (run p (rounds.take (tau - 1))) := by
  apply source_episode_execution p rounds tau htau
  exact (source_calendar_bounds p rounds tau heta htau htauT).2.2.1

/-- For every one-based round `tau ≤ t ≤ g` in the actual source calendar,
the actual run prefixes have the strict source weight envelope and the exact
logarithmic increment bound over their actual intervening suffix. -/
theorem source_calendar_prefix_weight_envelope (p : Parameters)
    (rounds : List (RoundInput K)) (tau t : ℕ)
    (heta : p.eta ≤ 1 / 64) (htau : 1 ≤ tau)
    (htauT : tau ≤ rounds.length + 1) (ht : tau ≤ t)
    (htg : t ≤ sourceEpisodeEnd rounds.length
      (ReplayWeightStability.episodeHorizon p.eta) tau) (i : Fin K) :
    scoreWeight p (run p (rounds.take (tau - 1))) i ≤
        scoreWeight p (run p (rounds.take (t - 1))) i ∧
      scoreWeight p (run p (rounds.take (t - 1))) i <
        2 * scoreWeight p (run p (rounds.take (tau - 1))) i ∧
      Real.log (scoreWeight p (run p (rounds.take (t - 1))) i /
        scoreWeight p (run p (rounds.take (tau - 1))) i) ≤
      4 * p.eta * ((t - tau : ℕ) : ℝ) ∧
      4 * p.eta * ((t - tau : ℕ) : ℝ) ≤ 1 / 16 := by
  have hcal := source_calendar_bounds p rounds tau heta htau htauT
  have hgT : sourceEpisodeEnd rounds.length
      (ReplayWeightStability.episodeHorizon p.eta) tau ≤ rounds.length + 1 := by
    exact Nat.min_le_left _ _
  have htT : t ≤ rounds.length + 1 := htg.trans hgT
  have hsteps : t - tau ≤ ReplayWeightStability.episodeHorizon p.eta :=
    (Nat.sub_le_sub_right htg tau).trans hcal.2.2.2
  have hdropLength : (rounds.drop (tau - 1)).length = rounds.length - (tau - 1) := by
    simp
  have htakebound : t - tau ≤ (rounds.drop (tau - 1)).length := by
    rw [hdropLength]
    omega
  have hsegmentExact : ((rounds.drop (tau - 1)).take (t - tau)).length = t - tau := by
    rw [List.length_take, Nat.min_eq_left htakebound]
  have hsegmentBound : ((rounds.drop (tau - 1)).take (t - tau)).length ≤
      ReplayWeightStability.episodeHorizon p.eta := by
    rw [hsegmentExact]
    exact hsteps
  have hfactor := source_prefix_execution p rounds tau t htau ht
  have hdropLength : (rounds.drop (tau - 1)).length = rounds.length - (tau - 1) := by
    simp
  have htakebound : t - tau ≤ (rounds.drop (tau - 1)).length := by
    rw [hdropLength]
    omega
  have hsegmentExact : ((rounds.drop (tau - 1)).take (t - tau)).length = t - tau := by
    rw [List.length_take, Nat.min_eq_left htakebound]
  rw [hfactor]
  have hresult := execute_source_weight_envelope p (run p (rounds.take (tau - 1)))
    ((rounds.drop (tau - 1)).take (t - tau)) i hsegmentBound
  rw [hsegmentExact] at hresult
  exact hresult

end Bandits.Support.RecordedEpisodeStability

end
