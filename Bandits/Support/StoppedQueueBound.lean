/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedQueueRun

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Deterministic stopped-queue backlog bound

This module proves the pathwise backlog bound for the literal finite machine in
`RecordedQueueRun`, under the explicit internal rate condition
`32 * eta ≤ rate`. It covers the retained first overflowing update and every
later frozen round. The source motivating the rate condition, queue update,
cutoff, and stopped continuation is
`sources/zip4/manuscript/04_slow_fast_learner.tex:96-104,140-174,182-187,245-290`.
It does not derive the protocol's recording law or any probabilistic queue
estimate.
-/

@[expose] public section

namespace Bandits.Support.StoppedQueueBound

open Bandits.Support.RecordedQueueRun

variable {K : ℕ}

/-- The manuscript's backlog normalized by the integer queue scale `n`. -/
noncomputable def normalizedBacklog (p : Parameters) (state : RunState K)
    (i : Fin K) : ℝ :=
  ((state.registers i).2 : ℝ) / (p.n : ℝ)

/-- Under the internal rate condition, the literal natural floor arrival is at
most `D / 32` in the exact integer sense. No bounded-arrival premise is used. -/
theorem quantizedArrival_mul_32_le_D (p : Parameters) (round : RoundInput K)
    (i : Fin K) (hrate : 32 * p.eta ≤ round.rate i) :
    32 * quantizedArrival p round i ≤ p.D := by
  unfold quantizedArrival
  split
  · have hnum : (p.n : ℝ) * round.reward i ≤
        (p.D : ℝ) * p.eta := by
      rw [p.n_eq_eta_mul_D]
      calc
        p.eta * (p.D : ℝ) * round.reward i ≤
            p.eta * (p.D : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (round.reward_le_one i)
            (mul_nonneg p.eta_pos.le (Nat.cast_nonneg p.D))
        _ = (p.D : ℝ) * p.eta := by ring
    have heta : p.eta ≤ round.rate i / 32 := by nlinarith
    have hden : (p.D : ℝ) * p.eta ≤
        (p.D : ℝ) * (round.rate i / 32) :=
      mul_le_mul_of_nonneg_left heta (Nat.cast_nonneg p.D)
    have hratio : (p.n : ℝ) * round.reward i / round.rate i ≤
        (p.D : ℝ) / 32 := by
      apply (div_le_iff₀ (round.rate_pos i)).2
      calc
        (p.n : ℝ) * round.reward i ≤ (p.D : ℝ) * p.eta := hnum
        _ ≤ (p.D : ℝ) * (round.rate i / 32) := hden
        _ = ((p.D : ℝ) / 32) * round.rate i := by ring
    have hnonneg : 0 ≤ (p.n : ℝ) * round.reward i / round.rate i :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg p.n) (round.reward_nonneg i))
        (round.rate_pos i).le
    have hfloor := (Nat.floor_le hnonneg).trans hratio
    have hfloor32 : 32 * (Nat.floor
        ((p.n : ℝ) * round.reward i / round.rate i) : ℝ) ≤ (p.D : ℝ) := by
      nlinarith
    exact_mod_cast hfloor32
  · exact Nat.zero_le _

/-- Every record accepted by a non-frozen enabled step has the same exact
`D / 32` arrival bound; disabled and frozen records accept zero. -/
theorem acceptedRecord_arrival_mul_32_le_D (p : Parameters)
    (state : RunState K) (round : RoundInput K)
    (hrate : ∀ i, 32 * p.eta ≤ round.rate i) (i : Fin K) :
    32 * (acceptedRecord p state round i).2 ≤ p.D := by
  cases hstate : state.overflow <;> cases henabled : round.enabled
  · simp [acceptedRecord, hstate, henabled]
  · simpa [acceptedRecord, hstate, henabled] using
      quantizedArrival_mul_32_le_D p round i (hrate i)
  · simp [acceptedRecord, hstate]
  · simp [acceptedRecord, hstate]

private theorem transition_backlog_le_total (capacity : ℕ)
    (registers : Registers) (record : Bool × ℕ) :
    (QueueReplay.transition capacity registers record).2 ≤
      registers.2 + record.2 := by
  cases record with
  | mk enabled arrival =>
    cases enabled
    · simp [QueueReplay.transition]
    · exact Nat.sub_le _ _

private theorem step_backlog_bound_of_nonoverflow (p : Parameters)
    (state : RunState K) (round : RoundInput K) (i : Fin K)
    (hbefore : 32 * (state.registers i).2 ≤ p.D)
    (harrival : 32 * (acceptedRecord p state round i).2 ≤ p.D) :
    16 * ((step p state round).registers i).2 ≤ p.D := by
  have htransition := transition_backlog_le_total (4 * p.n)
    (state.registers i) (acceptedRecord p state round i)
  change 16 * (QueueReplay.transition (4 * p.n) (state.registers i)
    (acceptedRecord p state round i)).2 ≤ p.D
  omega

/-- The transition preserves the global `16 * backlog ≤ D` invariant. On a
non-overflowing input, the cutoff gives a `D / 32` pre-update bound and the
derived `D / 32` arrival bound proves the retained successor bound. Once the
overflow flag is set, the accepted machine freezes every register. -/
private theorem step_backlog_bound (p : Parameters) (state : RunState K)
    (round : RoundInput K)
    (hbound : ∀ i, 16 * (state.registers i).2 ≤ p.D)
    (hcutoff : state.overflow = true ↔
      ∃ i, 32 * (state.registers i).2 > p.D)
    (hrate : ∀ i, 32 * p.eta ≤ round.rate i) :
    ∀ i, 16 * ((step p state round).registers i).2 ≤ p.D := by
  intro i
  cases hstate : state.overflow
  · have hnotcutoff : ¬ ∃ j, 32 * (state.registers j).2 > p.D := by
      intro h
      have htrue := hcutoff.mpr h
      rw [hstate] at htrue
      contradiction
    have hbefore : 32 * (state.registers i).2 ≤ p.D := by
      by_contra h
      have hgt : p.D < 32 * (state.registers i).2 := by omega
      exact hnotcutoff ⟨i, hgt⟩
    exact step_backlog_bound_of_nonoverflow p state round i hbefore
      (acceptedRecord_arrival_mul_32_le_D p state round hrate i)
  · rw [(step_after_overflow_preserves p state round hstate i).1]
    exact hbound i

/-- Finite execution preserves the cutoff characterization and the global
backlog bound. This induction applies the actual transition on every round,
including disabled rounds and enabled zero-arrival service rounds. -/
private theorem execute_backlog_bound (p : Parameters)
    (rounds : List (RoundInput K)) (state : RunState K)
    (hbound : ∀ i, 16 * (state.registers i).2 ≤ p.D)
    (hcutoff : state.overflow = true ↔
      ∃ i, 32 * (state.registers i).2 > p.D)
    (hrate : ∀ round ∈ rounds, ∀ i, 32 * p.eta ≤ round.rate i) :
    ∀ i, 16 * ((execute p rounds state).registers i).2 ≤ p.D := by
  induction rounds generalizing state with
  | nil =>
    simpa [execute] using hbound
  | cons round rounds ih =>
    have htail : ∀ next ∈ rounds, ∀ i, 32 * p.eta ≤ next.rate i := by
      intro next hnext i
      exact hrate next (by simp [hnext]) i
    have hstepBound := step_backlog_bound p state round hbound hcutoff
      (by intro i; exact hrate round (by simp) i)
    have hstepCutoff := step_overflow_iff_cutoff p state round hcutoff
    simpa [execute] using ih (step p state round) hstepBound hstepCutoff htail

/-- Every actual constructed prefix obeys `16 * backlog ≤ D`, with all rates
in that prefix satisfying the explicit internal lower-rate condition. -/
theorem run_prefix_backlog_bound (p : Parameters)
    (rounds : List (RoundInput K))
    (hrate : ∀ round ∈ rounds, ∀ i, 32 * p.eta ≤ round.rate i)
    (prefixLength : ℕ) (i : Fin K) :
    16 * ((run p (rounds.take prefixLength)).registers i).2 ≤ p.D := by
  have hprefixRate : ∀ round ∈ rounds.take prefixLength, ∀ j,
      32 * p.eta ≤ round.rate j := by
    intro round hround j
    exact hrate round (List.mem_of_mem_take hround) j
  have h := execute_backlog_bound p (rounds.take prefixLength)
    (initialState K) (by intro j; simp [initialState])
    (by simp [initialState]) hprefixRate i
  simpa [run, initialState] using h

/-- The exact real normalization of the integer backlog bound. The identity
uses only `n = eta * D`; it assumes no divisibility property of `D`. -/
theorem run_prefix_normalized_backlog_le_twice_threshold (p : Parameters)
    (rounds : List (RoundInput K))
    (hrate : ∀ round ∈ rounds, ∀ i, 32 * p.eta ≤ round.rate i)
    (prefixLength : ℕ) (i : Fin K) :
    normalizedBacklog p (run p (rounds.take prefixLength)) i ≤
      2 * (1 / (32 * p.eta)) := by
  have hbound := run_prefix_backlog_bound p rounds hrate prefixLength i
  have hreal : 16 *
      (((run p (rounds.take prefixLength)).registers i).2 : ℝ) ≤ (p.D : ℝ) :=
    by exact_mod_cast hbound
  have hscaled :
      (((run p (rounds.take prefixLength)).registers i).2 : ℝ) ≤
        (p.D : ℝ) / 16 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    nlinarith
  have hn : 0 < (p.n : ℝ) := Nat.cast_pos.mpr p.n_pos
  calc
    normalizedBacklog p (run p (rounds.take prefixLength)) i =
        (((run p (rounds.take prefixLength)).registers i).2 : ℝ) /
          (p.n : ℝ) := rfl
    _ ≤ ((p.D : ℝ) / 16) / (p.n : ℝ) :=
      div_le_div_of_nonneg_right hscaled hn.le
    _ = 2 * (1 / (32 * p.eta)) := by
      rw [p.n_eq_eta_mul_D]
      field_simp [ne_of_gt p.eta_pos,
        ne_of_gt (Nat.cast_pos.mpr p.D_pos)]
      ring

/-- The exact source cutoff is equivalent to the integer strict cutoff for
every state register. -/
theorem normalized_backlog_gt_iff_cutoff (p : Parameters)
    (state : RunState K) (i : Fin K) :
    normalizedBacklog p state i > 1 / (32 * p.eta) ↔
      32 * (state.registers i).2 > p.D := by
  simpa [normalizedBacklog] using
    overflowCutoff_iff p (state.registers i).2

/-- Any reachable prefix whose overflow flag is still false satisfies the
stronger pre-update source bound `backlog / n ≤ 1 / (32 eta)`. -/
theorem run_prefix_normalized_backlog_le_threshold_of_overflow_false
    (p : Parameters) (rounds : List (RoundInput K)) (prefixLength : ℕ)
    (i : Fin K)
    (hfalse : (run p (rounds.take prefixLength)).overflow = false) :
    normalizedBacklog p (run p (rounds.take prefixLength)) i ≤
      1 / (32 * p.eta) := by
  apply le_of_not_gt
  intro hgt
  have hcutoff := (normalized_backlog_gt_iff_cutoff p
    (run p (rounds.take prefixLength)) i).mp hgt
  have hoverflow := (run_overflow_iff_cutoff p
    (rounds.take prefixLength)).2 ⟨i, hcutoff⟩
  rw [hfalse] at hoverflow
  contradiction

private theorem execute_append (p : Parameters) (first second : List (RoundInput K))
    (state : RunState K) :
    execute p (first ++ second) state =
      execute p second (execute p first state) := by
  induction first generalizing state with
  | nil => simp [execute]
  | cons round first ih =>
    simp only [List.cons_append, execute]
    exact ih (step p state round)

private theorem execute_overflow_of_prefix (p : Parameters)
    (rounds : List (RoundInput K)) (state : RunState K)
    (prefixLength : ℕ)
    (hprefix : (execute p (rounds.take prefixLength) state).overflow = true) :
    (execute p rounds state).overflow = true := by
  rw [← List.take_append_drop prefixLength rounds, execute_append]
  exact (execute_after_overflow_preserves p (rounds.drop prefixLength)
    (execute p (rounds.take prefixLength) state) hprefix).1

private theorem execute_overflow_reachable (p : Parameters)
    (rounds : List (RoundInput K)) (state : RunState K)
    (hoverflow : (execute p rounds state).overflow = true) :
    state.overflow = true ∨
      ∃ t, t < rounds.length ∧
        (execute p (rounds.take (t + 1)) state).overflow = true := by
  induction rounds generalizing state with
  | nil =>
    simpa [execute] using hoverflow
  | cons round rounds ih =>
    have htail : (execute p rounds (step p state round)).overflow = true := by
      simpa only [execute] using hoverflow
    rcases ih (step p state round) htail with hstep | ⟨t, ht, hprefix⟩
    · right
      refine ⟨0, by simp, ?_⟩
      simpa [execute] using hstep
    · right
      refine ⟨t + 1, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      have htake : (round :: rounds).take ((t + 1) + 1) =
          round :: rounds.take (t + 1) := by
        simp only [List.take_succ_cons]
      rw [htake]
      simpa only [execute] using hprefix

/-- The final overflow flag is equivalent to an overflow at a genuinely
processed prefix successor. The forward direction is reachability from the
initial state; the reverse direction uses the machine's post-overflow
preservation on the actual remaining suffix. -/
theorem run_overflow_iff_exists_prefix_overflow (p : Parameters)
    (rounds : List (RoundInput K)) :
    (run p rounds).overflow = true ↔
      ∃ t, t < rounds.length ∧
        (run p (rounds.take (t + 1))).overflow = true := by
  constructor
  · intro h
    have hreach := execute_overflow_reachable p rounds (initialState K) (by
      simpa [run, initialState] using h)
    rcases hreach with hinit | hprefix
    · simp [initialState] at hinit
    · rcases hprefix with ⟨t, ht, hprefix⟩
      exact ⟨t, ht, by simpa [run, initialState] using hprefix⟩
  · rintro ⟨t, ht, hprefix⟩
    have hprefixExec :
        (execute p (rounds.take (t + 1)) (initialState K)).overflow = true := by
      simpa [run, initialState] using hprefix
    have hfull := execute_overflow_of_prefix p rounds (initialState K)
      (t + 1) hprefixExec
    simpa [run, initialState] using hfull

/-- The final stopped event is exactly a strict normalized-backlog crossing at
some processed prefix successor. The integer cutoff is converted with the
accepted run's exact `n = eta * D` cutoff theorem. -/
theorem run_overflow_iff_exists_prefix_threshold (p : Parameters)
    (rounds : List (RoundInput K)) :
    (run p rounds).overflow = true ↔
      ∃ t, t < rounds.length ∧ ∃ i,
        normalizedBacklog p (run p (rounds.take (t + 1))) i >
          1 / (32 * p.eta) := by
  rw [run_overflow_iff_exists_prefix_overflow]
  constructor
  · rintro ⟨t, ht, hprefix⟩
    obtain ⟨i, hi⟩ := (run_overflow_iff_cutoff p
      (rounds.take (t + 1))).1 hprefix
    exact ⟨t, ht, i,
      (normalized_backlog_gt_iff_cutoff p
        (run p (rounds.take (t + 1))) i).2 hi⟩
  · rintro ⟨t, ht, i, hi⟩
    refine ⟨t, ht, ?_⟩
    apply (run_overflow_iff_cutoff p (rounds.take (t + 1))).2
    exact ⟨i, (normalized_backlog_gt_iff_cutoff p
      (run p (rounds.take (t + 1))) i).1 hi⟩

/-- The same terminal stopped event is the exact terminal-arm normalized
threshold event, via the accepted run's integer cutoff characterization. -/
theorem run_overflow_iff_terminal_threshold (p : Parameters)
    (rounds : List (RoundInput K)) :
    (run p rounds).overflow = true ↔
      ∃ i, normalizedBacklog p (run p rounds) i > 1 / (32 * p.eta) := by
  rw [run_overflow_iff_cutoff]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, (normalized_backlog_gt_iff_cutoff p (run p rounds) i).2 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (normalized_backlog_gt_iff_cutoff p (run p rounds) i).1 hi⟩

end Bandits.Support.StoppedQueueBound

end
