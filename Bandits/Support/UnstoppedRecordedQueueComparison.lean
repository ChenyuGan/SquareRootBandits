/-
Copyright (c) 2026 Bandits Lean preparation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedQueueRun

import Lean.Elab.Tactic.Omega

/-!
# Unstopped and stopped queue prefixes

This file compares the per-arm replay that continues to accept scheduled
records with `RecordedQueueRun`, whose machine stops accepting arrivals after
its first overflow. The crossing index is a finite least prefix length. The
update at that prefix is retained, and later physical records continue to be
represented by the unstopped replay only through that fixed prefix.

The source passages are `sources/zip4/manuscript/06_interruptions.tex:355-361`,
`:391-397`, and `:425-426`. This deterministic module supplies no physical
producer identifying its records with protocol raw arrivals.
-/

@[expose] public section

namespace Bandits.Support.UnstoppedRecordedQueueComparison

open Bandits.Support.RecordedQueueRun

variable {K : ℕ}

/-- The literal record supplied to the unstopped replay for one scheduled
round: disabled rounds preserve backlog, while enabled zero arrivals still
perform service. -/
noncomputable def unstoppedRecord (q : Parameters) (round : RoundInput K)
    (i : Fin K) : Bool × ℕ :=
  if round.enabled then (true, quantizedArrival q round i) else (false, 0)

/-- Unstopped replay of the first `n` scheduled records for arm `i`. -/
noncomputable def unstoppedReplay (q : Parameters) (xs : List (RoundInput K))
    (n : ℕ) (i : Fin K) : Registers :=
  QueueReplay.replay (4 * q.n) (0, 0)
    ((xs.take n).map fun round => unstoppedRecord q round i)

/-- Whether some arm's unstopped backlog crosses the integer overflow cutoff
after the first `n` scheduled records. -/
def replay_crosses_overflow (q : Parameters) (xs : List (RoundInput K))
    (n : ℕ) : Prop :=
  ∃ i, 32 * (unstoppedReplay q xs n i).2 > q.D

/-- The least crossing prefix in `1..xs.length`, or `xs.length + 1` when no
prefix crosses. -/
noncomputable def firstOverflowPrefix (q : Parameters)
    (xs : List (RoundInput K)) : ℕ := by
  classical
  exact if h : ∃ n, 1 ≤ n ∧ n ≤ xs.length ∧ replay_crosses_overflow q xs n then
    Nat.find h else xs.length + 1

/-- The crossing index is positive, including the no-overflow value `L + 1`. -/
theorem first_overflow_prefix_pos (q : Parameters) (xs : List (RoundInput K)) :
    0 < firstOverflowPrefix q xs := by
  classical
  by_cases h : ∃ n, 1 ≤ n ∧ n ≤ xs.length ∧ replay_crosses_overflow q xs n
  · simp only [firstOverflowPrefix, dite_eq_left h]
    exact Nat.lt_of_succ_le (Nat.find_spec h).1
  · simp [firstOverflowPrefix, h]

/-- If the crossing index is within the horizon, its own prefix crosses. -/
theorem replay_crosses_overflow_at_first (q : Parameters)
    (xs : List (RoundInput K))
    (hk : firstOverflowPrefix q xs ≤ xs.length) :
    replay_crosses_overflow q xs (firstOverflowPrefix q xs) := by
  classical
  by_cases h : ∃ n, 1 ≤ n ∧ n ≤ xs.length ∧ replay_crosses_overflow q xs n
  · simp only [firstOverflowPrefix, dite_eq_left h] at hk ⊢
    exact (Nat.find_spec h).2.2
  · simp [firstOverflowPrefix, h] at hk

/-- No in-horizon prefix before the crossing index crosses. -/
theorem not_replay_crosses_overflow_before_first (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) (hnpos : 1 ≤ n)
    (hnle : n ≤ xs.length)
    (hnk : n < firstOverflowPrefix q xs) :
    ¬ replay_crosses_overflow q xs n := by
  classical
  intro hcross
  have hex : ∃ m, 1 ≤ m ∧ m ≤ xs.length ∧ replay_crosses_overflow q xs m :=
    ⟨n, hnpos, hnle, hcross⟩
  have hmin : firstOverflowPrefix q xs ≤ n := by
    simp only [firstOverflowPrefix, dite_eq_left hex]
    exact Nat.find_min' hex ⟨hnpos, hnle, hcross⟩
  omega

/-- The integer replay cutoff is exactly the manuscript's normalized backlog
test `B / n > 1 / (32 eta)`. -/
theorem replay_crosses_overflow_iff_normalized (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) :
    replay_crosses_overflow q xs n ↔
      ∃ i, ((unstoppedReplay q xs n i).2 : ℝ) / (q.n : ℝ) >
        1 / (32 * q.eta) := by
  unfold replay_crosses_overflow
  exact exists_congr fun i => (overflowCutoff_iff q _).symm

/-- Every stopped prefix is the replay of the records emitted by its literal
machine execution. -/
theorem prefix_registers_replay_emitted_records (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) (i : Fin K) :
    (run q (xs.take n)).registers i =
      QueueReplay.replay (4 * q.n) (0, 0)
        ((run q (xs.take n)).records i) :=
  run_replay_projection q (xs.take n) i

private theorem execute_append (q : Parameters) (left right : List (RoundInput K))
    (state : RunState K) :
    execute q (left ++ right) state = execute q right (execute q left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons round left ih =>
    simp only [List.cons_append, execute]
    exact ih (step q state round)

private theorem run_take_succ (q : Parameters) (xs : List (RoundInput K))
    (n : ℕ) (hn : n < xs.length) :
    run q (xs.take (n + 1)) = step q (run q (xs.take n)) xs[n] := by
  rw [← List.take_append_getElem hn, run, execute_append]
  simp [run, execute]

private theorem acceptedRecord_eq_unstoppedRecord (q : Parameters)
    (state : RunState K) (round : RoundInput K) (i : Fin K)
    (hstate : state.overflow = false) :
    acceptedRecord q state round i = unstoppedRecord q round i := by
  simp [acceptedRecord, unstoppedRecord, hstate]

private theorem unstoppedReplay_succ (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) (hn : n < xs.length) (i : Fin K) :
    unstoppedReplay q xs (n + 1) i =
      QueueReplay.transition (4 * q.n) (unstoppedReplay q xs n i)
        (unstoppedRecord q xs[n] i) := by
  unfold unstoppedReplay
  rw [← List.take_append_getElem hn, List.map_append,
    QueueReplay.replay_append]
  rfl

/-- For every prefix through the first crossing (including that prefix), the
stopped machine agrees arm-by-arm with unstopped replay. After it, the stopped
machine remains at exactly the crossing replay state. -/
theorem prefix_state_comparison (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) (hn : n ≤ xs.length) :
    (∀ i, (run q (xs.take n)).registers i =
      unstoppedReplay q xs (min n (firstOverflowPrefix q xs)) i) ∧
      ((run q (xs.take n)).overflow = true ↔ firstOverflowPrefix q xs ≤ n) := by
  let k := firstOverflowPrefix q xs
  have hkpos : 0 < k := first_overflow_prefix_pos q xs
  revert hn
  induction n with
  | zero =>
    intro hn
    constructor
    · intro i
      simp [run, execute, initialState, unstoppedReplay, QueueReplay.replay]
    · have hnot : ¬ firstOverflowPrefix q xs ≤ 0 :=
        Nat.not_le_of_gt (first_overflow_prefix_pos q xs)
      simp [run, execute, initialState, hnot]
  | succ n ih =>
    intro hn
    have hnle : n ≤ xs.length := by omega
    have hprev := ih hnle
    have hstepBound : n < xs.length := by omega
    have hstep : run q (xs.take (n + 1)) =
        step q (run q (xs.take n)) xs[n] :=
      run_take_succ q xs n hstepBound
    by_cases hkn : k ≤ n
    · have hstate : (run q (xs.take n)).overflow = true := hprev.2.mpr hkn
      have hregs : ∀ i,
          (run q (xs.take (n + 1))).registers i =
            unstoppedReplay q xs (min (n + 1) k) i := by
        intro i
        rw [hstep]
        have hpres := step_after_overflow_preserves q
          (run q (xs.take n)) xs[n] hstate i
        calc
          (step q (run q (xs.take n)) xs[n]).registers i =
              (run q (xs.take n)).registers i := hpres.1
          _ = unstoppedReplay q xs k i := by
            simpa [k, Nat.min_eq_right hkn] using hprev.1 i
          _ = unstoppedReplay q xs (min (n + 1) k) i := by
            rw [Nat.min_eq_right (le_trans hkn (Nat.le_succ n))]
      have hcut :
          (∃ i, 32 * ((run q (xs.take (n + 1))).registers i).2 > q.D) ↔
            k ≤ n + 1 := by
        constructor
        · rintro ⟨i, hi⟩
          rw [hregs i] at hi
          by_contra hkn'
          have hnltk' : n + 1 < k := Nat.lt_of_not_ge hkn'
          rw [Nat.min_eq_left (Nat.le_of_lt hnltk')] at hi
          have hnocross := not_replay_crosses_overflow_before_first q xs
            (n + 1) (by omega) hn (by omega)
          exact hnocross ⟨i, hi⟩
        · intro hkn'
          have hkbound : k ≤ xs.length := by omega
          obtain ⟨i, hi⟩ := replay_crosses_overflow_at_first q xs hkbound
          refine ⟨i, ?_⟩
          rw [hregs i, Nat.min_eq_right hkn']
          exact hi
      exact ⟨hregs, (run_overflow_iff_cutoff q (xs.take (n + 1))).trans hcut⟩
    · have hnltk : n < k := Nat.lt_of_not_ge hkn
      have hstate : (run q (xs.take n)).overflow = false := by
        cases hflag : (run q (xs.take n)).overflow with
        | false => rfl
        | true =>
          have hcontr := hprev.2.mp hflag
          omega
      have hmin : min n k = n := Nat.min_eq_left (Nat.le_of_lt hnltk)
      have hmin' : min (n + 1) k = n + 1 := Nat.min_eq_left (by omega)
      have hregs : ∀ i,
          (run q (xs.take (n + 1))).registers i =
            unstoppedReplay q xs (min (n + 1) k) i := by
        intro i
        rw [hstep]
        change QueueReplay.transition (4 * q.n) ((run q (xs.take n)).registers i)
            (acceptedRecord q (run q (xs.take n)) xs[n] i) =
          unstoppedReplay q xs (min (n + 1) k) i
        rw [hprev.1 i, hmin,
          acceptedRecord_eq_unstoppedRecord q (run q (xs.take n)) xs[n] i hstate,
          ← unstoppedReplay_succ q xs n hstepBound i, hmin']
      have hcut :
          (∃ i, 32 * ((run q (xs.take (n + 1))).registers i).2 > q.D) ↔
            k ≤ n + 1 := by
        constructor
        · rintro ⟨i, hi⟩
          rw [hregs i] at hi
          by_contra hkn'
          have hnltk' : n + 1 < k := Nat.lt_of_not_ge hkn'
          rw [Nat.min_eq_left (Nat.le_of_lt hnltk')] at hi
          have hnocross := not_replay_crosses_overflow_before_first q xs
            (n + 1) (by omega) hn (by omega)
          exact hnocross ⟨i, hi⟩
        · intro hkn'
          have hkbound : k ≤ xs.length := by omega
          obtain ⟨i, hi⟩ := replay_crosses_overflow_at_first q xs hkbound
          refine ⟨i, ?_⟩
          rw [hregs i, Nat.min_eq_right hkn']
          exact hi
      exact ⟨hregs, (run_overflow_iff_cutoff q (xs.take (n + 1))).trans hcut⟩

/-- Literal register comparison for every prefix length. -/
theorem prefix_registers_eq_unstopped_replay (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) (hn : n ≤ xs.length) (i : Fin K) :
    (run q (xs.take n)).registers i =
      unstoppedReplay q xs (min n (firstOverflowPrefix q xs)) i :=
  (prefix_state_comparison q xs n hn).1 i

/-- The stopped overflow flag is set exactly at and after the least unstopped
crossing prefix. -/
theorem prefix_overflow_iff_first_overflow_prefix_le (q : Parameters)
    (xs : List (RoundInput K)) (n : ℕ) (hn : n ≤ xs.length) :
    (run q (xs.take n)).overflow = true ↔ firstOverflowPrefix q xs ≤ n :=
  (prefix_state_comparison q xs n hn).2

end Bandits.Support.UnstoppedRecordedQueueComparison
