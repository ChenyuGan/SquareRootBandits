/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.RecordedPotentialStep
public import Bandits.Support.StoppedQueueBound
public import Bandits.Support.ProductSetDistribution
public import Bandits.Support.RecordedQueueRun

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Raw and served queue summation by parts

This module relates the raw accepted arrivals of the deterministic finite
recorded queue to its served estimates. It proves the finite summation-by-parts
identities and the pathwise terminal backlog bound under the explicit internal
rate condition. It does not formalize a recording law or close a manuscript
regret assertion.

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:154-174`,
`:245-290`, and `:428-452`.
-/

public section

open scoped BigOperators

namespace Bandits.Support.RecordedQueueSummation

open Bandits.Support.RecordedQueueRun
open Bandits.Support.ProductSetLaw

variable {K m : ℕ}

/-- The actual canonical product-set inclusion marginal at a finite run
prefix. The time argument is a prefix length; round inputs themselves are only
accessed through bounded `Fin rounds.length` indices in the queue identities. -/
@[expose] noncomputable def runMarginal (p : Parameters) (m : ℕ)
    (rounds : List (RoundInput K)) (prefixLength : ℕ) (i : Fin K) : ℝ :=
  ProductSetLaw.theta m
    (RecordedQueueRun.scoreWeight p (RecordedQueueRun.run p
      (rounds.take prefixLength))) i

/-- The run marginal is the inclusion-event sum under the accepted
product-set distribution. -/
theorem runMarginal_eq_sum_productSet_Q (p : Parameters) (m : ℕ)
    (rounds : List (RoundInput K)) (prefixLength : ℕ) (i : Fin K) :
    runMarginal p m rounds prefixLength i =
      ∑ S : ProductSet K m,
        if i ∈ S.1 then
          ProductSetLaw.Q m
            (RecordedQueueRun.scoreWeight p
              (RecordedQueueRun.run p (rounds.take prefixLength))) S
        else 0 := by
  exact ProductSetDistribution.theta_eq_sum_productSet_Q _ i

/-- Canonical inclusion marginals are positive at every actual run prefix. -/
theorem runMarginal_pos (p : Parameters) (m : ℕ)
    (rounds : List (RoundInput K)) (prefixLength : ℕ) (i : Fin K)
    (hm : 2 ≤ m) (hmK : m < K) : 0 < runMarginal p m rounds prefixLength i := by
  have hm0 : 0 < m := by omega
  have hw : ∀ j, 0 < RecordedQueueRun.scoreWeight p
      (RecordedQueueRun.run p (rounds.take prefixLength)) j := by
    intro j
    exact RecordedPotentialStep.scoreWeight_pos p
      (RecordedQueueRun.run p (rounds.take prefixLength)) j
  unfold runMarginal
  exact ProductSetLaw.theta_pos _ _ hm0 hmK hw

/-- The inclusion marginals sum to the comparator size; this follows from the
product-set law rather than being an assumption on a marginal sequence. -/
theorem runMarginal_sum_eq_m (p : Parameters) (m : ℕ)
    (rounds : List (RoundInput K)) (prefixLength : ℕ)
    (hm : 2 ≤ m) (hmK : m < K) :
    (∑ i : Fin K, runMarginal p m rounds prefixLength i) = (m : ℝ) := by
  have hm0 : 0 < m := by omega
  have hw : ∀ j, 0 < RecordedQueueRun.scoreWeight p
      (RecordedQueueRun.run p (rounds.take prefixLength)) j := by
    intro j
    exact RecordedPotentialStep.scoreWeight_pos p
      (RecordedQueueRun.run p (rounds.take prefixLength)) j
  exact ProductSetLaw.sum_theta_eq_card _ hm0 hmK hw

/-- A scalar telescoping identity used to express finite queue increments. -/
private theorem sum_fin_sub_succ (b : ℕ → ℝ) (n : ℕ) :
    (∑ t : Fin n, (b (t.val + 1) - b t.val)) = b n - b 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

/-- The all-length finite summation-by-parts identity, in successor-backlog
form. This includes the empty prefix. -/
private theorem sum_fin_weighted_increment (theta b : ℕ → ℝ) (n : ℕ) :
    (∑ t : Fin n, theta t.val * (b (t.val + 1) - b t.val)) =
      theta n * b n - theta 0 * b 0 -
        ∑ t : Fin n,
          (theta (t.val + 1) - theta t.val) * b (t.val + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

/-- The two terminal-correction conventions are equal whenever the source
terminal index exists. -/
private theorem terminal_correction_forms_eq (theta b : ℕ → ℝ) (n : ℕ)
    (hn : 0 < n) :
    -theta n * b n +
        ∑ t : Fin n,
          (theta (t.val + 1) - theta t.val) * b (t.val + 1) =
      -theta (n - 1) * b n +
        ∑ t : Fin (n - 1),
          (theta (t.val + 1) - theta t.val) * b (t.val + 1) := by
  cases n with
  | zero => omega
  | succ k =>
    simp only [Nat.succ_sub_one]
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring

/-- The zero-prefix backlog is zero in the actual initialized machine. -/
theorem run_initial_backlog_eq_zero (p : Parameters)
    (rounds : List (RoundInput K)) (i : Fin K) :
    StoppedQueueBound.normalizedBacklog p
      (RecordedQueueRun.run p (rounds.take 0)) i = 0 := by
  have hstate : RecordedQueueRun.run p (rounds.take 0) =
      RecordedQueueRun.initialState K := by
    simp [RecordedQueueRun.run, RecordedQueueRun.execute]
  rw [hstate, StoppedQueueBound.normalizedBacklog,
    RecordedQueueRun.initialState]
  simp

/-- Exact raw-arrival minus served-estimate recurrence at every genuine round
index. The arrival uses the actual accepted record, including enabled and
overflow gating. -/
theorem rawArrival_sub_servedEstimate_eq_backlog_difference (p : Parameters)
    (rounds : List (RoundInput K)) (t : Fin rounds.length) (i : Fin K) :
    (RecordedQueueRun.acceptedArrival
        (RecordedQueueRun.acceptedRecord p
          (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
        (p.n : ℝ) -
      RecordedPotentialStep.servedEstimate p
        (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i =
      StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (t.val + 1))) i -
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take t.val)) i := by
  let state := RecordedQueueRun.run p (rounds.take t.val)
  let round := rounds[t]
  let record := RecordedQueueRun.acceptedRecord p state round i
  have hnext : RecordedQueueRun.run p (rounds.take (t.val + 1)) =
      RecordedQueueRun.step p state round := by
    exact RecordedPotentialStep.run_take_succ_eq_step p rounds t.val t.isLt
  have htotal := RecordedQueueRun.transition_total (4 * p.n)
    (state.registers i) record
  have hscore := RecordedQueueRun.transition_score_eq_add_recordService
    (4 * p.n) (state.registers i) record
  have hpair :
      (QueueReplay.transition (4 * p.n) (state.registers i) record).2 +
          RecordedQueueRun.recordService (4 * p.n) (state.registers i) record =
        (state.registers i).2 + RecordedQueueRun.acceptedArrival record := by
    change (QueueReplay.transition (4 * p.n) (state.registers i) record).1 +
        (QueueReplay.transition (4 * p.n) (state.registers i) record).2 = _ at htotal
    rw [hscore] at htotal
    omega
  have hcast :
      ((QueueReplay.transition (4 * p.n) (state.registers i) record).2 : ℝ) +
          (RecordedQueueRun.recordService (4 * p.n) (state.registers i) record : ℝ) =
        ((state.registers i).2 : ℝ) +
          (RecordedQueueRun.acceptedArrival record : ℝ) := by
    exact_mod_cast hpair
  have hres :
      (RecordedQueueRun.acceptedArrival record : ℝ) -
          (RecordedQueueRun.recordService (4 * p.n) (state.registers i) record : ℝ) =
        ((QueueReplay.transition (4 * p.n) (state.registers i) record).2 : ℝ) -
          ((state.registers i).2 : ℝ) := by
    linarith only [hcast]
  rw [hnext]
  change (RecordedQueueRun.acceptedArrival record : ℝ) / (p.n : ℝ) -
      (RecordedQueueRun.recordService (4 * p.n) (state.registers i) record : ℝ) /
        (p.n : ℝ) =
      ((QueueReplay.transition (4 * p.n) (state.registers i) record).2 : ℝ) /
          (p.n : ℝ) - ((state.registers i).2 : ℝ) / (p.n : ℝ)
  rw [← sub_div, ← sub_div, hres]

private theorem raw_served_identity_all (p : Parameters) (rounds : List (RoundInput K))
    (m : ℕ) (S : ProductSet K m) :
    (∑ t : Fin rounds.length,
      ((∑ i ∈ S.1,
        (RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
          (p.n : ℝ)) -
        ∑ i : Fin K, runMarginal p m rounds t.val i *
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord p
              (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
            (p.n : ℝ)))) =
      (∑ t : Fin rounds.length,
        ((∑ i ∈ S.1,
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) -
        ∑ i : Fin K, runMarginal p m rounds t.val i *
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i)) +
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i) -
      ∑ i : Fin K, runMarginal p m rounds rounds.length i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i +
      ∑ t : Fin rounds.length, ∑ i : Fin K,
        (runMarginal p m rounds (t.val + 1) i -
          runMarginal p m rounds t.val i) *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (t.val + 1))) i := by
  classical
  let n := rounds.length
  let b : ℕ → Fin K → ℝ := fun q i =>
    StoppedQueueBound.normalizedBacklog p
      (RecordedQueueRun.run p (rounds.take q)) i
  let theta : ℕ → Fin K → ℝ := fun q i => runMarginal p m rounds q i
  let raw : Fin n → Fin K → ℝ := fun t i =>
    (RecordedQueueRun.acceptedArrival
      (RecordedQueueRun.acceptedRecord p
        (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
      (p.n : ℝ)
  let served : Fin n → Fin K → ℝ := fun t i =>
    RecordedPotentialStep.servedEstimate p
      (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i
  have hrec (t : Fin n) (i : Fin K) :
      raw t i - served t i = b (t.val + 1) i - b t.val i := by
    simpa [n, b, theta, raw, served] using
      rawArrival_sub_servedEstimate_eq_backlog_difference p rounds t i
  have hbzero (i : Fin K) : b 0 i = 0 := by
    simpa [b] using run_initial_backlog_eq_zero p rounds i
  have hcomp :
      (∑ t : Fin n, ∑ i ∈ S.1, (b (t.val + 1) i - b t.val i)) =
        ∑ i ∈ S.1, b n i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    have h := sum_fin_sub_succ (fun q => b q i) n
    rw [h, hbzero i, sub_zero]
  have hweight :
      (∑ t : Fin n, ∑ i : Fin K,
        theta t.val i * (b (t.val + 1) i - b t.val i)) =
        (∑ i : Fin K, theta n i * b n i) -
          (∑ i : Fin K, theta 0 i * b 0 i) -
        ∑ t : Fin n, ∑ i : Fin K,
          (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i := by
    calc
      _ = ∑ i : Fin K, ∑ t : Fin n,
          theta t.val i * (b (t.val + 1) i - b t.val i) := by
        rw [Finset.sum_comm]
      _ = ∑ i : Fin K,
          (theta n i * b n i - theta 0 i * b 0 i -
            ∑ t : Fin n,
              (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact sum_fin_weighted_increment
          (fun q => theta q i) (fun q => b q i) n
      _ = (∑ i : Fin K,
          (theta n i * b n i - theta 0 i * b 0 i)) -
          ∑ i : Fin K, ∑ t : Fin n,
            (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i := by
        rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hgap :
      (∑ t : Fin n,
        ((∑ i ∈ S.1, raw t i) - ∑ i : Fin K, theta t.val i * raw t i)) -
        (∑ t : Fin n,
          ((∑ i ∈ S.1, served t i) -
            ∑ i : Fin K, theta t.val i * served t i)) =
        (∑ t : Fin n, ∑ i ∈ S.1, (b (t.val + 1) i - b t.val i)) -
          ∑ t : Fin n, ∑ i : Fin K,
            theta t.val i * (b (t.val + 1) i - b t.val i) := by
    have hterm (t : Fin n) :
        ((∑ i ∈ S.1, raw t i) -
            ∑ i : Fin K, theta t.val i * raw t i) -
          ((∑ i ∈ S.1, served t i) -
            ∑ i : Fin K, theta t.val i * served t i) =
        (∑ i ∈ S.1, (b (t.val + 1) i - b t.val i)) -
          ∑ i : Fin K, theta t.val i * (b (t.val + 1) i - b t.val i) := by
      have hset :
          (∑ i ∈ S.1, raw t i) - ∑ i ∈ S.1, served t i =
            ∑ i ∈ S.1, (raw t i - served t i) := by
        rw [← Finset.sum_sub_distrib]
      have htheta :
          (∑ i : Fin K, theta t.val i * raw t i) -
              ∑ i : Fin K, theta t.val i * served t i =
            ∑ i : Fin K, theta t.val i * (raw t i - served t i) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      calc
        _ = ((∑ i ∈ S.1, raw t i) - ∑ i ∈ S.1, served t i) -
            ((∑ i : Fin K, theta t.val i * raw t i) -
              ∑ i : Fin K, theta t.val i * served t i) := by ring
        _ = _ := by rw [hset, htheta]; simp_rw [hrec]
    calc
      _ = ∑ t : Fin n,
          (((∑ i ∈ S.1, raw t i) -
              ∑ i : Fin K, theta t.val i * raw t i) -
            ((∑ i ∈ S.1, served t i) -
              ∑ i : Fin K, theta t.val i * served t i)) := by
        rw [← Finset.sum_sub_distrib]
      _ = ∑ t : Fin n,
          ((∑ i ∈ S.1, (b (t.val + 1) i - b t.val i)) -
            ∑ i : Fin K, theta t.val i * (b (t.val + 1) i - b t.val i)) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact hterm t
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hresult :
      (∑ t : Fin n,
        ((∑ i ∈ S.1, raw t i) - ∑ i : Fin K, theta t.val i * raw t i)) =
        (∑ t : Fin n,
          ((∑ i ∈ S.1, served t i) -
            ∑ i : Fin K, theta t.val i * served t i)) +
          (∑ i ∈ S.1, b n i) -
            ∑ i : Fin K, theta n i * b n i +
          ∑ t : Fin n, ∑ i : Fin K,
            (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i := by
    have hgap' := hgap
    rw [hcomp, hweight] at hgap'
    have hbzero_sum : (∑ i : Fin K, theta 0 i * b 0 i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp [hbzero]
    rw [hbzero_sum] at hgap'
    linarith only [hgap']
  simpa [n, b, theta, raw, served] using hresult

/-- The exact all-length raw-vs-served identity. Round indices are bounded by
`Fin rounds.length`; the terminal marginal is evaluated at the genuine prefix
of length `rounds.length`. -/
theorem run_raw_served_summation_by_parts_all (p : Parameters)
    (rounds : List (RoundInput K)) (_hm : 2 ≤ m) (_hmK : m < K)
    (S : ProductSet K m) :
    (∑ t : Fin rounds.length,
      ((∑ i ∈ S.1,
        (RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
          (p.n : ℝ)) -
        ∑ i : Fin K, runMarginal p m rounds t.val i *
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord p
              (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
            (p.n : ℝ)))) =
      (∑ t : Fin rounds.length,
        ((∑ i ∈ S.1,
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) -
        ∑ i : Fin K, runMarginal p m rounds t.val i *
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i)) +
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i) -
      ∑ i : Fin K, runMarginal p m rounds rounds.length i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i +
      ∑ t : Fin rounds.length, ∑ i : Fin K,
        (runMarginal p m rounds (t.val + 1) i -
          runMarginal p m rounds t.val i) *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (t.val + 1))) i := by
  have h := raw_served_identity_all p rounds m S
  simpa using h

/-- For a nonempty source horizon, the all-length terminal convention agrees
exactly with the manuscript's `theta_(T-1)` and interior correction. -/
theorem run_terminal_correction_forms_agree (p : Parameters)
    (rounds : List (RoundInput K)) (_hm : 2 ≤ m) (_hmK : m < K)
    (hT : 0 < rounds.length) :
    -(∑ i : Fin K, runMarginal p m rounds rounds.length i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i) +
      ∑ t : Fin rounds.length, ∑ i : Fin K,
        (runMarginal p m rounds (t.val + 1) i -
          runMarginal p m rounds t.val i) *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (t.val + 1))) i =
    -(∑ i : Fin K, runMarginal p m rounds (rounds.length - 1) i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i) +
      ∑ t : Fin (rounds.length - 1), ∑ i : Fin K,
        (runMarginal p m rounds (t.val + 1) i -
          runMarginal p m rounds t.val i) *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (t.val + 1))) i := by
  classical
  let b : ℕ → Fin K → ℝ := fun q i =>
    StoppedQueueBound.normalizedBacklog p
      (RecordedQueueRun.run p (rounds.take q)) i
  let theta : ℕ → Fin K → ℝ := fun q i => runMarginal p m rounds q i
  let n := rounds.length
  change -(∑ i : Fin K, theta n i * b n i) +
      ∑ t : Fin n, ∑ i : Fin K,
        (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i =
    -(∑ i : Fin K, theta (n - 1) i * b n i) +
      ∑ t : Fin (n - 1), ∑ i : Fin K,
        (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i
  have hleft :
      -(∑ i : Fin K, theta n i * b n i) +
        ∑ t : Fin n, ∑ i : Fin K,
          (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i =
        ∑ i : Fin K,
          (-theta n i * b n i +
            ∑ t : Fin n,
              (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright :
      -(∑ i : Fin K, theta (n - 1) i * b n i) +
        ∑ t : Fin (n - 1), ∑ i : Fin K,
          (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i =
        ∑ i : Fin K,
          (-theta (n - 1) i * b n i +
            ∑ t : Fin (n - 1),
              (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  calc
    _ = ∑ i : Fin K,
        (-theta n i * b n i +
          ∑ t : Fin n,
            (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i) := hleft
    _ = ∑ i : Fin K,
        (-theta (n - 1) i * b n i +
          ∑ t : Fin (n - 1),
            (theta (t.val + 1) i - theta t.val i) * b (t.val + 1) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h := terminal_correction_forms_eq (fun q => theta q i)
        (fun q => b q i) n hT
      simpa using h
    _ = _ := hright.symm

/-- The source's nonempty-horizon raw-vs-served summation-by-parts identity. -/
theorem run_raw_served_summation_by_parts (p : Parameters)
    (rounds : List (RoundInput K)) (hm : 2 ≤ m) (hmK : m < K)
    (S : ProductSet K m) (hT : 0 < rounds.length) :
    (∑ t : Fin rounds.length,
      ((∑ i ∈ S.1,
        (RecordedQueueRun.acceptedArrival
          (RecordedQueueRun.acceptedRecord p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
          (p.n : ℝ)) -
        ∑ i : Fin K, runMarginal p m rounds t.val i *
          ((RecordedQueueRun.acceptedArrival
            (RecordedQueueRun.acceptedRecord p
              (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) : ℝ) /
            (p.n : ℝ)))) =
      (∑ t : Fin rounds.length,
        ((∑ i ∈ S.1,
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i) -
        ∑ i : Fin K, runMarginal p m rounds t.val i *
          RecordedPotentialStep.servedEstimate p
            (RecordedQueueRun.run p (rounds.take t.val)) rounds[t] i)) +
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i) -
      ∑ i : Fin K, runMarginal p m rounds (rounds.length - 1) i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i +
      ∑ t : Fin (rounds.length - 1), ∑ i : Fin K,
        (runMarginal p m rounds (t.val + 1) i -
          runMarginal p m rounds t.val i) *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (t.val + 1))) i := by
  have h := run_raw_served_summation_by_parts_all p rounds hm hmK S
  have hcorr := run_terminal_correction_forms_agree p rounds hm hmK hT
  linarith only [h, hcorr]

/-- Under the explicit internal rate condition, the manuscript terminal
expression is at most `m/(16 eta)`. The stopped-queue theorem bounds every
prefix, including the retained first overflow update and the frozen tail. -/
theorem run_terminal_backlog_correction_le (p : Parameters)
    (rounds : List (RoundInput K)) (hm : 2 ≤ m) (hmK : m < K)
    (S : ProductSet K m)
    (hrate : ∀ round ∈ rounds, ∀ i, 32 * p.eta ≤ round.rate i)
    (hT : 0 < rounds.length) :
    (∑ i ∈ S.1,
      StoppedQueueBound.normalizedBacklog p
        (RecordedQueueRun.run p (rounds.take rounds.length)) i) -
      ∑ i : Fin K, runMarginal p m rounds (rounds.length - 1) i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i ≤
      (m : ℝ) / (16 * p.eta) := by
  have hback (i : Fin K) :
      StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i ≤
        1 / (16 * p.eta) := by
    have hlast : rounds.length - 1 + 1 = rounds.length := by omega
    calc
      _ = StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take (rounds.length - 1 + 1))) i := by
        rw [hlast]
      _ ≤ 2 * (1 / (32 * p.eta)) :=
        StoppedQueueBound.run_prefix_normalized_backlog_le_twice_threshold
          p rounds hrate (rounds.length - 1 + 1) i
      _ = 1 / (16 * p.eta) := by
        field_simp [ne_of_gt p.eta_pos]
        ring
  have hnonneg (i : Fin K) :
      0 ≤ runMarginal p m rounds (rounds.length - 1) i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i :=
    mul_nonneg (runMarginal_pos p m rounds (rounds.length - 1) i hm hmK).le
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hsum_nonneg :
      0 ≤ ∑ i : Fin K, runMarginal p m rounds (rounds.length - 1) i *
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i :=
    Finset.sum_nonneg fun i _ => hnonneg i
  have hset :
      (∑ i ∈ S.1,
        StoppedQueueBound.normalizedBacklog p
          (RecordedQueueRun.run p (rounds.take rounds.length)) i) ≤
        (m : ℝ) / (16 * p.eta) := by
    calc
      _ ≤ ∑ i ∈ S.1, (1 / (16 * p.eta) : ℝ) :=
        Finset.sum_le_sum fun i hi => hback i
      _ = (m : ℝ) / (16 * p.eta) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [(Finset.mem_powersetCard.mp S.2).2]
        ring
  linarith only [hset, hsum_nonneg]

end Bandits.Support.RecordedQueueSummation

end
