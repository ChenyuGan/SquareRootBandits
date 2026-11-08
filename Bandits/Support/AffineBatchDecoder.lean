/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AffineChannelLaw
public import Bandits.Support.OrdinaryMessageCodec
public import Bandits.Support.ConstructorDimensions
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Flatten
import Lean.Elab.Tactic.Omega

/-!
# A literal finite positive-only affine equation-batch decoder

Sources: `sources/zip4/manuscript/05_binary_transport.tex:7-43` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:87-157,280-310`.
The decoder enumerates all binary words and returns a word exactly when the
literal equation solution set is a singleton. It processes an explicit input
trace, retaining round indices and samples, and clears every completed batch
even when its solver fails. Rounded rewards and the selected/receiver-enabled
flags are input data; their physical production is outside this module.

No result asserts delivery, acceptance, authenticity, collision freedom, a
relation to the actually sent word, freshness, or a probabilistic tail bound.
The decision-time results count eligible positive inputs, without asserting
that those inputs occur. This is internal deterministic mathematics.
-/

@[expose] public section

namespace Bandits.Support.AffineBatchDecoder

open AffineChannelLaw

/-- Actual ordinary word width, with the constructor's dyadic denominator. -/
abbrev width (p : ConstructorDimensions.Parameters) : ℕ :=
  5 * OrdinaryMessageCodec.fieldWidth p.T (ConstructorDimensions.D p)

/-- Actual ordinary positive-observation quota, not an independent parameter. -/
def quota (p : ConstructorDimensions.Parameters) : ℕ :=
  width p + Nat.clog 2
    (4 * (p.m - 1) * p.T * (ConstructorDimensions.N p) ^ 2)

theorem width_pos (p : ConstructorDimensions.Parameters) : 0 < width p := by
  have hTD := Nat.mul_pos (ConstructorDimensions.T_pos p) (ConstructorDimensions.D_pos p)
  exact Nat.mul_pos (by decide) (Nat.clog_pos (by decide) (by omega))

theorem quota_pos (p : ConstructorDimensions.Parameters) : 0 < quota p :=
  Nat.lt_of_lt_of_le (width_pos p) (Nat.le_add_right _ _)

/-- The retained equation is literally `c · u = 1 + b` in `ZMod 2`. -/
def equation {B : ℕ} (s : Sample B) (u : Word B) : Prop :=
  AffineChannelLaw.dotProduct s.1 u = 1 + s.2

/-- Addition and subtraction of the offset coincide in the binary field. -/
theorem one_sub_bit (b : Bit) : 1 - b = 1 + b := by
  have hneg : -b = b := by
    have h := OrdinaryMessageCodec.encodeBit_decodeBit b
    split at h
    · rw [← h]
      exact ZMod.neg_one_eq_one_iff.mpr (Or.inr rfl)
    · rw [← h, neg_zero]
  rw [sub_eq_add_neg, hneg]

theorem equation_iff_affineHash {B : ℕ} (s : Sample B) (u : Word B) :
    equation s u ↔ affineHash s u = 1 := by
  rw [equation, affineHash, ← eq_sub_iff_add_eq, one_sub_bit]

/-- Every equation in the finite list must hold; repeated equations are retained. -/
def satisfies {B : ℕ} (W : List (Sample B)) (u : Word B) : Prop :=
  ∀ s ∈ W, equation s u

theorem satisfies_iff_hashes {B : ℕ} (W : List (Sample B)) (u : Word B) :
    satisfies W u ↔ ∀ s ∈ W, affineHash s u = 1 := by
  simp only [satisfies, equation_iff_affineHash]

/-- The solution set filters the entire finite word carrier. -/
noncomputable def solutions {B : ℕ} (W : List (Sample B)) : Finset (Word B) := by
  classical
  exact Finset.univ.filter (satisfies W)

theorem mem_solutions {B : ℕ} (W : List (Sample B)) (u : Word B) :
    u ∈ solutions W ↔ satisfies W u := by
  classical
  simp only [solutions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Return the sole enumerated element; empty and ambiguous sets both return `none`. -/
noncomputable def solve {B : ℕ} (W : List (Sample B)) : Option (Word B) :=
  match (solutions W).toList with
  | [u] => some u
  | _ => none

theorem solve_eq_some_iff_singleton {B : ℕ} (W : List (Sample B)) (u : Word B) :
    solve W = some u ↔ solutions W = {u} := by
  classical
  rw [← Finset.toList_eq_singleton_iff]
  unfold solve
  cases h : (solutions W).toList with
  | nil => simp only [reduceCtorEq]
  | cons a tail =>
    cases tail with
    | nil => simp only [Option.some.injEq, List.cons.injEq, and_true]
    | cons b tail => simp only [reduceCtorEq, List.cons.injEq, and_false]

/-- Complete characterization: the returned word solves every equation and is unique. -/
theorem solve_eq_some_iff {B : ℕ} (W : List (Sample B)) (u : Word B) :
    solve W = some u ↔ satisfies W u ∧ ∀ v, satisfies W v → v = u := by
  classical
  rw [solve_eq_some_iff_singleton, Finset.eq_singleton_iff_unique_mem]
  simp only [mem_solutions]

theorem solve_eq_none_iff {B : ℕ} (W : List (Sample B)) :
    solve W = none ↔ ¬ ∃! u, satisfies W u := by
  constructor
  · intro h ⟨u, hu, huniq⟩
    have hs := (solve_eq_some_iff W u).mpr ⟨hu, huniq⟩
    rw [h] at hs
    cases hs
  · intro h
    cases hs : solve W with
    | none => rfl
    | some u =>
      obtain ⟨hu, huniq⟩ := (solve_eq_some_iff W u).mp hs
      exact (h ⟨u, hu, huniq⟩).elim

/-- Exactly the source's two failure cases: inconsistency or distinct solutions. -/
theorem solve_eq_none_iff_empty_or_ambiguous {B : ℕ} (W : List (Sample B)) :
    solve W = none ↔ (∀ u, ¬ satisfies W u) ∨
      ∃ u v, satisfies W u ∧ satisfies W v ∧ u ≠ v := by
  classical
  rw [solve_eq_none_iff]
  constructor
  · intro h
    by_cases hex : ∃ u, satisfies W u
    · obtain ⟨u, hu⟩ := hex
      right
      by_contra hn
      apply h
      refine ⟨u, hu, fun v hv => ?_⟩
      by_contra hne
      exact hn ⟨u, v, hu, hv, Ne.symm hne⟩
    · left
      exact fun u hu => hex ⟨u, hu⟩
  · rintro (h | ⟨u, v, hu, hv, hne⟩) ⟨w, hw, huniq⟩
    · exact h w hw
    · exact hne ((huniq u hu).trans (huniq v hv).symm)

/-- One channel's explicit round inputs. No physical action rule is included. -/
structure RoundInput (B : ℕ) where
  selected : Bool
  receiverEnabled : Bool
  sample : Sample B
  roundedReward : ℝ

/-- Both control flags and a strictly positive rounded observation are required. -/
def eligible {B : ℕ} (r : RoundInput B) : Prop :=
  r.selected = true ∧ r.receiverEnabled = true ∧ 0 < r.roundedReward

/-- A retained equation includes its origin round, even for identical samples. -/
structure Entry (T B : ℕ) where
  time : Fin T
  sample : Sample B
  deriving DecidableEq

/-- The observation trace is indexed by the actual finite horizon. -/
abbrev Trace (p : ConstructorDimensions.Parameters) := Fin p.T → RoundInput (width p)

def entry (p : ConstructorDimensions.Parameters) (tr : Trace p) (t : Fin p.T) :
    Entry p.T (width p) := ⟨t, (tr t).sample⟩

/-- A round contributes either its single stamped equation or the empty list. -/
noncomputable def positiveAt (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (t : Fin p.T) : List (Entry p.T (width p)) := by
  classical
  exact if eligible (tr t) then [entry p tr t] else []

/-- Literal chronological collection of the eligible positives in a round list. -/
noncomputable def positives (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) : List (Entry p.T (width p)) := by
  classical
  exact (rounds.filter (fun t => decide (eligible (tr t)))).map (entry p tr)

theorem positives_nil (p : ConstructorDimensions.Parameters) (tr : Trace p) :
    positives p tr [] = [] := rfl

theorem positives_cons (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (t : Fin p.T) (ts : List (Fin p.T)) :
    positives p tr (t :: ts) = positiveAt p tr t ++ positives p tr ts := by
  classical
  by_cases h : eligible (tr t) <;> simp [positives, positiveAt, h]

theorem mem_positives_iff (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (e : Entry p.T (width p)) :
    e ∈ positives p tr rounds ↔
      e.time ∈ rounds ∧ eligible (tr e.time) ∧ e.sample = (tr e.time).sample := by
  classical
  constructor
  · intro h
    obtain ⟨t, ht, he⟩ := List.mem_map.mp h
    obtain ⟨htmem, htpos⟩ := List.mem_filter.mp ht
    have het : t = e.time := congrArg Entry.time he
    subst t
    exact ⟨htmem, of_decide_eq_true htpos, (congrArg Entry.sample he).symm⟩
  · rintro ⟨ht, hpos, hs⟩
    apply List.mem_map.mpr
    refine ⟨e.time, List.mem_filter.mpr ⟨ht, by simpa only [decide_eq_true_eq]⟩, ?_⟩
    cases e
    simp only [entry, Entry.mk.injEq, true_and] at hs ⊢
    exact hs.symm

/-- Retain completed batches even when the raw solver returns `none`. -/
structure State (T B : ℕ) where
  pending : List (Entry T B)
  completed : List (List (Entry T B))

def initial (p : ConstructorDimensions.Parameters) : State p.T (width p) := ⟨[], []⟩

def collected {T B : ℕ} (s : State T B) : List (Entry T B) :=
  s.completed.flatten ++ s.pending

def samples {T B : ℕ} (batch : List (Entry T B)) : List (Sample B) :=
  batch.map Entry.sample

theorem satisfies_samples_iff {T B : ℕ} (batch : List (Entry T B)) (u : Word B) :
    satisfies (samples batch) u ↔ ∀ e ∈ batch, equation e.sample u := by
  constructor
  · intro h e he
    exact h e.sample (List.mem_map.mpr ⟨e, he, rfl⟩)
  · intro h s hs
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hs
    exact h e he

/-- The raw output associated to a completed batch, independently of parsing. -/
noncomputable def batchOutput {T B : ℕ} (batch : List (Entry T B)) : Option (Word B) :=
  solve (samples batch)

theorem batchOutput_eq_some_iff {T B : ℕ} (batch : List (Entry T B)) (u : Word B) :
    batchOutput batch = some u ↔
      (∀ e ∈ batch, equation e.sample u) ∧
        ∀ v, (∀ e ∈ batch, equation e.sample v) → v = u := by
  simp only [batchOutput, solve_eq_some_iff, satisfies_samples_iff]

/-- The first and last retained round identify the origin and decision round. -/
def batchOrigin {T B : ℕ} (batch : List (Entry T B)) : Option (Fin T) :=
  (batch.map Entry.time).head?

def decisionTime {T B : ℕ} (batch : List (Entry T B)) : Option (Fin T) :=
  (batch.map Entry.time).getLast?

/-- Append only the eligible positive, then test size, then clear on completion.
The solver outcome does not occur in the state-transition condition. -/
noncomputable def step (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) : State p.T (width p) :=
  let appended := s.pending ++ positiveAt p tr t
  if appended.length < quota p then ⟨appended, s.completed⟩
  else ⟨[], s.completed ++ [appended]⟩

/-- The returned raw word: no decision yet, or the completed batch's exact solver output. -/
noncomputable def stepOutput (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) : Option (Word (width p)) :=
  let appended := s.pending ++ positiveAt p tr t
  if appended.length < quota p then none else batchOutput appended

/-- Full literal decoder transition, pairing its new state with its returned raw word. -/
noncomputable def decodeStep (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) :
    State p.T (width p) × Option (Word (width p)) :=
  (step p tr s t, stepOutput p tr s t)

theorem stepOutput_eq_some_iff (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) (u : Word (width p)) :
    stepOutput p tr s t = some u ↔
      quota p ≤ (s.pending ++ positiveAt p tr t).length ∧
        satisfies (samples (s.pending ++ positiveAt p tr t)) u ∧
          ∀ v, satisfies (samples (s.pending ++ positiveAt p tr t)) v → v = u := by
  by_cases h : (s.pending ++ positiveAt p tr t).length < quota p
  · simp only [stepOutput, ite_eq_left h, reduceCtorEq, Nat.not_le_of_lt h, false_and]
  · simp only [stepOutput, ite_eq_right h, batchOutput, solve_eq_some_iff,
      Nat.le_of_not_gt h, true_and]

theorem stepOutput_eq_none_iff (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) :
    stepOutput p tr s t = none ↔
      (s.pending ++ positiveAt p tr t).length < quota p ∨
        ¬ ∃! u, satisfies (samples (s.pending ++ positiveAt p tr t)) u := by
  by_cases h : (s.pending ++ positiveAt p tr t).length < quota p
  · simp only [stepOutput, h, ite_true, true_or]
  · simp only [stepOutput, h, ite_false, batchOutput, solve_eq_none_iff, false_or]

theorem step_ineligible (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) (hk : s.pending.length < quota p)
    (h : ¬ eligible (tr t)) : step p tr s t = s := by
  classical
  cases s
  simp only [step, positiveAt, ite_eq_right h, List.append_nil, ite_eq_left hk]

theorem decodeStep_ineligible (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) (hk : s.pending.length < quota p)
    (h : ¬ eligible (tr t)) : decodeStep p tr s t = (s, none) := by
  classical
  rw [decodeStep, step_ineligible p tr s t hk h]
  simp only [stepOutput, positiveAt, ite_eq_right h, List.append_nil, ite_eq_left hk]

theorem step_zero_reward (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) (hk : s.pending.length < quota p)
    (hy : (tr t).roundedReward = 0) : step p tr s t = s := by
  apply step_ineligible p tr s t hk
  rintro ⟨_, _, hpos⟩
  rw [hy] at hpos
  exact (lt_irrefl 0) hpos

/-- Every quota-reaching positive clears, with no successful-solver premise. -/
theorem step_complete (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) (h : eligible (tr t))
    (hk : s.pending.length + 1 = quota p) :
    step p tr s t = ⟨[], s.completed ++ [s.pending ++ [entry p tr t]]⟩ := by
  classical
  simp only [step, positiveAt, ite_eq_left h, List.length_append, List.length_singleton, hk,
    lt_self_iff_false, ite_false]

/-- A decision returns the exact solver result and clears even on `none`. -/
theorem decodeStep_complete (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T) (h : eligible (tr t))
    (hk : s.pending.length + 1 = quota p) :
    decodeStep p tr s t =
      (⟨[], s.completed ++ [s.pending ++ [entry p tr t]]⟩,
        batchOutput (s.pending ++ [entry p tr t])) := by
  classical
  rw [decodeStep, step_complete p tr s t h hk]
  simp only [stepOutput, positiveAt, ite_eq_left h, List.length_append,
    List.length_singleton, hk, lt_self_iff_false, ite_false]

theorem decisionTime_append (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (pending : List (Entry p.T (width p))) (t : Fin p.T) :
    decisionTime (pending ++ [entry p tr t]) = some t := by
  simp only [decisionTime, List.map_append, List.map_cons, List.map_nil,
    List.getLast?_append_cons, List.getLast?_singleton, entry]

/-- One transition preserves size and exact positive-input provenance. -/
theorem step_spec (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (s : State p.T (width p)) (t : Fin p.T)
    (hk : s.pending.length < quota p)
    (hc : ∀ batch ∈ s.completed, batch.length = quota p) :
    (step p tr s t).pending.length < quota p ∧
    (∀ batch ∈ (step p tr s t).completed, batch.length = quota p) ∧
    collected (step p tr s t) = collected s ++ positiveAt p tr t := by
  classical
  have hlen : (s.pending ++ positiveAt p tr t).length ≤ quota p := by
    by_cases h : eligible (tr t)
    · simp only [positiveAt, ite_eq_left h, List.length_append, List.length_singleton]
      omega
    · simp only [positiveAt, ite_eq_right h, List.append_nil]
      exact hk.le
  by_cases hsmall : (s.pending ++ positiveAt p tr t).length < quota p
  · refine ⟨?_, ?_, ?_⟩
    · simpa only [step, ite_eq_left hsmall] using hsmall
    · simpa only [step, ite_eq_left hsmall] using hc
    · simp only [step, ite_eq_left hsmall, collected, List.append_assoc]
  · have heq : (s.pending ++ positiveAt p tr t).length = quota p := by omega
    refine ⟨?_, ?_, ?_⟩
    · simpa only [step, ite_eq_right hsmall, List.length_nil] using quota_pos p
    · intro batch hb
      simp only [step, ite_eq_right hsmall, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | rfl
      · exact hc batch hb
      · exact heq
    · simp only [step, ite_eq_right hsmall, collected, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]

/-- Chronological fold of the literal transition over the supplied round list. -/
noncomputable def run (p : ConstructorDimensions.Parameters) (tr : Trace p) :
    List (Fin p.T) → State p.T (width p) → State p.T (width p)
  | [], s => s
  | t :: ts, s => run p tr ts (step p tr s t)

theorem run_spec (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (s : State p.T (width p))
    (hk : s.pending.length < quota p)
    (hc : ∀ batch ∈ s.completed, batch.length = quota p) :
    (run p tr rounds s).pending.length < quota p ∧
    (∀ batch ∈ (run p tr rounds s).completed, batch.length = quota p) ∧
    collected (run p tr rounds s) = collected s ++ positives p tr rounds := by
  induction rounds generalizing s with
  | nil => exact ⟨hk, hc, by simp only [run, positives_nil, List.append_nil]⟩
  | cons t ts ih =>
    obtain ⟨hk', hc', heq⟩ := step_spec p tr s t hk hc
    obtain ⟨hk'', hc'', heq'⟩ := ih (step p tr s t) hk' hc'
    exact ⟨hk'', hc'', by
      simpa only [run, heq, positives_cons, List.append_assoc] using heq'⟩

/-- Enumerate precisely the rounds strictly before `n`, in increasing order.
For `n = T` this is the full one-channel run over `Fin T`. -/
def roundPrefix (p : ConstructorDimensions.Parameters) (n : ℕ) : List (Fin p.T) :=
  (List.ofFn (fun t : Fin p.T => t)).filter (fun t => decide (t.val < n))

theorem mem_roundPrefix (p : ConstructorDimensions.Parameters) (n : ℕ) (t : Fin p.T) :
    t ∈ roundPrefix p n ↔ t.val < n := by
  simp only [roundPrefix, List.mem_filter, List.mem_ofFn, exists_eq, true_and,
    decide_eq_true_eq]

theorem roundPrefix_pairwise (p : ConstructorDimensions.Parameters) (n : ℕ) :
    (roundPrefix p n).Pairwise (fun a b => a.val < b.val) := by
  apply List.Pairwise.filter
  exact List.pairwise_ofFn.mpr fun _ _ h => h

theorem roundPrefix_full (p : ConstructorDimensions.Parameters) :
    roundPrefix p p.T = List.ofFn (fun t : Fin p.T => t) := by
  rw [roundPrefix, List.filter_eq_self]
  intro t _
  exact decide_eq_true t.isLt

/-- State after a genuine chronological prefix, initially empty. -/
noncomputable def stateAt (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) : State p.T (width p) := run p tr (roundPrefix p n) (initial p)

theorem stateAt_spec (p : ConstructorDimensions.Parameters) (tr : Trace p) (n : ℕ) :
    (stateAt p tr n).pending.length < quota p ∧
    (∀ batch ∈ (stateAt p tr n).completed, batch.length = quota p) ∧
    collected (stateAt p tr n) = positives p tr (roundPrefix p n) := by
  obtain ⟨hk, hc, heq⟩ := run_spec p tr (roundPrefix p n) (initial p) (quota_pos p)
    (by simp only [initial, List.not_mem_nil, false_implies, implies_true])
  exact ⟨hk, hc, by simpa only [stateAt, initial, collected, List.flatten_nil, List.nil_append]
    using heq⟩

theorem stateAt_zero (p : ConstructorDimensions.Parameters) (tr : Trace p) :
    stateAt p tr 0 = initial p := by
  have hprefix : roundPrefix p 0 = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    have := (mem_roundPrefix p 0 t).mp ht
    omega
  simp only [stateAt, hprefix, run]

/-- Exact retained membership includes the time cutoff, both flags, positivity,
and the actual affine sample from that round. -/
theorem mem_collected_stateAt_iff (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) (e : Entry p.T (width p)) :
    e ∈ collected (stateAt p tr n) ↔ e.time.val < n ∧
      eligible (tr e.time) ∧ e.sample = (tr e.time).sample := by
  rw [(stateAt_spec p tr n).2.2, mem_positives_iff, mem_roundPrefix]

theorem mem_collected_final_iff (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (e : Entry p.T (width p)) :
    e ∈ collected (stateAt p tr p.T) ↔
      eligible (tr e.time) ∧ e.sample = (tr e.time).sample := by
  simp only [mem_collected_stateAt_iff, e.time.isLt, true_and]

/-- The exact collected list is strictly chronological, so no round is duplicated. -/
theorem collected_stateAt_pairwise (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) :
    (collected (stateAt p tr n)).Pairwise (fun a b => a.time.val < b.time.val) := by
  rw [(stateAt_spec p tr n).2.2]
  apply List.pairwise_map.mpr
  exact (roundPrefix_pairwise p n).filter _

theorem completed_batch_provenance (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) (batch : List (Entry p.T (width p)))
    (hb : batch ∈ (stateAt p tr n).completed) :
    batch.length = quota p ∧
      ∀ e ∈ batch, e.time.val < n ∧ eligible (tr e.time) ∧
        e.sample = (tr e.time).sample := by
  refine ⟨(stateAt_spec p tr n).2.1 batch hb, ?_⟩
  intro e he
  apply (mem_collected_stateAt_iff p tr n e).mp
  exact List.mem_append_left _ (List.mem_flatten.mpr ⟨batch, hb, he⟩)

/-- Each completed batch is a contiguous segment of the chronological positive list. -/
theorem completed_batch_infix (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) (batch : List (Entry p.T (width p)))
    (hb : batch ∈ (stateAt p tr n).completed) :
    batch <:+: positives p tr (roundPrefix p n) := by
  rw [← (stateAt_spec p tr n).2.2]
  exact (List.infix_of_mem_flatten hb).trans List.infix_append_left

theorem completed_batch_pairwise (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) (batch : List (Entry p.T (width p)))
    (hb : batch ∈ (stateAt p tr n).completed) :
    batch.Pairwise (fun a b => a.time.val < b.time.val) := by
  exact List.Pairwise.sublist
    ((List.sublist_flatten_of_mem hb).trans (List.sublist_append_left _ _))
    (collected_stateAt_pairwise p tr n)

/-- Completed batches have genuine first and last retained rounds, never defaults. -/
theorem completed_batch_endpoints (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) (batch : List (Entry p.T (width p)))
    (hb : batch ∈ (stateAt p tr n).completed) :
    ∃ first last : Entry p.T (width p), first ∈ batch ∧ last ∈ batch ∧
      batchOrigin batch = some first.time ∧ decisionTime batch = some last.time := by
  have hne : batch ≠ [] := by
    have hlen := (stateAt_spec p tr n).2.1 batch hb
    intro hnil
    rw [hnil, List.length_nil] at hlen
    have := quota_pos p
    omega
  refine ⟨batch.head hne, batch.getLast hne, List.head_mem hne, List.getLast_mem hne, ?_, ?_⟩
  · simp only [batchOrigin, List.head?_map, List.head?_eq_some_head hne, Option.map_some]
  · simp only [decisionTime, List.getLast?_map, List.getLast?_eq_some_getLast hne,
      Option.map_some]

theorem zero_reward_not_collected (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (n : ℕ) (e : Entry p.T (width p)) (hy : (tr e.time).roundedReward = 0) :
    e ∉ collected (stateAt p tr n) := by
  intro he
  have hpos := ((mem_collected_stateAt_iff p tr n e).mp he).2.1.2.2
  rw [hy] at hpos
  exact (lt_irrefl 0) hpos

/-- Uniform completed-batch sizes give the literal conservation identity. -/
theorem length_collected {T B Q : ℕ} (s : State T B)
    (hc : ∀ batch ∈ s.completed, batch.length = Q) :
    (collected s).length = s.completed.length * Q + s.pending.length := by
  have hflat : s.completed.flatten.length = s.completed.length * Q := by
    have aux : ∀ batches : List (List (Entry T B)),
        (∀ batch ∈ batches, batch.length = Q) →
          batches.flatten.length = batches.length * Q := by
      intro batches
      induction batches with
      | nil => simp only [List.flatten_nil, List.length_nil, Nat.zero_mul, implies_true]
      | cons batch batches ih =>
        intro hall
        rw [List.flatten_cons, List.length_append, hall batch (by simp only [List.mem_cons, true_or]),
          ih (fun b hb => hall b (List.mem_cons_of_mem _ hb)), List.length_cons, Nat.add_mul]
        omega
    exact aux s.completed hc
  simp only [collected, List.length_append, hflat]

/-- General supplied partial-batch count, exposing its sole size requirement.
This arithmetic statement does not certify the supplied prefix's physical provenance. -/
theorem run_counts (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (pending : List (Entry p.T (width p)))
    (hk : pending.length < quota p) :
    let out := run p tr rounds ⟨pending, []⟩
    out.pending.length = (pending.length + (positives p tr rounds).length) % quota p ∧
    out.completed.length = (pending.length + (positives p tr rounds).length) / quota p := by
  dsimp only
  obtain ⟨hsmall, hcomp, hcol⟩ := run_spec p tr rounds ⟨pending, []⟩ hk
    (by simp only [List.not_mem_nil, false_implies, implies_true])
  have hlen := congrArg List.length hcol
  rw [length_collected _ hcomp] at hlen
  simp only [collected, List.flatten_nil, List.nil_append, List.length_append] at hlen
  constructor
  · rw [← hlen, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hsmall]
  · rw [← hlen, Nat.mul_comm _ (quota p), Nat.mul_add_div (quota_pos p),
      Nat.div_eq_of_lt hsmall, Nat.add_zero]

/-- Final pending count is the remainder and completed count is the quotient. -/
theorem stateAt_counts (p : ConstructorDimensions.Parameters) (tr : Trace p) (n : ℕ) :
    (stateAt p tr n).pending.length = (positives p tr (roundPrefix p n)).length % quota p ∧
    (stateAt p tr n).completed.length = (positives p tr (roundPrefix p n)).length / quota p := by
  simpa only [stateAt, initial, List.length_nil, Nat.zero_add] using
    run_counts p tr (roundPrefix p n) [] (quota_pos p)

/-- Over the full horizon, the numerator is exactly the total eligible positive inputs. -/
theorem final_counts (p : ConstructorDimensions.Parameters) (tr : Trace p) :
    let total := (positives p tr (List.ofFn (fun t : Fin p.T => t))).length
    (stateAt p tr p.T).pending.length = total % quota p ∧
    (stateAt p tr p.T).completed.length = total / quota p := by
  simpa only [roundPrefix_full] using stateAt_counts p tr p.T

/-- Before `Q-k` additional positives, no decision has occurred. -/
theorem no_decision_before (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (pending : List (Entry p.T (width p)))
    (hk : pending.length < quota p)
    (hn : (positives p tr rounds).length < quota p - pending.length) :
    (run p tr rounds ⟨pending, []⟩).completed.length = 0 := by
  rw [(run_counts p tr rounds pending hk).2]
  exact Nat.div_eq_of_lt (by omega)

/-- The first decision uses exactly `Q-k` additional positives and clears. -/
theorem first_decision (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (pending : List (Entry p.T (width p)))
    (hk : pending.length < quota p)
    (hn : (positives p tr rounds).length = quota p - pending.length) :
    (run p tr rounds ⟨pending, []⟩).completed.length = 1 ∧
    (run p tr rounds ⟨pending, []⟩).pending = [] := by
  have hsum : pending.length + (positives p tr rounds).length = quota p := by omega
  obtain ⟨hrem, hdiv⟩ := run_counts p tr rounds pending hk
  rw [hsum, Nat.mod_self] at hrem
  rw [hsum, Nat.div_self (quota_pos p)] at hdiv
  exact ⟨hdiv, List.length_eq_zero_iff.mp hrem⟩

/-- Between the first and second thresholds there has been exactly one decision. -/
theorem one_decision_between (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (pending : List (Entry p.T (width p)))
    (hk : pending.length < quota p)
    (hlo : quota p - pending.length ≤ (positives p tr rounds).length)
    (hhi : (positives p tr rounds).length < quota p - pending.length + quota p) :
    (run p tr rounds ⟨pending, []⟩).completed.length = 1 := by
  rw [(run_counts p tr rounds pending hk).2, Nat.div_eq_iff (quota_pos p)]
  simp only [Nat.one_mul]
  omega

/-- A further `Q` positives produces the following decision, with no acceptance claim. -/
theorem second_decision (p : ConstructorDimensions.Parameters) (tr : Trace p)
    (rounds : List (Fin p.T)) (pending : List (Entry p.T (width p)))
    (hk : pending.length < quota p)
    (hn : (positives p tr rounds).length = quota p - pending.length + quota p) :
    (run p tr rounds ⟨pending, []⟩).completed.length = 2 ∧
    (run p tr rounds ⟨pending, []⟩).pending = [] := by
  have hsum : pending.length + (positives p tr rounds).length = 2 * quota p := by omega
  obtain ⟨hrem, hdiv⟩ := run_counts p tr rounds pending hk
  rw [hsum, Nat.mul_mod_left] at hrem
  rw [hsum, Nat.mul_div_cancel _ (quota_pos p)] at hdiv
  exact ⟨hdiv, List.length_eq_zero_iff.mp hrem⟩

/-- Codec parameters have the actual constructor dimensions; only `beta` is extra data. -/
noncomputable abbrev codecParams (p : ConstructorDimensions.Parameters) (beta : ℝ) :
    OrdinaryMessageCodec.CodecParams :=
  ⟨p.m, p.K, p.T, ConstructorDimensions.D p, ConstructorDimensions.b_N p, beta,
    ConstructorDimensions.T_pos p, ConstructorDimensions.D_pos p,
    ConstructorDimensions.K_le_D p, ConstructorDimensions.b_N_le_D p⟩

/-- Parse the raw unique solution through the accepted flat-word equivalence. -/
noncomputable def parseBatch (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (dir : OrdinaryMessageCodec.Direction) (W : List (Sample (width p))) :
    Option (OrdinaryMessageCodec.MessageRecord (codecParams p beta) dir) :=
  OrdinaryMessageCodec.parseDir (codecParams p beta) dir
    ((solve W).map (OrdinaryMessageCodec.wordEquivFlat (codecParams p beta)).symm)

/-- Every parsed output re-encodes to exactly the raw solved flat word, and conversely. -/
theorem parseBatch_eq_some_iff (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (dir : OrdinaryMessageCodec.Direction) (W : List (Sample (width p)))
    (x : OrdinaryMessageCodec.MessageRecord (codecParams p beta) dir) :
    parseBatch p beta dir W = some x ↔ solve W = some
      (OrdinaryMessageCodec.wordEquivFlat (codecParams p beta)
        (OrdinaryMessageCodec.encode (codecParams p beta) dir x)) := by
  constructor
  · intro h
    have hs := OrdinaryMessageCodec.parseDir_some_sound (codecParams p beta) dir _ x h
    cases hraw : solve W with
    | none => simp only [hraw, Option.map_none, reduceCtorEq] at hs
    | some u =>
      simp only [hraw, Option.map_some, Option.some.injEq] at hs
      congr 1
      exact ((OrdinaryMessageCodec.wordEquivFlat (codecParams p beta)).apply_symm_apply u).symm.trans
        (congrArg (OrdinaryMessageCodec.wordEquivFlat (codecParams p beta)) hs)
  · intro h
    simp only [parseBatch, h, Option.map_some, Equiv.symm_apply_apply,
      OrdinaryMessageCodec.parseDir_encode]

/-- Parsing success certifies the exact unique equation solution, without authenticity. -/
theorem parseBatch_eq_some_iff_unique (p : ConstructorDimensions.Parameters) (beta : ℝ)
    (dir : OrdinaryMessageCodec.Direction) (W : List (Sample (width p)))
    (x : OrdinaryMessageCodec.MessageRecord (codecParams p beta) dir) :
    parseBatch p beta dir W = some x ↔
      let u := OrdinaryMessageCodec.wordEquivFlat (codecParams p beta)
        (OrdinaryMessageCodec.encode (codecParams p beta) dir x)
      satisfies W u ∧ ∀ v, satisfies W v → v = u := by
  rw [parseBatch_eq_some_iff, solve_eq_some_iff]

end Bandits.Support.AffineBatchDecoder

end
