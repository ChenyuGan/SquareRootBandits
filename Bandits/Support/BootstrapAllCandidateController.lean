/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapTruePrefixController

/-!
# All-candidate bootstrap prefix controller

This module runs the literal bootstrap decoder against every complete row on
one already constructed physical block. It owns only per-row positive counts,
per-row permanent mismatch flags, and the pending row declaration.

Sources: appendix_b_communication.tex:101-126,134-165 and
07_public_setup.tex:93-109,129-140.

This is a local decoder operation on a supplied physical block. It supplies
neither a false-candidate probability nor a global clean-prefix event.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapAllCandidateController

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.CompletePublicTable
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount

variable {p : Parameters} {s : Fin (n_boot p)}

/-- The common event that makes physical feedback eligible for decoder
processing, before testing a row's own DATA coordinate. -/
def positiveRound (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) : Prop :=
  t ∈ calendarBlock p s ∧ x.active i = true ∧
    x.ids (x.privateId i) t = false ∧
    0 < (BootstrapPhysicalBlock.observationIndex x
      (BootstrapPhysicalBlock.run x t.val) t
      (followerPlayer p.two_le_m i.val)).val

/-- Candidate v's own DATA test, evaluated from its complete row. -/
def rowIsData (rows : CompleteRows p) (v : Fin (M p)) (t : Fin p.T) : Prop :=
  slotDraw ((rows v).2 t).1 = dataSlot

/-- Actual decoder eligibility for candidate v. The physical positive
observation is shared, but the DATA coordinate comes from v's own row. -/
def candidateEligible (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) : Prop :=
  positiveRound x i t ∧ rowIsData rows v t

/-- Boolean observation of candidate eligibility for finite filtering. -/
def candidateEligibleFlag (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) : Bool := by
  classical
  exact decide (candidateEligible x rows i v t)

theorem candidateEligibleFlag_eq_true_iff
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (v : Fin (M p)) (t : Fin p.T) :
    candidateEligibleFlag x rows i v t = true ↔ candidateEligible x rows i v t := by
  simp [candidateEligibleFlag]

/-- Candidate v's forward identification bit at follower i's private ID. -/
def candidateForwardBit (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) : Bool :=
  (rows v).1 (x.privateId i) t

/-- Literal eligible-positive set through calendar prefix k, including each
candidate's own DATA restriction. -/
def eligiblePrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) : Finset (Fin p.T) := by
  classical
  exact Finset.univ.filter fun t => t.val < k ∧ candidateEligible x rows i v t

/-- A candidate has a mismatch in its literal full eligible-positive prefix. -/
def hasMismatchPrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) : Prop :=
  ∃ t, t ∈ eligiblePrefix x rows i v k ∧
    candidateForwardBit x rows i v t = false

/-- Every bit in the literal full eligible-positive prefix is one. -/
def allForwardPrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) : Prop :=
  ∀ t, t ∈ eligiblePrefix x rows i v k →
    candidateForwardBit x rows i v t = true

/-- The source decoder's full prefix pass predicate for one candidate. -/
def passesPrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) : Prop :=
  q_dec p ≤ (eligiblePrefix x rows i v k).card ∧
    allForwardPrefix x rows i v k

/-- The selected source quota is positive. -/
theorem q_dec_pos (p : Parameters) : 0 < q_dec p := by
  have hL : 0 < L0 p := by
    unfold L0
    exact Nat.pow_pos (by decide)
  rw [q_dec]
  exact Nat.mul_pos (Nat.mul_pos (by decide) hL)
    (ConstructorDimensions.b_N_pos p)

/-- Literal pass at a prefix ending at an eligible positive round. -/
def passesAt (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) : Prop :=
  candidateEligible x rows i v t ∧ passesPrefix x rows i v (t.val + 1)

/-- Some eligible positive prefix strictly before k has passed the literal
quota and forward-bit test. -/
def hasPassingPrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) : Prop :=
  ∃ t, t.val < k ∧ passesAt x rows i v t

/-- Per-row count, per-row permanent rejection flag, and sole pending
declaration. No other decoder or physical register is owned here. -/
structure Registers (p : Parameters) where
  count : Fin (M p) → ℕ
  dead : Fin (M p) → Bool
  pending : Option (Fin (M p))

/-- Extensionality for the three exposed candidate registers. -/
theorem registers_ext {r₁ r₂ : Registers p}
    (hcount : ∀ v, r₁.count v = r₂.count v)
    (hdead : ∀ v, r₁.dead v = r₂.dead v)
    (hpending : r₁.pending = r₂.pending) : r₁ = r₂ := by
  cases r₁
  cases r₂
  simp only [Registers.mk.injEq]
  exact ⟨funext hcount, funext hdead, hpending⟩

/-- Block-start reset of every candidate register. -/
def initialRegisters (p : Parameters) : Registers p :=
  ⟨fun _ => 0, fun _ => false, none⟩

/-- Return a member only when a finite set has exactly one member. The choice
is justified by an explicit uniqueness proof and is never used on a tie. -/
noncomputable def uniqueMember {α : Type} [DecidableEq α]
    (members : Finset α) : Option α := by
  classical
  exact if h : ∃! a, a ∈ members then some (Classical.choose h) else none

theorem uniqueMember_eq_some_iff {α : Type} [DecidableEq α]
    (members : Finset α) (a : α) :
    uniqueMember members = some a ↔ a ∈ members ∧ ∀ b, b ∈ members → b = a := by
  classical
  by_cases h : ∃! b, b ∈ members
  · have hspec := Classical.choose_spec h
    rw [uniqueMember, dite_eq_left h]
    constructor
    · intro heq
      injection heq with heq
      subst a
      exact ⟨hspec.1, fun b hb => hspec.2 b hb⟩
    · rintro ⟨ha, huniq⟩
      have heq : Classical.choose h = a := huniq _ hspec.1
      exact congrArg some heq
  · rw [uniqueMember, dite_eq_right h]
    constructor
    · intro heq
      cases heq
    · intro ha
      exact False.elim (h ⟨a, ha.1, fun b hb => ha.2 b hb⟩)

/-- The empty passing set has no unique member to save. -/
theorem uniqueMember_empty {α : Type} [DecidableEq α] :
    uniqueMember (∅ : Finset α) = none := by
  classical
  simp [uniqueMember]

/-- Rows passing the literal count and mismatch tests in a register state. -/
def passingSet (r : Registers p) : Finset (Fin (M p)) :=
  Finset.univ.filter fun v => q_dec p ≤ r.count v ∧ r.dead v = false

/-- Full-prefix candidates passing the quota and every forward-bit test. -/
def prefixPassingSet (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed}) (k : ℕ) :
    Finset (Fin (M p)) := by
  classical
  exact Finset.univ.filter fun v => passesPrefix x rows i v k

/-- Evidence update after this round's physical feedback. Every candidate is
updated from its own row DATA coordinate; pending is set by advance. -/
def updateEvidence (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) : Registers p := by
  classical
  exact ⟨fun v => if candidateEligible x rows i v t then r.count v + 1 else r.count v,
    fun v => if candidateEligible x rows i v t then
      r.dead v || decide (candidateForwardBit x rows i v t = false) else r.dead v,
    none⟩

/-- One actual post-feedback decoder step. It tests all updated candidates on
a positive private-ID-zero observation and saves only a unique passer. -/
def advance (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) : Registers p := by
  classical
  exact if hpending : r.pending.isSome then r else
    if hpositive : positiveRound x i t then
      let updated := updateEvidence x rows i r t
      { updated with pending := uniqueMember (passingSet updated) }
    else r

/-- Candidate registers after processing the first k calendar rounds. -/
def run (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed}) : ℕ → Registers p
  | 0 => initialRegisters p
  | k + 1 => if hk : k < p.T then
      advance x rows i (run x rows i k) ⟨k, hk⟩ else run x rows i k

theorem run_zero (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed}) :
    run x rows i 0 = initialRegisters p := rfl

theorem run_succ (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    run x rows i (t.val + 1) = advance x rows i (run x rows i t.val) t := by
  simp only [run, t.isLt, ↓reduceDIte]

theorem mem_eligiblePrefix_iff (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) (t : Fin p.T) :
    t ∈ eligiblePrefix x rows i v k ↔
      t.val < k ∧ candidateEligible x rows i v t := by
  simp only [eligiblePrefix, Finset.mem_filter, Finset.mem_univ, true_and]

theorem eligiblePrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) :
    eligiblePrefix x rows i v (t.val + 1) =
      if candidateEligibleFlag x rows i v t = true then
        insert t (eligiblePrefix x rows i v t.val)
      else eligiblePrefix x rows i v t.val := by
  classical
  have hflagFalse : ∀ {v}, ¬ candidateEligible x rows i v t →
      candidateEligibleFlag x rows i v t = false := by
    intro v hv
    cases hflag : candidateEligibleFlag x rows i v t with
    | false => rfl
    | true => exact False.elim (hv ((candidateEligibleFlag_eq_true_iff x rows i v t).1 hflag))
  ext r
  by_cases he : candidateEligible x rows i v t
  · have hf := (candidateEligibleFlag_eq_true_iff x rows i v t).2 he
    rw [ite_eq_left hf]
    rw [mem_eligiblePrefix_iff, Finset.mem_insert, mem_eligiblePrefix_iff]
    constructor
    · rintro ⟨hrlt, hrel⟩
      by_cases hrt : r = t
      · exact Or.inl hrt
      · right
        refine ⟨?_, hrel⟩
        have hne : r.val ≠ t.val := fun h => hrt (Fin.ext h)
        omega
    · rintro (hrt | ⟨hrlt, hrel⟩)
      · subst r
        exact ⟨by omega, he⟩
      · exact ⟨by omega, hrel⟩
  · have hf := hflagFalse he
    rw [ite_eq_right (by simp [hf])]
    rw [mem_eligiblePrefix_iff, mem_eligiblePrefix_iff]
    by_cases hrt : r = t
    · subst r
      constructor
      · rintro ⟨_, hrel⟩
        exact False.elim (he hrel)
      · rintro ⟨hlt, _⟩
        exact False.elim (by omega)
    · constructor
      · rintro ⟨hrlt, hrel⟩
        have hne : r.val ≠ t.val := fun h => hrt (Fin.ext h)
        exact ⟨by omega, hrel⟩
      · rintro ⟨hrlt, hrel⟩
        have hne : r.val ≠ t.val := fun h => hrt (Fin.ext h)
        exact ⟨by omega, hrel⟩

theorem eligiblePrefix_card_succ (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) (he : candidateEligible x rows i v t) :
    (eligiblePrefix x rows i v (t.val + 1)).card =
      (eligiblePrefix x rows i v t.val).card + 1 := by
  have hf := (candidateEligibleFlag_eq_true_iff x rows i v t).2 he
  rw [eligiblePrefix_succ, ite_eq_left hf]
  have hnot : t ∉ eligiblePrefix x rows i v t.val := by
    intro hmem
    have hlt := (mem_eligiblePrefix_iff x rows i v t.val t).mp hmem
    omega
  exact Finset.card_insert_of_notMem hnot

theorem allForwardPrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) :
    allForwardPrefix x rows i v (t.val + 1) ↔
      allForwardPrefix x rows i v t.val ∧
        (candidateEligible x rows i v t →
          candidateForwardBit x rows i v t = true) := by
  unfold allForwardPrefix
  rw [eligiblePrefix_succ]
  by_cases he : candidateEligible x rows i v t
  · have hf := (candidateEligibleFlag_eq_true_iff x rows i v t).2 he
    rw [ite_eq_left hf]
    simp only [Finset.forall_mem_insert]
    constructor
    · rintro ⟨ht, hall⟩
      exact ⟨hall, fun _ => ht⟩
    · rintro ⟨hall, ht⟩
      exact ⟨ht he, hall⟩
  · have hf : candidateEligibleFlag x rows i v t ≠ true := by
      intro h
      exact he ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h)
    rw [ite_eq_right (by simp [hf])]
    constructor
    · intro hall
      exact ⟨hall, fun h => False.elim (he h)⟩
    · intro h
      exact h.1

/-- A full-prefix pass must first have occurred at one of its eligible rounds.
This exposes the event used by the accepted true-row pending equivalence. -/
theorem passesPrefix_implies_hasPassingPrefix
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (v : Fin (M p)) (k : ℕ)
    (hk : k ≤ p.T) (hpass : passesPrefix x rows i v k) :
    hasPassingPrefix x rows i v k := by
  induction k with
  | zero =>
      have hpfx : eligiblePrefix x rows i v 0 = ∅ := by
        classical
        ext u
        rw [mem_eligiblePrefix_iff]
        simp
      rw [passesPrefix, hpfx] at hpass
      have hfalse : False := (Nat.not_le_of_gt (q_dec_pos p)) hpass.1
      exact False.elim hfalse
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have hpass' : passesPrefix x rows i v (t.val + 1) := by
        simpa [t] using hpass
      by_cases he : candidateEligible x rows i v t
      · exact ⟨t, by simp [t], ⟨he, hpass'⟩⟩
      · have hprefix := eligiblePrefix_succ x rows i v t
        have hf : candidateEligibleFlag x rows i v t = false := by
          cases h : candidateEligibleFlag x rows i v t with
          | false => rfl
          | true => exact False.elim (he
              ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h))
        simp only [hf, Bool.false_eq_true, ↓reduceIte] at hprefix
        have hall := (allForwardPrefix_succ x rows i v t).mp hpass'.2
        have hprev : passesPrefix x rows i v k := by
          rw [passesPrefix]
          refine ⟨?_, ?_⟩
          · rw [← hprefix]
            simpa [t] using hpass'.1
          · simpa [t] using hall.1
        rcases ih (by omega) hprev with ⟨u, hu, hpassu⟩
        exact ⟨u, by omega, hpassu⟩

theorem hasMismatchPrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) :
    hasMismatchPrefix x rows i v (t.val + 1) ↔
      hasMismatchPrefix x rows i v t.val ∨
        (candidateEligible x rows i v t ∧
          candidateForwardBit x rows i v t = false) := by
  unfold hasMismatchPrefix
  rw [eligiblePrefix_succ]
  by_cases he : candidateEligible x rows i v t
  · have hf := (candidateEligibleFlag_eq_true_iff x rows i v t).2 he
    rw [ite_eq_left hf]
    simp only [Finset.exists_mem_insert]
    simp only [he, true_and]
    exact or_comm
  · have hf : candidateEligibleFlag x rows i v t ≠ true := by
      intro h
      exact he ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h)
    rw [ite_eq_right (by simp [hf])]
    simp only [he, false_and, or_false]

theorem allForwardPrefix_iff_noMismatch (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ) :
    allForwardPrefix x rows i v k ↔ ¬ hasMismatchPrefix x rows i v k := by
  constructor
  · intro hall ⟨t, ht, hbit⟩
    rw [hall t ht] at hbit
    cases hbit
  · intro hnone t ht
    cases hbit : candidateForwardBit x rows i v t with
    | false => exact False.elim (hnone ⟨t, ht, hbit⟩)
    | true => simp

theorem hasMismatchPrefix_mono (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) {k l : ℕ} (hkl : k ≤ l)
    (hm : hasMismatchPrefix x rows i v k) :
    hasMismatchPrefix x rows i v l := by
  rcases hm with ⟨t, ht, hbit⟩
  have ht' := (mem_eligiblePrefix_iff x rows i v k t).mp ht
  exact ⟨t, (mem_eligiblePrefix_iff x rows i v l t).mpr
    ⟨Nat.lt_of_lt_of_le ht'.1 hkl, ht'.2⟩, hbit⟩

theorem advance_eq_of_not_positive (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) (h : ¬ positiveRound x i t) :
    advance x rows i r t = r := by
  classical
  simp [advance, h]

theorem advance_eq_of_pending (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) (h : r.pending.isSome) :
    advance x rows i r t = r := by
  simp [advance, h]

/-- A saved candidate declaration remains pending through every later
calendar prefix. -/
theorem pending_persists
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) {k l : ℕ} (hkl : k ≤ l)
    (v : Fin (M p)) (hpending : (run x rows i k).pending = some v) :
    (run x rows i l).pending = some v := by
  induction l generalizing k with
  | zero =>
      have hk : k = 0 := by omega
      subst k
      exact hpending
  | succ l ih =>
      by_cases hkn : k ≤ l
      · have hcurrent := ih hkn hpending
        by_cases htime : l < p.T
        · let t : Fin p.T := ⟨l, htime⟩
          have hfreeze := advance_eq_of_pending x rows i
            (run x rows i l) t (by simp [hcurrent])
          rw [show l + 1 = t.val + 1 by rfl, run_succ, hfreeze]
          exact hcurrent
        · have hsame : run x rows i (l + 1) = run x rows i l := by
            simp [run, htime]
          rw [hsame]
          exact hcurrent
      · have hk : k = l + 1 := by omega
        subst k
        exact hpending

theorem advance_eq_of_outside_block (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) (ht : t ∉ calendarBlock p s) :
    advance x rows i r t = r := by
  apply advance_eq_of_not_positive x rows i r t
  exact fun h => ht h.1

theorem advance_eq_of_inactive (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) (ha : x.active i = false) :
    advance x rows i r t = r := by
  apply advance_eq_of_not_positive x rows i r t
  intro h
  unfold positiveRound at h
  rcases h with ⟨_, hactive, _, _⟩
  rw [ha] at hactive
  cases hactive

theorem advance_eq_of_id_one (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T)
    (hid : x.ids (x.privateId i) t = true) : advance x rows i r t = r := by
  apply advance_eq_of_not_positive x rows i r t
  intro h
  unfold positiveRound at h
  rcases h with ⟨_, _, hid', _⟩
  rw [hid] at hid'
  cases hid'

/-- Exact per-row one-step count and mismatch equations. The current positive
feedback is included before testing the quota. -/
theorem advance_count_dead_eq (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) (hp : r.pending = none)
    (v : Fin (M p)) :
    (advance x rows i r t).count v =
        (if candidateEligibleFlag x rows i v t = true then r.count v + 1 else r.count v) ∧
      (advance x rows i r t).dead v =
        (if candidateEligibleFlag x rows i v t = true then
          r.dead v || decide (candidateForwardBit x rows i v t = false)
        else r.dead v) := by
  classical
  by_cases hpositive : positiveRound x i t
  · have hnone : ¬ r.pending.isSome := by simp [hp]
    rw [advance, dite_eq_right hnone]
    rw [dite_eq_left hpositive]
    by_cases he : candidateEligible x rows i v t
    · have hf := (candidateEligibleFlag_eq_true_iff x rows i v t).2 he
      simp only [hf, updateEvidence, he, ↓reduceIte]
      exact ⟨trivial, trivial⟩
    · have hf : candidateEligibleFlag x rows i v t ≠ true := by
        intro h
        exact he ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h)
      have hfFalse : candidateEligibleFlag x rows i v t = false := by
        cases h : candidateEligibleFlag x rows i v t with
        | false => rfl
        | true => exact False.elim (hf h)
      simp only [hfFalse, Bool.false_eq_true, updateEvidence, he, ↓reduceIte]
      exact ⟨trivial, trivial⟩
  · have hnot : ¬ candidateEligible x rows i v t := fun he => hpositive he.1
    have hf : candidateEligibleFlag x rows i v t ≠ true := by
      intro h
      exact hnot ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h)
    simp [advance_eq_of_not_positive x rows i r t hpositive, hf]

/-- A decoder step reads only each candidate's current DATA bit and current
forward bit, in addition to the shared physical feedback. -/
theorem advance_eq_of_same_current_row_evidence
    (x : BootstrapPhysicalBlock.Input p s) (rows₁ rows₂ : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (r : Registers p) (t : Fin p.T)
    (hdata : ∀ v, rowIsData rows₁ v t ↔ rowIsData rows₂ v t)
    (hbit : ∀ v, candidateForwardBit x rows₁ i v t =
      candidateForwardBit x rows₂ i v t) :
    advance x rows₁ i r t = advance x rows₂ i r t := by
  classical
  have hEligible (v : Fin (M p)) :
      candidateEligible x rows₁ i v t ↔ candidateEligible x rows₂ i v t := by
    unfold candidateEligible
    constructor
    · rintro ⟨hp, hd⟩
      exact ⟨hp, (hdata v).mp hd⟩
    · rintro ⟨hp, hd⟩
      exact ⟨hp, (hdata v).mpr hd⟩
  by_cases hpending : r.pending.isSome
  · simp [advance, hpending]
  · by_cases hpositive : positiveRound x i t
    · have hupdate : updateEvidence x rows₁ i r t = updateEvidence x rows₂ i r t := by
        apply registers_ext
        · intro v
          simp only [updateEvidence]
          by_cases h₁ : candidateEligible x rows₁ i v t
          · have h₂ := hEligible v |>.mp h₁
            simp [h₁, h₂]
          · have h₂ : ¬ candidateEligible x rows₂ i v t := by
              intro h₂
              exact h₁ ((hEligible v).mpr h₂)
            simp [h₁, h₂]
        · intro v
          simp only [updateEvidence]
          by_cases h₁ : candidateEligible x rows₁ i v t
          · have h₂ := hEligible v |>.mp h₁
            simp [h₁, h₂, hbit v]
          · have h₂ : ¬ candidateEligible x rows₂ i v t := by
              intro h₂
              exact h₁ ((hEligible v).mpr h₂)
            simp [h₁, h₂]
        · rfl
      simp [advance, hpending, hpositive, hupdate]
    · simp [advance, hpending, hpositive]

/-- The entire decoder register through prefix `k` depends on candidate rows
only through their DATA and forward bits strictly before `k`. The supplied
physical input and its feedback history are held fixed. -/
theorem run_eq_of_same_past_row_evidence
    (x : BootstrapPhysicalBlock.Input p s) (rows₁ rows₂ : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (k : ℕ)
    (hdata : ∀ v t, t.val < k →
      (rowIsData rows₁ v t ↔ rowIsData rows₂ v t))
    (hbit : ∀ v t, t.val < k →
      candidateForwardBit x rows₁ i v t = candidateForwardBit x rows₂ i v t) :
    run x rows₁ i k = run x rows₂ i k := by
  induction k with
  | zero => simp [run, initialRegisters]
  | succ k ih =>
      have hdataPrev : ∀ v t, t.val < k →
          (rowIsData rows₁ v t ↔ rowIsData rows₂ v t) := by
        intro v t ht
        exact hdata v t (by omega)
      have hbitPrev : ∀ v t, t.val < k →
          candidateForwardBit x rows₁ i v t = candidateForwardBit x rows₂ i v t := by
        intro v t ht
        exact hbit v t (by omega)
      have hprev := ih hdataPrev hbitPrev
      by_cases htime : k < p.T
      · let t : Fin p.T := ⟨k, htime⟩
        have hdataAt : ∀ v, rowIsData rows₁ v t ↔ rowIsData rows₂ v t := by
          intro v
          exact hdata v t (by simp [t])
        have hbitAt : ∀ v,
            candidateForwardBit x rows₁ i v t = candidateForwardBit x rows₂ i v t := by
          intro v
          exact hbit v t (by simp [t])
        rw [show k + 1 = t.val + 1 by rfl,
          run_succ x rows₁ i t, run_succ x rows₂ i t, hprev]
        exact advance_eq_of_same_current_row_evidence x rows₁ rows₂ i
          (run x rows₂ i k) t hdataAt hbitAt
      · have hsame₁ : run x rows₁ i (k + 1) = run x rows₁ i k := by
          simp [run, htime]
        have hsame₂ : run x rows₂ i (k + 1) = run x rows₂ i k := by
          simp [run, htime]
        rw [hsame₁, hsame₂]
        exact hprev

/-- A no-pending run stores precisely the full literal prefix cardinality and
the mismatch flag, for every candidate row. -/
theorem count_dead_before_save (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed}) (k : ℕ)
    (hk : k ≤ p.T) (hpending : (run x rows i k).pending = none)
    (v : Fin (M p)) :
    (run x rows i k).count v = (eligiblePrefix x rows i v k).card ∧
      ((run x rows i k).dead v = true ↔ hasMismatchPrefix x rows i v k) := by
  induction k with
  | zero =>
      simp [run, initialRegisters, eligiblePrefix, hasMismatchPrefix]
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have hstep := run_succ x rows i t
      rw [hstep] at hpending ⊢
      have htval : t.val = k := rfl
      rw [htval] at hpending ⊢
      have hprev : (run x rows i k).pending = none := by
        by_contra hne
        obtain ⟨w, hw⟩ : ∃ w, (run x rows i k).pending = some w := by
          cases h : (run x rows i k).pending with
          | none => exact False.elim (hne h)
          | some w => exact ⟨w, rfl⟩
        have hfreeze := advance_eq_of_pending x rows i
          (run x rows i k) t (by simp [hw])
        rw [hfreeze] at hpending
        simp [hw] at hpending
      have hprevInv := ih (by omega) hprev
      have hone := advance_count_dead_eq x rows i (run x rows i k) t hprev v
      by_cases he : candidateEligible x rows i v t
      · have hcard := eligiblePrefix_card_succ x rows i v t he
        rw [htval] at hcard
        have hf := (candidateEligibleFlag_eq_true_iff x rows i v t).2 he
        simp only [hf, ↓reduceIte] at hone
        have hmis := hasMismatchPrefix_succ x rows i v t
        rw [htval] at hmis
        rw [hone.1, hone.2, hcard, hmis]
        constructor
        · rw [hprevInv.1]
        · rw [Bool.or_eq_true, decide_eq_true_eq]
          simpa [he] using or_congr hprevInv.2 Iff.rfl
      · have hprefix : eligiblePrefix x rows i v (k + 1) =
            eligiblePrefix x rows i v k := by
          have hf : candidateEligibleFlag x rows i v t ≠ true := by
            intro h
            exact he ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h)
          have hfFalse : candidateEligibleFlag x rows i v t = false := by
            cases h : candidateEligibleFlag x rows i v t with
            | false => rfl
            | true => exact False.elim (hf h)
          have hpfx := eligiblePrefix_succ x rows i v t
          simp only [hfFalse, Bool.false_eq_true, ↓reduceIte] at hpfx
          rw [htval] at hpfx
          exact hpfx
        have hmis := hasMismatchPrefix_succ x rows i v t
        rw [htval] at hmis
        simp [he] at hmis
        have hf : candidateEligibleFlag x rows i v t ≠ true := by
          intro h
          exact he ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h)
        have hfFalse : candidateEligibleFlag x rows i v t = false := by
          cases h : candidateEligibleFlag x rows i v t with
          | false => rfl
          | true => exact False.elim (hf h)
        simp only [hfFalse, Bool.false_eq_true, ↓reduceIte] at hone
        rw [hone.1, hone.2, hprefix, hmis]
        exact hprevInv

/-- Counts and mismatch flags immediately after processing a no-pending
observation have their exact full-prefix meanings, for every candidate. -/
theorem updateEvidence_count_dead_eq_prefix
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (t : Fin p.T)
    (hkt : t.val = k) (hpending : (run x rows i k).pending = none)
    (v : Fin (M p)) :
    (updateEvidence x rows i (run x rows i k) t).count v =
        (eligiblePrefix x rows i v (k + 1)).card ∧
      ((updateEvidence x rows i (run x rows i k) t).dead v = true ↔
        hasMismatchPrefix x rows i v (k + 1)) := by
  have hprev := count_dead_before_save x rows i k (by omega) hpending v
  by_cases he : candidateEligible x rows i v t
  · have hcard := eligiblePrefix_card_succ x rows i v t he
    rw [hkt] at hcard
    have hmis := hasMismatchPrefix_succ x rows i v t
    rw [hkt] at hmis
    constructor
    · simp only [updateEvidence, he, ite_true]
      rw [hcard, hprev.1]
    · simp only [updateEvidence, he, ite_true]
      rw [Bool.or_eq_true, decide_eq_true_eq, hmis]
      exact or_congr hprev.2 (by simp [he])
  · have hf : candidateEligibleFlag x rows i v t = false := by
      cases hflag : candidateEligibleFlag x rows i v t with
      | false => rfl
      | true => exact False.elim (he ((candidateEligibleFlag_eq_true_iff x rows i v t).1 hflag))
    have hpfx := eligiblePrefix_succ x rows i v t
    simp only [hf, Bool.false_eq_true, ↓reduceIte] at hpfx
    rw [hkt] at hpfx
    have hmis := hasMismatchPrefix_succ x rows i v t
    rw [hkt] at hmis
    simp only [he, false_and, or_false] at hmis
    constructor
    · simp only [updateEvidence, he, ite_false]
      rw [hpfx, hprev.1]
    · simp only [updateEvidence, he, ite_false]
      exact hprev.2.trans hmis.symm

/-- The set computed by the updated registers is exactly the set satisfying
the literal quota and forward-bit tests on the current complete prefix. -/
theorem updateEvidence_passingSet_eq_prefix
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (t : Fin p.T)
    (hkt : t.val = k) (hpending : (run x rows i k).pending = none) :
    passingSet (updateEvidence x rows i (run x rows i k) t) =
      prefixPassingSet x rows i (k + 1) := by
  classical
  ext v
  simp only [passingSet, prefixPassingSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hu := updateEvidence_count_dead_eq_prefix x rows i k t hkt hpending v
  constructor
  · rintro ⟨hq, hdead⟩
    have hquota : q_dec p ≤ (eligiblePrefix x rows i v (k + 1)).card := by
      rw [← hu.1]
      exact hq
    have hnomis : ¬ hasMismatchPrefix x rows i v (k + 1) := by
      intro hm
      have htrue := hu.2.mpr hm
      rw [hdead] at htrue
      cases htrue
    exact ⟨hquota,
      (allForwardPrefix_iff_noMismatch x rows i v (k + 1)).mpr hnomis⟩
  · rintro ⟨hq, hall⟩
    have hquota : q_dec p ≤ (updateEvidence x rows i (run x rows i k) t).count v := by
      rw [hu.1]
      exact hq
    have hdead :
        (updateEvidence x rows i (run x rows i k) t).dead v = false := by
      cases hd : (updateEvidence x rows i (run x rows i k) t).dead v with
      | false => rfl
      | true =>
          have hm := hu.2.mp hd
          exact False.elim ((allForwardPrefix_iff_noMismatch x rows i v (k + 1)).mp hall hm)
    exact ⟨hquota, hdead⟩

/-- A mismatched candidate never satisfies the full-prefix pass predicate. -/
theorem no_pass_after_mismatch (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (k : ℕ)
    (hm : hasMismatchPrefix x rows i v k) :
    ¬ passesPrefix x rows i v k := by
  intro hp
  exact (allForwardPrefix_iff_noMismatch x rows i v k).mp hp.2 hm

/-- Once its dead flag is set, a candidate remains dead even if a declaration
later freezes all candidate registers. -/
theorem dead_persists (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) {k l : ℕ} (hkl : k ≤ l)
    (hdead : (run x rows i k).dead v = true) :
    (run x rows i l).dead v = true := by
  have hstep_dead (r : Registers p) (t : Fin p.T)
      (hr : r.dead v = true) : (advance x rows i r t).dead v = true := by
    classical
    by_cases hp : r.pending.isSome
    · simp [advance, hp, hr]
    · by_cases hpositive : positiveRound x i t
      · simp [advance, hp, hpositive, updateEvidence, hr]
      · simp [advance, hp, hpositive, hr]
  induction l generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      exact hdead
  | succ n ih =>
      by_cases hkn : k ≤ n
      · have hcurrent := ih hkn hdead
        by_cases htime : n < p.T
        · let t : Fin p.T := ⟨n, htime⟩
          rw [show n + 1 = t.val + 1 by rfl, run_succ]
          exact hstep_dead (run x rows i n) t hcurrent
        · simpa [run, htime] using hcurrent
      · have hknext : k = n + 1 := by omega
        subst k
        exact hdead

/-- A no-pending update saves v exactly when its updated literal passing set is
the singleton containing v. -/
theorem advance_pending_eq_some_iff (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (r : Registers p) (t : Fin p.T) (hp : r.pending = none)
    (hpositive : positiveRound x i t) (v : Fin (M p)) :
    (advance x rows i r t).pending = some v ↔
      passingSet (updateEvidence x rows i r t) = {v} := by
  classical
  have hnone : ¬ r.pending.isSome := by simp [hp]
  rw [advance, dite_eq_right hnone]
  simp only [hpositive]
  change uniqueMember (passingSet (updateEvidence x rows i r t)) = some v ↔
    passingSet (updateEvidence x rows i r t) = {v}
  rw [uniqueMember_eq_some_iff, Finset.eq_singleton_iff_unique_mem]

/-- The literal false-candidate clean event through prefix k. -/
def noFalseCandidatePassPrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (J : Fin (M p)) (k : ℕ) : Prop :=
  ∀ v, v ≠ J → ¬ passesPrefix x rows i v k

/-- Candidate J uses exactly the accepted true-row eligibility event under the
explicit equality between the physical row and the selected complete row. -/
theorem true_candidate_eligible_iff
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (t : Fin p.T) :
    candidateEligible x rows i J t ↔
      BootstrapTruePrefixController.eligible x i t := by
  rw [candidateEligible, positiveRound, BootstrapTruePrefixController.eligible]
  constructor
  · rintro ⟨⟨ht, ha, hid, hpositive⟩, hdata⟩
    refine ⟨ht, ha, hid, ?_, hpositive⟩
    change slotDraw ((rows J).2 t).1 = dataSlot at hdata
    change slotDraw (x.row.2 t).1 = dataSlot
    rw [hrow]
    exact hdata
  · rintro ⟨ht, ha, hid, hslot, hpositive⟩
    refine ⟨⟨ht, ha, hid, hpositive⟩, ?_⟩
    change slotDraw (x.row.2 t).1 = dataSlot at hslot
    change slotDraw ((rows J).2 t).1 = dataSlot
    rw [← hrow]
    exact hslot

/-- The selected candidate's literal eligible-positive set is the true
controller's complete prefix set. -/
theorem true_candidate_prefix_eq
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (k : ℕ) :
    eligiblePrefix x rows i J k =
      BootstrapTruePrefixController.eligiblePrefix x i k := by
  classical
  ext t
  rw [mem_eligiblePrefix_iff,
    BootstrapTruePrefixController.mem_eligiblePrefix_iff]
  rw [true_candidate_eligible_iff x rows i J hrow t]
  constructor
  · rintro ⟨hlt, he⟩
    exact ⟨he.1, hlt, he⟩
  · rintro ⟨_, hlt, he⟩
    exact ⟨hlt, he⟩

/-- The all-candidate true-row bit is the accepted controller's true bit. -/
theorem true_candidate_forward_eq
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (t : Fin p.T) :
    candidateForwardBit x rows i J t =
      BootstrapTruePrefixController.trueForwardBit x i t := by
  change (rows J).1 (x.privateId i) t = x.row.1 (x.privateId i) t
  rw [← hrow]

/-- The full literal pass predicate for J agrees with its quota and forward-bit
test in the accepted true-row prefix. -/
theorem true_candidate_passes_iff
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (k : ℕ) :
    passesPrefix x rows i J k ↔
      q_dec p ≤ (BootstrapTruePrefixController.eligiblePrefix x i k).card ∧
        BootstrapTruePrefixController.allTruePrefix x i k := by
  rw [passesPrefix]
  constructor
  · rintro ⟨hq, hall⟩
    have hq' := hq
    rw [true_candidate_prefix_eq x rows i J hrow k] at hq'
    refine ⟨hq', ?_⟩
    intro t ht
    rw [← true_candidate_forward_eq x rows i J hrow t]
    have ht' : t ∈ eligiblePrefix x rows i J k := by
      rw [true_candidate_prefix_eq x rows i J hrow k]
      exact ht
    exact hall t ht'
  · rintro ⟨hq, hall⟩
    have hq' := hq
    rw [← true_candidate_prefix_eq x rows i J hrow k] at hq'
    refine ⟨hq', ?_⟩
    intro t ht
    rw [true_candidate_forward_eq x rows i J hrow t]
    have ht' : t ∈ BootstrapTruePrefixController.eligiblePrefix x i k := by
      rw [← true_candidate_prefix_eq x rows i J hrow k]
      exact ht
    exact hall t ht'

/-- The deterministic clean event through every prefix up to `k`: no row
other than the selected row ever satisfies the literal full-prefix tests. -/
def cleanPrefix (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (J : Fin (M p)) (k : ℕ) : Prop :=
  ∀ n, n ≤ k → noFalseCandidatePassPrefix x rows i J n

/-- If the accepted true controller has not declared by prefix `k`, then the
selected row has not passed the literal full-prefix test there. -/
theorem true_candidate_no_pass_before_save
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (k : ℕ) (hk : k ≤ p.T)
    (hpending : (BootstrapTruePrefixController.run x i k).pending = false) :
    ¬ passesPrefix x rows i J k := by
  intro hpass
  have hpassing := passesPrefix_implies_hasPassingPrefix x rows i J k hk hpass
  have htruePassing : BootstrapTruePrefixController.hasPassingPrefix x i k := by
    rcases hpassing with ⟨t, ht, he, hp⟩
    have he' := (true_candidate_eligible_iff x rows i J hrow t).mp he
    have hp' := (true_candidate_passes_iff x rows i J hrow (t.val + 1)).mp hp
    exact ⟨t, ht, by
      rw [BootstrapTruePrefixController.passesAt]
      exact ⟨he', hp'⟩⟩
  have hdeclared :=
    (BootstrapTruePrefixController.pending_iff_passingPrefix x i k hk).mpr
      htruePassing
  rw [hpending] at hdeclared
  cases hdeclared

/-- With no earlier full-prefix pass, passing at the new full prefix is
equivalent to passing at the current eligible round. -/
theorem passesPrefix_succ_iff_passesAt
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (v : Fin (M p))
    (t : Fin p.T) (k : ℕ) (hkt : t.val = k)
    (hprior : ¬ passesPrefix x rows i v k) :
    passesPrefix x rows i v (k + 1) ↔ passesAt x rows i v t := by
  constructor
  · intro hpass
    by_cases he : candidateEligible x rows i v t
    · exact ⟨he, by simpa [hkt] using hpass⟩
    · have hf : candidateEligibleFlag x rows i v t = false := by
        cases h : candidateEligibleFlag x rows i v t with
        | false => rfl
        | true => exact False.elim (he
            ((candidateEligibleFlag_eq_true_iff x rows i v t).1 h))
      have hprefix := eligiblePrefix_succ x rows i v t
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hprefix
      rw [hkt] at hprefix
      have hall := (allForwardPrefix_succ x rows i v t).mp
        (by simpa [hkt] using hpass.2)
      have hprev : passesPrefix x rows i v k := by
        rw [passesPrefix]
        refine ⟨?_, by simpa [hkt] using hall.1⟩
        rw [← hprefix]
        simpa [hkt] using hpass.1
      exact False.elim (hprior hprev)
  · rintro ⟨he, hpass⟩
    exact by simpa [hkt] using hpass

/-- Candidate J's current pass test is exactly the accepted true-row pass
test under the explicit complete-row equality. -/
theorem true_candidate_passesAt_iff
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (t : Fin p.T) :
    passesAt x rows i J t ↔ BootstrapTruePrefixController.passesAt x i t := by
  rw [passesAt, BootstrapTruePrefixController.passesAt]
  constructor
  · rintro ⟨he, hp⟩
    have he' := (true_candidate_eligible_iff x rows i J hrow t).mp he
    have hp' := (true_candidate_passes_iff x rows i J hrow (t.val + 1)).mp hp
    exact ⟨he', hp'.1, hp'.2⟩
  · rintro ⟨he, hq, hall⟩
    have he' := (true_candidate_eligible_iff x rows i J hrow t).mpr he
    have hp' := (true_candidate_passes_iff x rows i J hrow (t.val + 1)).mpr
      ⟨hq, hall⟩
    exact ⟨he', hp'⟩

/-- On a clean prefix, the literal passing set is either exactly `{J}` or
empty, according to J's own full-prefix test. -/
theorem prefixPassingSet_eq_singleton_or_empty
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p)) (k : ℕ)
    (hclean : noFalseCandidatePassPrefix x rows i J k) :
    (passesPrefix x rows i J k → prefixPassingSet x rows i k = {J}) ∧
      (¬ passesPrefix x rows i J k → prefixPassingSet x rows i k = ∅) := by
  classical
  constructor
  · intro hJ
    ext v
    simp only [prefixPassingSet, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_singleton]
    constructor
    · intro hv
      by_cases hvJ : v = J
      · exact hvJ
      · exact False.elim ((hclean v hvJ) hv)
    · intro hv
      subst v
      exact hJ
  · intro hJ
    ext v
    simp only [prefixPassingSet, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hv
      by_cases hvJ : v = J
      · subst v
        exact False.elim (hJ hv)
      · exact False.elim ((hclean v hvJ) hv)
    · intro hv
      exact False.elim (Finset.notMem_empty v hv)

/-- From a false pending state, the accepted controller declares on this
round exactly when its current literal pass test holds. -/
theorem true_pending_after_iff_passesAt
    (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) (k : ℕ)
    (hkt : t.val = k)
    (hpending : (BootstrapTruePrefixController.run x i k).pending = false) :
    (BootstrapTruePrefixController.run x i (k + 1)).pending = true ↔
      BootstrapTruePrefixController.passesAt x i t := by
  have hk : k + 1 ≤ p.T := by omega
  rw [BootstrapTruePrefixController.pending_iff_passingPrefix x i (k + 1) hk]
  rw [show k + 1 = t.val + 1 by omega,
    BootstrapTruePrefixController.hasPassingPrefix_succ]
  have hno : ¬ BootstrapTruePrefixController.hasPassingPrefix x i k := by
    intro hpass
    have hdeclared :=
      (BootstrapTruePrefixController.pending_iff_passingPrefix x i k (by omega)).mpr
        hpass
    rw [hpending] at hdeclared
    cases hdeclared
  have hnot : ¬ BootstrapTruePrefixController.hasPassingPrefix x i t.val := by
    simpa [hkt] using hno
  simp [hnot]

/-- A clean full-prefix pass by J at the new endpoint is the same event as
the accepted controller's declaration on the current round. -/
theorem true_candidate_prefixPass_iff_pendingAfter
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p)) (t : Fin p.T)
    (k : ℕ) (hkt : t.val = k) (hrow : x.row = rows J)
    (hpending : (BootstrapTruePrefixController.run x i k).pending = false) :
    passesPrefix x rows i J (k + 1) ↔
      (BootstrapTruePrefixController.run x i (k + 1)).pending = true := by
  have hprior := true_candidate_no_pass_before_save x rows i J hrow k
    (by omega) hpending
  have hcurrent := passesPrefix_succ_iff_passesAt x rows i J t k hkt hprior
  have hpassAt := true_candidate_passesAt_iff x rows i J hrow t
  have hpendingAt := true_pending_after_iff_passesAt x i t k hkt hpending
  exact hcurrent.trans (hpassAt.trans hpendingAt.symm)

/-- The selected row's count and dead registers take the same one-step update
as the accepted true-row controller. -/
theorem advance_true_count_dead_eq
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (r : Registers p)
    (rt : BootstrapTruePrefixController.Registers)
    (hcount : r.count J = rt.count) (hdead : r.dead J = rt.dead)
    (hpending : r.pending = none) (htpending : rt.pending = false)
    (t : Fin p.T) :
    (advance x rows i r t).count J =
        (BootstrapTruePrefixController.advance x i rt t).count ∧
      (advance x rows i r t).dead J =
        (BootstrapTruePrefixController.advance x i rt t).dead := by
  by_cases hpositive : positiveRound x i t
  · have hstep := advance_count_dead_eq x rows i r t hpending J
    by_cases he : candidateEligible x rows i J t
    · have hte := (true_candidate_eligible_iff x rows i J hrow t).mp he
      have hflagC := (candidateEligibleFlag_eq_true_iff x rows i J t).2 he
      have hflagT :=
        (BootstrapTruePrefixController.eligibleFlag_eq_true_iff x i t).2 hte
      have hbit := true_candidate_forward_eq x rows i J hrow t
      constructor
      · rw [hstep.1, hflagC]
        simp [BootstrapTruePrefixController.advance, hflagT, htpending, hcount]
      · rw [hstep.2, hflagC, hbit]
        simp [BootstrapTruePrefixController.advance, hflagT, htpending, hdead]
    · have hflagC : candidateEligibleFlag x rows i J t = false := by
        cases h : candidateEligibleFlag x rows i J t with
        | false => rfl
        | true => exact False.elim (he
            ((candidateEligibleFlag_eq_true_iff x rows i J t).1 h))
      have htnot : ¬ BootstrapTruePrefixController.eligible x i t := by
        intro hte
        exact he ((true_candidate_eligible_iff x rows i J hrow t).mpr hte)
      have hflagT : BootstrapTruePrefixController.eligibleFlag x i t = false := by
        cases h : BootstrapTruePrefixController.eligibleFlag x i t with
        | false => rfl
        | true => exact False.elim (htnot
            ((BootstrapTruePrefixController.eligibleFlag_eq_true_iff x i t).1 h))
      constructor
      · rw [hstep.1, hflagC]
        simp [BootstrapTruePrefixController.advance, hflagT, hcount]
      · rw [hstep.2, hflagC]
        simp [BootstrapTruePrefixController.advance, hflagT, hdead]
  · have hnotTrue : ¬ BootstrapTruePrefixController.eligible x i t := by
      intro hte
      rcases hte with ⟨ht, ha, hid, _, hobs⟩
      exact hpositive ⟨ht, ha, hid, hobs⟩
    constructor
    · rw [advance_eq_of_not_positive x rows i r t hpositive]
      rw [BootstrapTruePrefixController.advance_eq_of_not_eligible x i rt t hnotTrue]
      exact hcount
    · rw [advance_eq_of_not_positive x rows i r t hpositive]
      rw [BootstrapTruePrefixController.advance_eq_of_not_eligible x i rt t hnotTrue]
      exact hdead

/-- On a positive round, under the clean event, the all-row decoder's saved
row agrees exactly with the accepted controller's pending bit. -/
theorem advance_pending_eq_true_run
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (k : ℕ) (t : Fin p.T) (hkt : t.val = k)
    (hpending : (run x rows i k).pending = none)
    (htpending : (BootstrapTruePrefixController.run x i k).pending = false)
    (hpositive : positiveRound x i t)
    (hclean : noFalseCandidatePassPrefix x rows i J (k + 1)) :
    (advance x rows i (run x rows i k) t).pending =
      if (BootstrapTruePrefixController.run x i (k + 1)).pending = true
        then some J else none := by
  have hset := updateEvidence_passingSet_eq_prefix x rows i k t hkt hpending
  have hshape := prefixPassingSet_eq_singleton_or_empty x rows i J (k + 1) hclean
  have hpass := true_candidate_prefixPass_iff_pendingAfter x rows i J t k hkt
    hrow htpending
  by_cases hJ : passesPrefix x rows i J (k + 1)
  · have hsingleton :
        passingSet (updateEvidence x rows i (run x rows i k) t) = {J} :=
      hset.trans (hshape.1 hJ)
    have hsave := (advance_pending_eq_some_iff x rows i
      (run x rows i k) t hpending hpositive J).2 hsingleton
    rw [hpass.mp hJ]
    simp only [ite_true]
    exact hsave
  · have hempty :
        passingSet (updateEvidence x rows i (run x rows i k) t) = ∅ :=
      hset.trans (hshape.2 hJ)
    have hnone : (advance x rows i (run x rows i k) t).pending = none := by
      cases hs : (advance x rows i (run x rows i k) t).pending with
      | none => rfl
      | some v =>
          have hsingleton := (advance_pending_eq_some_iff x rows i
            (run x rows i k) t hpending hpositive v).mp hs
          rw [hempty] at hsingleton
          have hv : v ∈ (∅ : Finset (Fin (M p))) := by
            have hmem : v ∈ ({v} : Finset (Fin (M p))) := by simp
            rw [← hsingleton] at hmem
            exact hmem
          exact False.elim (Finset.notMem_empty v hv)
    have hfalse :
        (BootstrapTruePrefixController.run x i (k + 1)).pending = false := by
      cases h : (BootstrapTruePrefixController.run x i (k + 1)).pending with
      | false => rfl
      | true => exact False.elim (hJ (hpass.mpr h))
    rw [hfalse]
    exact hnone

/-- On a clean block prefix, J's complete candidate state is the accepted
true-row state: counts and rejection bits agree, and pending records J exactly
when the reference pending bit is true. -/
theorem run_eq_true_on_cleanPrefix
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (K k : ℕ)
    (hK : K ≤ p.T) (hk : k ≤ K)
    (hclean : cleanPrefix x rows i J K) :
    (run x rows i k).count J =
        (BootstrapTruePrefixController.run x i k).count ∧
      (run x rows i k).dead J =
        (BootstrapTruePrefixController.run x i k).dead ∧
      (run x rows i k).pending =
        if (BootstrapTruePrefixController.run x i k).pending = true
          then some J else none := by
  induction k generalizing K with
  | zero =>
      simp [run, initialRegisters, BootstrapTruePrefixController.run,
        BootstrapTruePrefixController.initialRegisters]
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have hprevious := ih K hK (by omega) hclean
      have hcleanNext : noFalseCandidatePassPrefix x rows i J (k + 1) :=
        hclean (k + 1) hk
      have hcStep := run_succ x rows i t
      have htStep := BootstrapTruePrefixController.run_succ x i t
      have htval : t.val = k := rfl
      cases htp : (BootstrapTruePrefixController.run x i k).pending with
      | true =>
          have hcp : (run x rows i k).pending = some J := by
            simpa [htp] using hprevious.2.2
          have hfreezeC := advance_eq_of_pending x rows i
            (run x rows i k) t (by simp [hcp])
          have hfreezeT := BootstrapTruePrefixController.advance_eq_of_pending
            x i (BootstrapTruePrefixController.run x i k) t htp
          rw [hcStep, htStep, htval, hfreezeC, hfreezeT]
          exact hprevious
      | false =>
          have hcp : (run x rows i k).pending = none := by
            simpa [htp] using hprevious.2.2
          have hdata := advance_true_count_dead_eq x rows i J hrow
            (run x rows i k) (BootstrapTruePrefixController.run x i k)
            hprevious.1 hprevious.2.1 hcp htp t
          by_cases hpositive : positiveRound x i t
          · have hpend := advance_pending_eq_true_run x rows i J hrow k t
              htval hcp htp hpositive hcleanNext
            have hpend' : (advance x rows i (run x rows i k) t).pending =
                if (BootstrapTruePrefixController.advance x i
                    (BootstrapTruePrefixController.run x i k) t).pending = true
                  then some J else none := by
              rw [← htval, htStep] at hpend
              exact hpend
            rw [hcStep, htStep, htval]
            exact ⟨hdata.1, hdata.2, hpend'⟩
          · have hnotTrue : ¬ BootstrapTruePrefixController.eligible x i t := by
              intro he
              rcases he with ⟨ht, ha, hid, _, hobs⟩
              exact hpositive ⟨ht, ha, hid, hobs⟩
            have hfreezeC := advance_eq_of_not_positive x rows i
              (run x rows i k) t hpositive
            have hfreezeT :=
              BootstrapTruePrefixController.advance_eq_of_not_eligible
                x i (BootstrapTruePrefixController.run x i k) t hnotTrue
            rw [hcStep, htStep, htval, hfreezeC, hfreezeT]
            exact hprevious

/-- The all-candidate decoder never saves a row other than J on a clean
prefix. -/
theorem pending_only_selected_on_cleanPrefix
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J v : Fin (M p))
    (hrow : x.row = rows J) (K k : ℕ) (hK : K ≤ p.T)
    (hk : k ≤ K) (hclean : cleanPrefix x rows i J K)
    (hpending : (run x rows i k).pending = some v) :
    v = J := by
  have hrun := run_eq_true_on_cleanPrefix x rows i J hrow K k hK hk hclean
  rw [hrun.2.2] at hpending
  by_cases htrue : (BootstrapTruePrefixController.run x i k).pending = true
  · have hEq : J = v := by simpa [htrue] using hpending
    exact hEq.symm
  · simp [htrue] at hpending

/-- Candidate v is saved at the first transition from no pending row to v. -/
def candidateSavedAt (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (v : Fin (M p)) (t : Fin p.T) : Bool :=
  decide ((run x rows i t.val).pending = none ∧
    (run x rows i (t.val + 1)).pending = some v)

theorem candidateSavedAt_iff_transition
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (v : Fin (M p)) (t : Fin p.T) :
    candidateSavedAt x rows i v t = true ↔
      (run x rows i t.val).pending = none ∧
        (run x rows i (t.val + 1)).pending = some v := by
  simp [candidateSavedAt]

/-- The first-save transition records exactly a singleton updated passing set;
there is no arbitrary choice when candidates tie. -/
theorem candidateSavedAt_iff_singletonPrefixPassers
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (v : Fin (M p)) (t : Fin p.T)
    (hp : positiveRound x i t) :
    candidateSavedAt x rows i v t = true ↔
      (run x rows i t.val).pending = none ∧
        prefixPassingSet x rows i (t.val + 1) = {v} := by
  rw [candidateSavedAt_iff_transition]
  constructor
  · rintro ⟨hbefore, hafter⟩
    have hafter' :
        (advance x rows i (run x rows i t.val) t).pending = some v := by
      rw [← run_succ x rows i t]
      exact hafter
    have huniq := (advance_pending_eq_some_iff x rows i
      (run x rows i t.val) t hbefore hp v).mp hafter'
    have hset := updateEvidence_passingSet_eq_prefix x rows i t.val t rfl hbefore
    exact ⟨hbefore, hset.symm.trans huniq⟩
  · rintro ⟨hbefore, hset⟩
    have hprefix := updateEvidence_passingSet_eq_prefix x rows i t.val t rfl hbefore
    have huniq : passingSet (updateEvidence x rows i (run x rows i t.val) t) =
        {v} := by rw [hprefix]; exact hset
    have hsave := (advance_pending_eq_some_iff x rows i
      (run x rows i t.val) t hbefore hp v).2 huniq
    have hafter : (run x rows i (t.val + 1)).pending = some v := by
      rw [run_succ x rows i t]
      exact hsave
    exact ⟨hbefore, hafter⟩

/-- The selected row's first-save time is exactly the accepted controller's
first-save time on every clean block prefix. -/
theorem candidateSavedAt_eq_true_savedAt
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (K : ℕ) (hK : K ≤ p.T)
    (hclean : cleanPrefix x rows i J K) (t : Fin p.T)
    (htK : t.val + 1 ≤ K) :
    candidateSavedAt x rows i J t =
      BootstrapTruePrefixController.savedAt x i t := by
  have hbefore := run_eq_true_on_cleanPrefix x rows i J hrow K t.val
    hK (by omega) hclean
  have hafter := run_eq_true_on_cleanPrefix x rows i J hrow K (t.val + 1)
    hK htK hclean
  cases htb : (BootstrapTruePrefixController.run x i t.val).pending with
  | true =>
      have hcb : (run x rows i t.val).pending = some J := by
        simpa [htb] using hbefore.2.2
      simp [candidateSavedAt, BootstrapTruePrefixController.savedAt, hcb, htb]
  | false =>
      have hcb : (run x rows i t.val).pending = none := by
        simpa [htb] using hbefore.2.2
      cases hta : (BootstrapTruePrefixController.run x i (t.val + 1)).pending with
      | false =>
          have hca : (run x rows i (t.val + 1)).pending = none := by
            simpa [hta] using hafter.2.2
          simp [candidateSavedAt, BootstrapTruePrefixController.savedAt,
            hcb, hca, htb, hta]
      | true =>
          have hca : (run x rows i (t.val + 1)).pending = some J := by
            simpa [hta] using hafter.2.2
          simp [candidateSavedAt, BootstrapTruePrefixController.savedAt,
            hcb, hca, htb, hta]

/-- A false candidate cannot have a save time on a clean block prefix. -/
theorem candidateSavedAt_false_of_false_row
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J v : Fin (M p))
    (hrow : x.row = rows J) (K : ℕ) (hK : K ≤ p.T)
    (hclean : cleanPrefix x rows i J K) (hvJ : v ≠ J)
    (t : Fin p.T) (htK : t.val + 1 ≤ K) :
    candidateSavedAt x rows i v t = false := by
  have hsave := (candidateSavedAt_iff_transition x rows i v t)
  by_cases hbefore : (run x rows i t.val).pending = none
  · by_cases hafter : (run x rows i (t.val + 1)).pending = some v
    · have hselected := pending_only_selected_on_cleanPrefix x rows i J v
        hrow K (t.val + 1) hK htK hclean hafter
      exact False.elim (hvJ hselected)
    · have hnotSave : ¬ candidateSavedAt x rows i v t = true := by
        intro hs
        exact hafter ((hsave.mp hs).2)
      cases h : candidateSavedAt x rows i v t with
      | false => rfl
      | true => exact False.elim (hnotSave h)
  · have hnotSave : ¬ candidateSavedAt x rows i v t = true := by
      intro hs
      exact hbefore ((hsave.mp hs).1)
    cases h : candidateSavedAt x rows i v t with
    | false => rfl
    | true => exact False.elim (hnotSave h)

/-- The all-candidate output reuses the physical block trace and puts its
selected-row save event only in the existing boundary declaration field. -/
def candidateObservationTrace (x : BootstrapPhysicalBlock.Input p s)
    (rows : CompleteRows p) (i : {i // i ∈ x.uninformed})
    (J : Fin (M p)) : BootstrapBlockConstruction.ExplicitTrace p :=
  BootstrapPhysicalBlock.observationTrace x i (candidateSavedAt x rows i J) false

/-- Under the clean event through the block end, the all-candidate boundary
declaration agrees with the accepted true-prefix boundary declaration. -/
theorem candidate_boundaryDeclaration_eq_true
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p))
    (hrow : x.row = rows J) (hclean : cleanPrefix x rows i J p.T) :
    (candidateObservationTrace x rows i J).savedDeclaration s =
      (BootstrapTruePrefixController.observationTrace x i false).savedDeclaration s := by
  have hsave (t : Fin p.T) : candidateSavedAt x rows i J t =
      BootstrapTruePrefixController.savedAt x i t :=
    candidateSavedAt_eq_true_savedAt x rows i J hrow p.T le_rfl hclean t (by omega)
  have hdecl :
      (candidateObservationTrace x rows i J).savedDeclaration s = true ↔
        (BootstrapTruePrefixController.observationTrace x i false).savedDeclaration s = true := by
    rw [candidateObservationTrace,
      BootstrapPhysicalBlock.observationTrace_savedDeclaration,
      BootstrapTruePrefixController.observationTrace_savedDeclaration]
    constructor
    · rintro ⟨t, ht, hs⟩
      exact ⟨t, ht, by rw [hsave t] at hs; exact hs⟩
    · rintro ⟨t, ht, hs⟩
      exact ⟨t, ht, by rw [← hsave t] at hs; exact hs⟩
  cases hc : (candidateObservationTrace x rows i J).savedDeclaration s <;>
    cases hr : (BootstrapTruePrefixController.observationTrace x i false).savedDeclaration s <;>
    simp_all

/-- The all-candidate output retains the physical all-slot gain: the decoder
declaration changes no action or reward coordinate inside this block. -/
theorem candidateObservationTrace_gain_eq_physicalStayGain
    (x : BootstrapPhysicalBlock.Input p s) (rows : CompleteRows p)
    (i : {i // i ∈ x.uninformed}) (J : Fin (M p)) :
    BootstrapBlockConstruction.effectiveCalendarBlockGain
        (candidateObservationTrace x rows i J) s =
      BootstrapPhysicalBlock.physicalStayGain x i := by
  exact BootstrapPhysicalBlock.effectiveCalendarBlockGain_eq_physicalStayGain
    x i (candidateSavedAt x rows i J) false

end Bandits.Support.BootstrapAllCandidateController

end
