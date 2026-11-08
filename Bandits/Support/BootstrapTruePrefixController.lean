/-
Copyright (c) 2026 Bandits Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.BootstrapPhysicalBlock

/-!
# True-only bootstrap candidate controller

This module constructs the single true-row candidate register recursion for
one physical bootstrap block from the actual observations in
`BootstrapPhysicalBlock`. Candidate registers are computed after the round's
physical feedback and never enter the physical action or gain recursion.
The unique-candidate property is automatic here because only the true-row
branch is constructed.

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-109,129-140` and
`sources/zip4/manuscript/appendix_b_communication.tex:109-126,138-165`.

The module constructs one block's candidate output from an existing physical
input. It does not construct an initialization history, physical boundary
histories, activation, launch, or any probability of success.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.BootstrapTruePrefixController

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapBlockConstruction
open Bandits.Support.BootstrapPhysicalBlock
open Bandits.Support.FiniteBanditModel
open Bandits.Support.ActiveRoundActions
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.RealRewardGridCount

variable {p : Parameters} {s : Fin (n_boot p)}

/-- The one follower's controller registers before processing a round. -/
structure Registers where
  count : ℕ
  dead : Bool
  pending : Bool
  deriving DecidableEq, Repr

/-- The block-start reset required by the follower decoder. -/
def initialRegisters : Registers := ⟨0, false, false⟩

/-- The true candidate's forward bit at this round. -/
def trueForwardBit (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) : Bool :=
  x.row.1 (x.privateId i) t

/-- A round is tested after its actual physical feedback exactly when it is in
this calendar block, the follower is active, its private ID bit is zero, its
true-row slot is DATA, and its actual physical observation is positive. -/
def eligible (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) : Prop :=
  t ∈ calendarBlock p s ∧ x.active i = true ∧
    x.ids (x.privateId i) t = false ∧ BootstrapPhysicalBlock.slot x t = dataSlot ∧
    0 < (BootstrapPhysicalBlock.observationIndex x
      (BootstrapPhysicalBlock.run x t.val) t
      (followerPlayer p.two_le_m i.val)).val

/-- Boolean form of the eligible event, with classical decisions confined to
this derived test. -/
def eligibleFlag (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) : Bool := by
  classical
  exact decide (eligible x i t)

theorem eligibleFlag_eq_true_iff (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    eligibleFlag x i t = true ↔ eligible x i t := by
  simp [eligibleFlag]

/-- The eligible positive calendar rounds strictly before prefix `k`. -/
def eligiblePrefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) : Finset (Fin p.T) :=
  (by
    classical
    exact (calendarBlock p s).filter fun t => t.val < k ∧ eligible x i t)

/-- Whether an eligible positive with a zero true forward bit has occurred in
the prefix. -/
def hasMismatchPrefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) : Prop :=
  ∃ t, t ∈ eligiblePrefix x i k ∧ trueForwardBit x i t = false

/-- All eligible positives through prefix `k` have their true forward bit set. -/
def allTruePrefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) : Prop :=
  ∀ t, t ∈ eligiblePrefix x i k → trueForwardBit x i t = true

/-- The true candidate passes at eligible round `t` after including that
round's actual observation. -/
def passesAt (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) : Prop :=
  eligible x i t ∧ q_dec p ≤ (eligiblePrefix x i (t.val + 1)).card ∧
    allTruePrefix x i (t.val + 1)

/-- Some eligible prefix ending strictly before `k` has reached quota with all
of its true forward bits equal to one. -/
def hasPassingPrefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) : Prop :=
  ∃ t, t.val < k ∧ passesAt x i t

/-- Process one post-feedback candidate update. Pending freezes these registers;
it is not consulted by the physical action or gain definitions. -/
def advance (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (r : Registers) (t : Fin p.T) : Registers :=
  by
    classical
    exact if eligibleFlag x i t = true then
      if r.pending = false then
        let dead' := r.dead || decide (trueForwardBit x i t = false)
        let count' := r.count + 1
        ⟨count', dead', decide (q_dec p ≤ count' ∧ dead' = false)⟩
      else r
    else r

theorem advance_eq_of_not_eligible (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (r : Registers) (t : Fin p.T)
    (h : ¬ eligible x i t) : advance x i r t = r := by
  have hflag : eligibleFlag x i t = false := by simp [eligibleFlag, h]
  simp [advance, hflag]

theorem advance_eq_of_pending (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (r : Registers) (t : Fin p.T)
    (hpending : r.pending = true) : advance x i r t = r := by
  simp [advance, hpending]

theorem advance_eq_of_outside_block (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (r : Registers) (t : Fin p.T)
    (ht : t ∉ calendarBlock p s) : advance x i r t = r := by
  apply advance_eq_of_not_eligible
  intro he
  exact ht he.1

theorem advance_eq_of_inactive (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (r : Registers) (t : Fin p.T)
    (ha : x.active i = false) : advance x i r t = r := by
  apply advance_eq_of_not_eligible
  intro he
  rcases he with ⟨_, hactive, _, _, _⟩
  rw [ha] at hactive
  cases hactive

/-- Candidate registers after processing the first `k` calendar rounds. -/
def run (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) : ℕ → Registers
  | 0 => initialRegisters
  | k + 1 => if hk : k < p.T then
      advance x i (run x i k) ⟨k, hk⟩ else run x i k

theorem run_zero (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) : run x i 0 = initialRegisters := rfl

theorem no_pending_at_prefix_zero (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) : (run x i 0).pending = false := rfl

theorem run_succ (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    run x i (t.val + 1) = advance x i (run x i t.val) t := by
  simp only [run, t.isLt, ↓reduceDIte]

theorem mem_eligiblePrefix_iff (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (t : Fin p.T) :
    t ∈ eligiblePrefix x i k ↔ t ∈ calendarBlock p s ∧ t.val < k ∧ eligible x i t := by
  simp only [eligiblePrefix, Finset.mem_filter]

theorem eligiblePrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    eligiblePrefix x i (t.val + 1) =
      if eligibleFlag x i t = true then insert t (eligiblePrefix x i t.val)
      else eligiblePrefix x i t.val := by
  classical
  ext r
  by_cases he : eligible x i t
  · have hflag : eligibleFlag x i t = true :=
      (eligibleFlag_eq_true_iff x i t).mpr he
    simp only [eligiblePrefix, Finset.mem_filter, hflag, ↓reduceIte,
      Finset.mem_insert]
    by_cases hrt : r = t
    · subst r
      constructor
      · intro _
        exact Or.inl rfl
      · intro _
        exact ⟨he.1, by omega, he⟩
    · constructor
      · rintro ⟨hmem, hlt, hrEligible⟩
        right
        refine ⟨hmem, ?_, hrEligible⟩
        have hval : r.val ≠ t.val := by
          intro h
          exact hrt (Fin.ext h)
        omega
      · rintro (heq | ⟨hmem, hlt, hrEligible⟩)
        · exact False.elim (hrt heq)
        · exact ⟨hmem, by omega, hrEligible⟩
  · have hflag : eligibleFlag x i t = false := by
      simp [eligibleFlag, he]
    simp only [eligiblePrefix, Finset.mem_filter, hflag, Bool.false_eq_true,
      ↓reduceIte]
    constructor
    · rintro ⟨hmem, hlt, hrEligible⟩
      by_cases hrt : r = t
      · subst r
        exact False.elim (he hrEligible)
      · refine ⟨hmem, ?_, hrEligible⟩
        have hval : r.val ≠ t.val := by
          intro h
          exact hrt (Fin.ext h)
        omega
    · rintro ⟨hmem, hlt, hrEligible⟩
      exact ⟨hmem, by omega, hrEligible⟩

theorem eligiblePrefix_card_succ (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) (he : eligible x i t) :
    (eligiblePrefix x i (t.val + 1)).card =
      (eligiblePrefix x i t.val).card + 1 := by
  have hflag : eligibleFlag x i t = true :=
    (eligibleFlag_eq_true_iff x i t).mpr he
  rw [eligiblePrefix_succ]
  simp only [hflag, ↓reduceIte]
  have hnot : t ∉ eligiblePrefix x i t.val := by
    rw [mem_eligiblePrefix_iff]
    simp
  exact Finset.card_insert_of_notMem hnot

theorem allTruePrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    allTruePrefix x i (t.val + 1) ↔
      allTruePrefix x i t.val ∧ (eligible x i t → trueForwardBit x i t = true) := by
  unfold allTruePrefix
  rw [eligiblePrefix_succ]
  by_cases he : eligible x i t
  · have hflag : eligibleFlag x i t = true :=
      (eligibleFlag_eq_true_iff x i t).mpr he
    simp only [hflag, ↓reduceIte, Finset.forall_mem_insert]
    constructor
    · rintro ⟨ht, hall⟩
      exact ⟨hall, fun _ => ht⟩
    · rintro ⟨hall, ht⟩
      exact ⟨ht he, hall⟩
  · have hflag : eligibleFlag x i t = false := by simp [eligibleFlag, he]
    simp only [hflag, Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro hall
      exact ⟨hall, fun he' => False.elim (he he')⟩
    · intro h
      exact h.1

theorem hasMismatchPrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    hasMismatchPrefix x i (t.val + 1) ↔
      hasMismatchPrefix x i t.val ∨
        (eligible x i t ∧ trueForwardBit x i t = false) := by
  unfold hasMismatchPrefix
  rw [eligiblePrefix_succ]
  by_cases he : eligible x i t
  · have hflag : eligibleFlag x i t = true :=
      (eligibleFlag_eq_true_iff x i t).mpr he
    simp only [hflag, ↓reduceIte, Finset.exists_mem_insert]
    simp only [he, true_and]
    exact or_comm
  · have hflag : eligibleFlag x i t = false := by simp [eligibleFlag, he]
    simp only [hflag, Bool.false_eq_true, ↓reduceIte]
    simp [he]

theorem hasMismatchPrefix_mono (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) {k l : ℕ} (hkl : k ≤ l)
    (hm : hasMismatchPrefix x i k) : hasMismatchPrefix x i l := by
  rcases hm with ⟨t, ht, hbit⟩
  have ht' : t ∈ eligiblePrefix x i l := by
    rw [mem_eligiblePrefix_iff] at ht ⊢
    exact ⟨ht.1, Nat.lt_of_lt_of_le ht.2.1 hkl, ht.2.2⟩
  exact ⟨t, ht', hbit⟩

theorem allTruePrefix_iff_noMismatch (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) :
    allTruePrefix x i k ↔ ¬ hasMismatchPrefix x i k := by
  constructor
  · intro hall ⟨t, ht, hbit⟩
    rw [hall t ht] at hbit
    cases hbit
  · intro hnone t ht
    cases hbit : trueForwardBit x i t with
    | false => exact False.elim (hnone ⟨t, ht, hbit⟩)
    | true => simp

theorem hasPassingPrefix_succ (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    hasPassingPrefix x i (t.val + 1) ↔
      hasPassingPrefix x i t.val ∨ passesAt x i t := by
  constructor
  · rintro ⟨r, hr, hp⟩
    by_cases heq : r.val = t.val
    · have hrt : r = t := Fin.ext heq
      subst r
      exact Or.inr hp
    · exact Or.inl ⟨r, by omega, hp⟩
  · rintro (⟨r, hr, hp⟩ | hp)
    · exact ⟨r, by omega, hp⟩
    · exact ⟨t, by omega, hp⟩

theorem count_dead_before_save (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (hk : k ≤ p.T)
    (hpending : (run x i k).pending = false) :
    (run x i k).count = (eligiblePrefix x i k).card ∧
      ((run x i k).dead = true ↔ hasMismatchPrefix x i k) := by
  induction k with
  | zero =>
      simp [run, initialRegisters, eligiblePrefix, hasMismatchPrefix]
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have hstep := run_succ x i t
      rw [hstep] at hpending ⊢
      have htval : t.val = k := rfl
      rw [htval] at hpending ⊢
      by_cases he : eligible x i t
      · by_cases hold : (run x i k).pending = false
        · have hprev := ih (by omega) hold
          simp only [advance, eligibleFlag, he, hold, ↓reduceIte] at hpending ⊢
          have hcard := eligiblePrefix_card_succ x i t he
          rw [htval] at hcard
          constructor
          · change (run x i k).count + 1 =
              (eligiblePrefix x i (k + 1)).card
            rw [hcard, hprev.1]
          · change ((run x i k).dead ||
                decide (trueForwardBit x i t = false)) = true ↔
              hasMismatchPrefix x i (k + 1)
            have hmismatch := hasMismatchPrefix_succ x i t
            rw [htval] at hmismatch
            rw [Bool.or_eq_true, decide_eq_true_eq, hmismatch]
            simp only [he, true_and]
            exact or_congr hprev.2 Iff.rfl
        · simp [advance, eligibleFlag, he, hold] at hpending
      · have hprev := ih (by omega) (by
          simpa [advance, eligibleFlag, he] using hpending)
        have hflag : eligibleFlag x i t = false := by simp [eligibleFlag, he]
        have hprefix : eligiblePrefix x i (k + 1) =
            eligiblePrefix x i k := by
          have hs := eligiblePrefix_succ x i t
          rw [htval] at hs
          rw [hs]
          simp only [hflag, Bool.false_eq_true, ↓reduceIte]
        have hmismatch : hasMismatchPrefix x i (k + 1) ↔
            hasMismatchPrefix x i k := by
          have hs := hasMismatchPrefix_succ x i t
          rw [htval] at hs
          rw [hs]
          simp [he]
        simpa [advance, eligibleFlag, he, hprefix, hmismatch] using hprev

theorem pending_iff_passingPrefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (hk : k ≤ p.T) :
    (run x i k).pending = true ↔ hasPassingPrefix x i k := by
  induction k with
  | zero =>
      simp [run, initialRegisters, hasPassingPrefix]
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have hstep := run_succ x i t
      rw [hstep]
      have htval : t.val = k := rfl
      rw [htval]
      have hpassSucc := hasPassingPrefix_succ x i t
      rw [htval] at hpassSucc
      rw [hpassSucc]
      by_cases hp : (run x i k).pending = true
      · have hprev := (ih (by omega)).mp hp
        constructor
        · intro _
          exact Or.inl hprev
        · intro _
          simp [advance, hp]
      · have hpfalse : (run x i k).pending = false := by
          cases h : (run x i k).pending <;> simp_all
        have hprevPass : ¬ hasPassingPrefix x i k := by
          simpa [ih (by omega)] using hp
        have hinv := count_dead_before_save x i k (by omega) hpfalse
        by_cases he : eligible x i t
        · have hsave := eligiblePrefix_card_succ x i t he
          have hdeadFalse : (run x i k).dead = false ↔
              ¬ hasMismatchPrefix x i k := by
            cases hd : (run x i k).dead with
            | false =>
                constructor
                · intro _ hmis
                  have htrue := hinv.2.mpr hmis
                  rw [hd] at htrue
                  cases htrue
                · intro _
                  rfl
            | true =>
                constructor
                · intro hfalse
                  cases hfalse
                · intro hnone
                  exact False.elim (hnone (hinv.2.mp hd))
          have hallPrefix : allTruePrefix x i (k + 1) ↔
              ¬ hasMismatchPrefix x i k ∧ trueForwardBit x i t = true := by
            have hall := allTruePrefix_succ x i t
            rw [htval] at hall
            rw [hall]
            simp [he, allTruePrefix_iff_noMismatch]
          have hsaveCondition :
              (q_dec p ≤ (run x i k).count + 1 ∧
                (run x i k).dead = false ∧ trueForwardBit x i t = true) ↔
              passesAt x i t := by
            rw [passesAt]
            have hcard : (eligiblePrefix x i (k + 1)).card =
                (eligiblePrefix x i k).card + 1 := by
              simpa [htval] using hsave
            rw [hcard, hinv.1, hallPrefix]
            simp [he, hdeadFalse]
          simp [advance, eligibleFlag, he, hpfalse, hsaveCondition, hprevPass]
        · simp [advance, eligibleFlag, he, hpfalse, hprevPass, passesAt]

theorem no_passingPrefix_after_mismatch (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) {k l : ℕ}
    (hno : ¬ hasPassingPrefix x i k) (hm : hasMismatchPrefix x i k) :
    ¬ hasPassingPrefix x i l := by
  rintro ⟨t, ht, hpasses⟩
  by_cases htk : t.val < k
  · exact hno ⟨t, htk, hpasses⟩
  · have hkle : k ≤ t.val := by omega
    have hm' : hasMismatchPrefix x i (t.val + 1) :=
      hasMismatchPrefix_mono x i (Nat.le_trans hkle (Nat.le_succ _)) hm
    exact (allTruePrefix_iff_noMismatch x i (t.val + 1)).mp hpasses.2.2 hm'

theorem permanent_rejection (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ p.T)
    (hdead : (run x i k).dead = true)
    (hpending : (run x i k).pending = false) :
    (run x i l).dead = true ∧ (run x i l).pending = false := by
  have hinv := count_dead_before_save x i k (by omega) hpending
  have hm : hasMismatchPrefix x i k := hinv.2.mp hdead
  have hno : ¬ hasPassingPrefix x i k := by
    intro hp
    have : (run x i k).pending = true :=
      (pending_iff_passingPrefix x i k (by omega)).mpr hp
    simp [hpending] at this
  have hnoL := no_passingPrefix_after_mismatch x i (k := k) (l := l) hno hm
  have hpendingL : (run x i l).pending = false := by
    cases h : (run x i l).pending with
    | false => rfl
    | true => exact False.elim (hnoL ((pending_iff_passingPrefix x i l hl).mp h))
  have hmL := hasMismatchPrefix_mono x i hkl hm
  have hinvL := count_dead_before_save x i l hl hpendingL
  exact ⟨hinvL.2.mpr hmL, hpendingL⟩

theorem pending_monotone (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) {k l : ℕ}
    (hk : k ≤ l) (hl : l ≤ p.T) (hp : (run x i k).pending = true) :
    (run x i l).pending = true := by
  have hpass := (pending_iff_passingPrefix x i k (by omega)).mp hp
  have hpassl : hasPassingPrefix x i l := by
    rcases hpass with ⟨t, ht, hpasses⟩
    exact ⟨t, Nat.lt_of_lt_of_le ht hk, hpasses⟩
  exact (pending_iff_passingPrefix x i l hl).mpr hpassl

theorem count_le_prefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (hk : k ≤ p.T) :
    (run x i k).count ≤ (eligiblePrefix x i k).card := by
  induction k with
  | zero => simp [run, initialRegisters, eligiblePrefix]
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have hstep := run_succ x i t
      rw [hstep]
      have htval : t.val = k := rfl
      rw [htval]
      by_cases he : eligible x i t
      · have hflag : eligibleFlag x i t = true :=
          (eligibleFlag_eq_true_iff x i t).mpr he
        have hcard := eligiblePrefix_card_succ x i t he
        rw [htval] at hcard
        by_cases hp : (run x i k).pending = false
        · simp only [advance, hflag, hp, ↓reduceIte]
          change (run x i k).count + 1 ≤
            (eligiblePrefix x i (k + 1)).card
          rw [hcard]
          have hprev := ih (by omega)
          omega
        · simp only [advance, hflag, hp, ↓reduceIte]
          change (run x i k).count ≤ (eligiblePrefix x i (k + 1)).card
          rw [hcard]
          have hprev := ih (by omega)
          omega
      · have hflag : eligibleFlag x i t = false := by simp [eligibleFlag, he]
        have hprefix : eligiblePrefix x i (k + 1) =
          eligiblePrefix x i k := by
          have hs := eligiblePrefix_succ x i t
          rw [htval] at hs
          rw [hs]
          simp only [hflag, Bool.false_eq_true, ↓reduceIte]
        simp only [advance, hflag, Bool.false_eq_true, ↓reduceIte, hprefix]
        exact ih (by omega)

theorem count_le_B_boot (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (hk : k ≤ p.T) :
    (run x i k).count ≤ B_boot p := by
  classical
  calc
    (run x i k).count ≤ (eligiblePrefix x i k).card := count_le_prefix x i k hk
    _ ≤ (calendarBlock p s).card := by
      change ((calendarBlock p s).filter
        (fun t => t.val < k ∧ eligible x i t)).card ≤ _
      exact Finset.card_filter_le _ _
    _ ≤ B_boot p := calendarBlock_card_le_B_boot p s

/-- The declaration is saved at exactly the first prefix transition from no
pending declaration to pending. There is no time-zero save branch. -/
def savedAt (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) : Bool :=
  decide ((run x i t.val).pending = false ∧
    (run x i (t.val + 1)).pending = true)

theorem savedAt_iff_transition (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    savedAt x i t = true ↔
      (run x i t.val).pending = false ∧
        (run x i (t.val + 1)).pending = true := by
  simp [savedAt]

theorem savedAt_iff_firstPassingPrefix (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (t : Fin p.T) :
    savedAt x i t = true ↔
      ¬ hasPassingPrefix x i t.val ∧ passesAt x i t := by
  rw [savedAt_iff_transition]
  have hfalse (b : Bool) : b = false ↔ ¬ b = true := by
    cases b <;> simp
  rw [hfalse, pending_iff_passingPrefix x i t.val (Nat.le_of_lt t.isLt),
    pending_iff_passingPrefix x i (t.val + 1) (by omega), hasPassingPrefix_succ]
  constructor
  · rintro ⟨hno, hpass | hpass⟩
    · exact False.elim (hno hpass)
    · exact ⟨hno, hpass⟩
  · rintro ⟨hno, hpass⟩
    exact ⟨hno, Or.inr hpass⟩

theorem savedAt_unique (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) {t u : Fin p.T}
    (ht : savedAt x i t = true) (hu : savedAt x i u = true) : t = u := by
  have htt := (savedAt_iff_transition x i t).mp ht
  have huu := (savedAt_iff_transition x i u).mp hu
  by_contra hne
  rcases lt_or_gt_of_ne hne with htu | hut
  · have htuval : t.val < u.val := Fin.lt_def.mp htu
    have hmono := pending_monotone x i (Nat.succ_le_of_lt htuval)
      (Nat.le_of_lt u.isLt) htt.2
    rw [huu.1] at hmono
    cases hmono
  · have hutval : u.val < t.val := Fin.lt_def.mp hut
    have hmono := pending_monotone x i (Nat.succ_le_of_lt hutval)
      (Nat.le_of_lt t.isLt) huu.2
    rw [htt.1] at hmono
    cases hmono

theorem exists_savedAt_of_pending (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (k : ℕ) (hk : k ≤ p.T)
    (hpending : (run x i k).pending = true) :
    ∃ t, t.val < k ∧ savedAt x i t = true := by
  induction k with
  | zero => simp [run, initialRegisters] at hpending
  | succ k ih =>
      have hkt : k < p.T := by omega
      let t : Fin p.T := ⟨k, hkt⟩
      have htval : t.val = k := rfl
      by_cases hold : (run x i k).pending = true
      · obtain ⟨u, hu, hsave⟩ := ih (by omega) hold
        exact ⟨u, by omega, hsave⟩
      · have hfalse : (run x i k).pending = false := by
          cases h : (run x i k).pending <;> simp_all
        have hafter : (run x i (t.val + 1)).pending = true := by
          simpa [htval] using hpending
        have hsave : savedAt x i t = true :=
          (savedAt_iff_transition x i t).mpr ⟨hfalse, hafter⟩
        exact ⟨t, by omega, hsave⟩

/-- The output trace uses the controller-computed save bit; its only declaration
effect is the existing physical block's saved-declaration boundary flag. -/
def observationTrace (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (launchAtBoundary : Bool) :
    ExplicitTrace p :=
  BootstrapPhysicalBlock.observationTrace x i (savedAt x i) launchAtBoundary

theorem observationTrace_savedDeclaration (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (launchAtBoundary : Bool) :
    (observationTrace x i launchAtBoundary).savedDeclaration s = true ↔
      ∃ t ∈ calendarBlock p s, savedAt x i t = true := by
  exact BootstrapPhysicalBlock.observationTrace_savedDeclaration x i
    (savedAt x i) launchAtBoundary

theorem observationTrace_value (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (launchAtBoundary : Bool) (t : Fin p.T)
    (ht : t ∈ calendarBlock p s) :
    realRewardGridValue (D p) (D_pos p)
        ((observationTrace x i launchAtBoundary).observation t) =
      BootstrapPhysicalBlock.feedback x (BootstrapPhysicalBlock.run x t.val)
        t (followerPlayer p.two_le_m i.val) := by
  exact BootstrapPhysicalBlock.observationTrace_value x i (savedAt x i)
    launchAtBoundary t ht

theorem savedDeclaration_iff_pendingAtEnd (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) :
    (observationTrace x i false).savedDeclaration s = true ↔
      (run x i p.T).pending = true := by
  rw [observationTrace_savedDeclaration]
  constructor
  · rintro ⟨t, ht, hsave⟩
    have htransition := (savedAt_iff_transition x i t).mp hsave
    exact pending_monotone x i (Nat.succ_le_of_lt t.isLt) le_rfl htransition.2
  · intro hp
    obtain ⟨t, _, hsave⟩ := exists_savedAt_of_pending x i p.T le_rfl hp
    have heligible := (savedAt_iff_firstPassingPrefix x i t).mp hsave |>.2.1
    exact ⟨t, heligible.1, hsave⟩

/-- The candidate controller feeds the full physical all-slot gain to the
existing block updater, including observations after saving and non-DATA slots. -/
theorem observationTrace_gain_eq_physicalStayGain
    (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (launchAtBoundary : Bool) :
    BootstrapBlockConstruction.effectiveCalendarBlockGain
        (observationTrace x i launchAtBoundary) s =
      BootstrapPhysicalBlock.physicalStayGain x i := by
  exact BootstrapPhysicalBlock.effectiveCalendarBlockGain_eq_physicalStayGain
    x i (savedAt x i) launchAtBoundary

theorem effectiveGain_independent_of_candidate_output
    (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (saved₁ saved₂ : Fin p.T → Bool)
    (launch₁ launch₂ : Bool) :
    BootstrapBlockConstruction.effectiveCalendarBlockGain
        (BootstrapPhysicalBlock.observationTrace x i saved₁ launch₁) s =
      BootstrapBlockConstruction.effectiveCalendarBlockGain
        (BootstrapPhysicalBlock.observationTrace x i saved₂ launch₂) s := by
  exact BootstrapPhysicalBlock.gain_independent_of_saved_declaration
    x i saved₁ saved₂ launch₁ launch₂

/-- Changing the candidate's saved-at output cannot alter the physical
observation supplied by the already constructed physical block. -/
theorem physicalObservation_independent_of_savedAt
    (x : BootstrapPhysicalBlock.Input p s)
    (i : {i // i ∈ x.uninformed}) (saved₁ saved₂ : Fin p.T → Bool)
    (launch₁ launch₂ : Bool) (t : Fin p.T) (ht : t ∈ calendarBlock p s) :
    realRewardGridValue (D p) (D_pos p)
        ((BootstrapPhysicalBlock.observationTrace x i saved₁ launch₁).observation t) =
      realRewardGridValue (D p) (D_pos p)
        ((BootstrapPhysicalBlock.observationTrace x i saved₂ launch₂).observation t) := by
  rw [BootstrapPhysicalBlock.observationTrace_value x i saved₁ launch₁ t ht,
    BootstrapPhysicalBlock.observationTrace_value x i saved₂ launch₂ t ht]

end Bandits.Support.BootstrapTruePrefixController

end
