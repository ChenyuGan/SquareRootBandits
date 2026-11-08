/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownActiveBridge
public import Bandits.Support.ReferenceGeneratedPrelaunchDownInactiveBridge
public import Bandits.Support.ReferenceGeneratedPrelaunchDownCohortStep
public import Bandits.Support.ReferenceGeneratedPrelaunchDownBirthBounds

import Lean.Elab.Tactic.Omega

/-!
# Operational data for generated prelaunch DOWN births

The birth predicate remains the literal projection in
`ReferenceGeneratedPrelaunchDownPrefix`.  This producer derives the actual
predecessor operation for a birth: either a generated block's saved/forced
activation or an active quota-clearing step. It proves the operational iff
and unique historical origin of each actual current bank by per-round induction.
These are internal results. The same-birth launch/flag join remains separate.

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-142`,
and `05_binary_transport.tex:20-42`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownHistoricalBirth

open ConstructorDimensions BootstrapDimensions
open ReferenceInitializationRun ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix ReferenceGeneratedPrelaunchDownCohort
open ReferenceGeneratedPrelaunchDownActiveBridge
open ReferenceGeneratedPrelaunchDownInactiveBridge
open ReferenceGeneratedPrelaunchDownCohortStep
open ReferenceGeneratedPrelaunchDownBirthBounds
open ReferenceGeneratedDownBatchCalendar
open AffineBatchDecoder AffineChannelLaw
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

private theorem bankBirth_after_clear (a : Activation p)
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)) :
    bankBirth a ⟨[], bank.completed ++ [bank.pending ++ [entry]]⟩ =
      some (entry.time.val + 1) := by
  simp [bankBirth]

private theorem last_round_block (r : Fin p.T) (hLast : r.val + 1 = p.T) :
    ReferenceInitializationRun.elapsed p ((roundBlockIndex p r).val + 1) = p.T ∧
      (roundBlockIndex p r).val + 1 = n_boot p := by
  let s := roundBlockIndex p r
  have hmem := (mem_calendarBlock_iff p s r).mp (round_mem_quotient_block p r)
  have hEnd : ReferenceInitializationRun.elapsed p (s.val + 1) = p.T := by
    change min p.T ((s.val + 1) * B_boot p) = p.T
    omega
  refine ⟨hEnd, ?_⟩
  have hs := s.isLt
  by_contra hnot
  have hnext : s.val + 1 < n_boot p := by omega
  obtain ⟨t, ht⟩ := calendarBlock_nonempty p ⟨s.val + 1, hnext⟩
  have ht' := (mem_calendarBlock_iff p ⟨s.val + 1, hnext⟩ t).mp ht
  change s.val * B_boot p ≤ r.val ∧
    r.val < min p.T ((s.val + 1) * B_boot p) at hmem
  change min p.T ((s.val + 1) * B_boot p) = p.T at hEnd
  rw [hEnd] at hmem
  change (s.val + 1) * B_boot p ≤ t.val ∧
    t.val < min p.T ((s.val + 2) * B_boot p) at ht'
  have hT := t.isLt
  omega

private theorem birthAt_prefix_view
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T)
    (hBeforeEnd : alpha < p.T) (k : ℕ) :
    birthAt rate rewards C_star C_h z i alpha hAlpha k =
      match source_prelaunch_down_prefix rate rewards C_star C_h z i
          ⟨alpha, hBeforeEnd⟩ with
      | .inl (.inl active) =>
          active.val.2.2.2.downBatch.completed.length = k ∧
            active.val.2.2.2.downBatch.pending = [] ∧
            bankBirth active.val.2.1 active.val.2.2.2.downBatch = some alpha
      | .inl (.inr _) => False
      | .inr stopped =>
          ∃ a, stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i) =
                some a ∧
            stopped.val.2.downBatch.completed.length = k ∧
            stopped.val.2.downBatch.pending = [] ∧
            bankBirth a stopped.val.2.downBatch = some alpha := by
  unfold birthAt
  rw [dite_eq_left hBeforeEnd]
  rfl

private theorem birthAt_terminal_view
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (hAlpha : p.T ≤ p.T) (k : ℕ) :
    birthAt rate rewards C_star C_h z i p.T hAlpha k =
      ∃ a,
        (ReferenceInitializationRun.output (sourceReferenceInput rate rewards C_star C_h z)).activation
            (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        (ReferenceInitializationRun.ordinary (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length = k ∧
        (ReferenceInitializationRun.ordinary (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending = [] ∧
        bankBirth a (ReferenceInitializationRun.ordinary (sourceReferenceInput rate rewards C_star C_h z)
          (ReferenceInitializationRun.output (sourceReferenceInput rate rewards C_star C_h z))
          (ActualReferenceInitializationBlock.refFollower i)).downBatch = some p.T := by
  rw [birthAt, dite_eq_right (Nat.lt_irrefl p.T)]

/-- Literal activation/state projection of the existing actual prefix (or
terminal output at `T`). This introduces no execution or history data. -/
private def currentCohort
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (_hn : n ≤ p.T) :
    Option (Activation p × ReferencePrelaunchFollower.State p rate.eta) :=
  if h : n < p.T then
    match source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨n, h⟩ with
    | .inl (.inl active) => some (active.val.2.1, active.val.2.2.2)
    | .inl (.inr _) => none
    | .inr stopped => (stopped.val.1.activation
        (ActualReferenceInitializationBlock.refFollower i)).map (fun a => (a, stopped.val.2))
  else
    let terminal := source_prelaunch_down_terminal rate rewards C_star C_h z i
    (terminal.1.activation (ActualReferenceInitializationBlock.refFollower i)).map
      (fun a => (a, terminal.2))

private theorem exists_cohort_eq {eta : ReferencePrelaunchFollower.LearningRate}
    (a : Activation p) (state : ReferencePrelaunchFollower.State p eta)
    (P : Activation p → ReferencePrelaunchFollower.State p eta → Prop) :
    (∃ a' state', (a, state) = (a', state') ∧ P a' state') ↔ P a state := by
  constructor
  · rintro ⟨a', state', heq, hP⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    exact hP
  · intro hP
    exact ⟨a, state, rfl, hP⟩

private theorem birthAt_currentCohort
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T) (k : ℕ) :
    birthAt rate rewards C_star C_h z i n hn k ↔
      ∃ a state, currentCohort rate rewards C_star C_h z i n hn = some (a, state) ∧
        state.downBatch.completed.length = k ∧ state.downBatch.pending = [] ∧
        bankBirth a state.downBatch = some n := by
  classical
  by_cases h : n < p.T
  · rw [birthAt_prefix_view rate rewards C_star C_h z i n hn h k]
    unfold currentCohort
    rw [dite_eq_left h]
    cases source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨n, h⟩ with
    | inl branch =>
        cases branch with
        | inl active =>
            dsimp only
            simp only [Option.some.injEq]
            exact (exists_cohort_eq active.val.2.1 active.val.2.2.2 (fun a state =>
              state.downBatch.completed.length = k ∧ state.downBatch.pending = [] ∧
                bankBirth a state.downBatch = some n)).symm
        | inr inactive => simp
    | inr stopped =>
        cases ha : stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i) with
        | none => simp only [ha, Option.map_none, reduceCtorEq, false_and, exists_false]
        | some a =>
            simp only [ha, Option.map_some, Option.some.injEq, exists_eq_left']
            exact (exists_cohort_eq a stopped.val.2 (fun a state =>
              state.downBatch.completed.length = k ∧ state.downBatch.pending = [] ∧
                bankBirth a state.downBatch = some n)).symm
  · have hT : n = p.T := by omega
    subst n
    rw [birthAt_terminal_view rate rewards C_star C_h z i hn k]
    unfold currentCohort
    rw [dite_eq_right (Nat.lt_irrefl p.T)]
    dsimp only [source_prelaunch_down_terminal]
    cases ha : (ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).activation
        (ActualReferenceInitializationBlock.refFollower i) with
    | none => simp only [Option.map_none, reduceCtorEq, false_and, exists_false]
    | some a =>
        simp only [Option.map_some, Option.some.injEq, exists_eq_left']
        exact (exists_cohort_eq a
          (ReferenceInitializationRun.ordinary (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)) (fun a state =>
              state.downBatch.completed.length = k ∧ state.downBatch.pending = [] ∧
                bankBirth a state.downBatch = some p.T)).symm

private theorem currentCohort_active_next
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row r.isLt.le
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inl active)) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let own := ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) r
    currentCohort rate rewards C_star C_h z i (r.val + 1) r.isLt =
      some (active.val.2.1, ReferencePrelaunchFollower.step i x.row active.val.2.1 r own
        active.val.2.2.2) := by
  classical
  by_cases hn : r.val + 1 < p.T
  · have hs := source_prelaunch_down_active_successor rate rewards C_star C_h z i r hn
    rw [hp] at hs
    rcases hs with ⟨_, ha, _, _, hs⟩
    unfold currentCohort
    rw [dite_eq_left hn]
    cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨r.val + 1, hn⟩ with
    | inl branch =>
        cases branch with
        | inl next => rw [hnp] at hs; simp only [hs.2.2.1, hs.2.2.2]; rfl
        | inr next => rw [hnp] at hs; exact hs.elim
    | inr next =>
        rw [hnp] at hs
        have ha' : next.val.1.activation (ActualReferenceInitializationBlock.refFollower i) =
            some active.val.2.1 := by rw [hs.2.1]; exact ha
        simp only [ha', Option.map_some, hs.2.2]
        rfl
  · have hlast : r.val + 1 = p.T := by omega
    have hs := source_prelaunch_down_active_terminal rate rewards C_star C_h z i r hlast
    rw [hp] at hs
    rcases hs with ⟨_, _, _, _, _, _, ha, _, _, hstate, _⟩
    unfold currentCohort
    rw [dite_eq_right hn]
    simp only [ha, Option.map_some, hstate]
    rfl

private theorem currentCohort_stopped_next
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (stopped : StoppedProjection p (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r) i)
    (hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inr stopped) :
    currentCohort rate rewards C_star C_h z i (r.val + 1) r.isLt =
      currentCohort rate rewards C_star C_h z i r.val r.isLt.le := by
  classical
  have hs := source_prelaunch_down_stopped_to_terminal rate rewards C_star C_h z i r
  rw [hp] at hs
  rcases hs with ⟨hterminal, _, _, _, hlater⟩
  unfold currentCohort
  rw [dite_eq_left r.isLt, hp]
  by_cases hn : r.val + 1 < p.T
  · obtain ⟨next, hnp, hsame, _, _, _⟩ := hlater ⟨r.val + 1, hn⟩ (by simp)
    rw [dite_eq_left hn, hnp]
    dsimp only
    rw [hsame]
  · rw [dite_eq_right hn, ← hterminal]

private theorem currentCohort_inactive_next
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (inactive : InactiveProjection p i r.val r.isLt.le
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inr inactive)) :
    currentCohort rate rewards C_star C_h z i (r.val + 1) r.isLt = none ∨
      ∃ a, a.val = r.val + 2 ∧
        currentCohort rate rewards C_star C_h z i (r.val + 1) r.isLt =
          some (a, ReferencePrelaunchFollower.initial p rate.eta) := by
  classical
  by_cases hn : r.val + 1 < p.T
  · have hs := source_prelaunch_down_inactive_successor rate rewards C_star C_h z i r hn
    rw [hp] at hs
    rcases hs with ⟨_, _, hs⟩
    unfold currentCohort
    rw [dite_eq_left hn]
    cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨r.val + 1, hn⟩ with
    | inl branch =>
        cases branch with
        | inl next =>
            rw [hnp] at hs
            obtain ⟨_, a, ha, _, _, hval, hstate, _⟩ := hs
            exact Or.inr ⟨a, hval, by dsimp only; rw [ha, hstate]; rfl⟩
        | inr next => exact Or.inl rfl
    | inr next =>
        rw [hnp] at hs
        obtain ⟨_, a, _, ha, hval, hstate, _⟩ := hs
        exact Or.inr ⟨a, hval, by simp only [ha, Option.map_some, hstate]; rfl⟩
  · have hlast : r.val = p.T - 1 := by omega
    have hr : r = (⟨p.T - 1, by have := T_pos p; omega⟩ : Fin p.T) := Fin.ext hlast
    have hs := source_prelaunch_down_inactive_terminal_handoff rate rewards C_star C_h z i
    rw [← hr] at hs
    simp only [hp] at hs
    rcases hs with ⟨_, _, _, hs⟩
    unfold currentCohort
    rw [dite_eq_right hn]
    rcases hs with hnone | ⟨a, ha, hval, hstate, _⟩
    · left
      simp only [source_prelaunch_down_terminal, hnone.1, Option.map_none]
    · right
      refine ⟨a, by omega, ?_⟩
      simp only [source_prelaunch_down_terminal, ha, Option.map_some, hstate]

/-- Conditional constructor elimination. Its selector, block-end equation and
activation equation are explicit local inputs; the iff below constructs them
from its operational alternative, rather than adding them to Gamma. -/
private theorem currentCohort_inactive_creation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T)
    (inactive : InactiveProjection p i r.val r.isLt.le
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inl (.inr inactive))
    (htime : r.val + 1 = ReferenceInitializationRun.elapsed p (inactive.val.1.val.completed + 1))
    (ha : (ReferenceInitializationRun.finishBlock (sourceReferenceInput rate rewards C_star C_h z)
      inactive.val.1.val inactive.val.1.property.1).activation
        (ActualReferenceInitializationBlock.refFollower i) =
      some (ReferenceInitializationRun.boundaryActivation inactive.val.1.val)) :
    currentCohort rate rewards C_star C_h z i (r.val + 1) r.isLt =
      some (ReferenceInitializationRun.boundaryActivation inactive.val.1.val,
        ReferencePrelaunchFollower.initial p rate.eta) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  by_cases hn : r.val + 1 < p.T
  · let rn : Fin p.T := ⟨r.val + 1, hn⟩
    have hs := source_prelaunch_down_inactive_successor rate rewards C_star C_h z i r hn
    rw [hp] at hs
    rcases hs with ⟨_, _, hs⟩
    unfold currentCohort
    rw [dite_eq_left hn]
    cases hnp : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
    | inl branch =>
        cases branch with
        | inl next =>
            rw [hnp] at hs
            obtain ⟨_, a, haa, hb, hact, _, hstate, _⟩ := hs
            have heq : a = ReferenceInitializationRun.boundaryActivation inactive.val.1.val := by
              apply Option.some.inj
              exact hact.symm.trans (by rw [hb]; exact ha)
            dsimp only
            rw [haa, heq, hstate]
            rfl
        | inr next =>
            rw [hnp] at hs
            rcases hs.2.2 with hsame | ⟨hfinish, _, _⟩
            · have hprogress := ReferenceInitializationRun.run_progress x
                (roundBlockIndex p rn).val (roundBlockIndex p rn).isLt.le
              rw [← next.val.1.property.2.2] at hprogress
              have hc : next.val.1.val.completed = (roundBlockIndex p rn).val :=
                hprogress.resolve_left (by rw [next.val.1.property.2.1]; exact Bool.false_ne_true)
              have hm := (mem_calendarBlock_iff p (roundBlockIndex p rn) rn).mp
                (round_mem_quotient_block p rn)
              have hstrict : rn.val < ReferenceInitializationRun.elapsed p
                  (next.val.1.val.completed + 1) := by
                rw [hc]
                exact hm.2
              rw [hsame] at hstrict
              change r.val + 1 < _ at hstrict
              omega
            · have hnone := hs.2.1
              rw [hfinish, ha] at hnone
              cases hnone
    | inr next =>
        rw [hnp] at hs
        obtain ⟨_, a, hb, hact, _, hstate, _⟩ := hs
        have heq : a = ReferenceInitializationRun.boundaryActivation inactive.val.1.val := by
          apply Option.some.inj
          exact hact.symm.trans (by rw [hb]; exact ha)
        simp only [hact, Option.map_some, heq, hstate]
        rfl
  · have hlast : r.val + 1 = p.T := by omega
    have hr : r = (⟨p.T - 1, by have := T_pos p; omega⟩ : Fin p.T) := by
      apply Fin.ext
      change r.val = p.T - 1
      omega
    have hs := source_prelaunch_down_inactive_terminal_handoff rate rewards C_star C_h z i
    rw [← hr] at hs
    simp only [hp] at hs
    rcases hs with ⟨_, _, _, hs⟩
    have hout : ReferenceInitializationRun.output x =
        ReferenceInitializationRun.finishBlock x inactive.val.1.val inactive.val.1.property.1 := by
      have hq := (last_round_block r hlast).2
      change ReferenceInitializationRun.run x (n_boot p) = _
      calc
        ReferenceInitializationRun.run x (n_boot p) =
            ReferenceInitializationRun.run x ((roundBlockIndex p r).val + 1) :=
              congrArg (ReferenceInitializationRun.run x) hq.symm
        _ = ReferenceInitializationRun.advance x
            (ReferenceInitializationRun.run x (roundBlockIndex p r).val) :=
              ReferenceInitializationRun.run_succ x _
        _ = ReferenceInitializationRun.advance x inactive.val.1.val :=
              congrArg (ReferenceInitializationRun.advance x) inactive.val.1.property.2.2.symm
        _ = _ := ReferenceInitializationRun.advance_of_no_crossing x _
              inactive.val.1.property.2.1 inactive.val.1.property.1
    rcases hs with hnone | ⟨a, hact, _, hstate, _⟩
    · have hno := hnone.1
      rw [hout, ha] at hno
      cases hno
    · have heq : a = ReferenceInitializationRun.boundaryActivation inactive.val.1.val :=
        Option.some.inj (hact.symm.trans (by rw [hout]; exact ha))
      simp only [currentCohort, dite_eq_right hn, source_prelaunch_down_terminal,
        hact, Option.map_some, heq, hstate]

private theorem currentCohort_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    currentCohort rate rewards C_star C_h z i 0 (Nat.zero_le _) = none := by
  classical
  have hT := T_pos p
  have hindex : (roundBlockIndex p ⟨0, hT⟩).val = 0 := Nat.zero_div _
  unfold currentCohort
  rw [dite_eq_left hT]
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨0, hT⟩ with
  | inl branch =>
      cases branch with
      | inl active =>
          have ha := active.property.choose_spec.1
          have hb : active.val.1.val = ReferenceInitializationRun.initial p :=
            active.val.1.property.2.2.trans (by rw [hindex, ReferenceInitializationRun.run_zero])
          rw [hb] at ha
          cases ha
      | inr inactive => rfl
  | inr stopped =>
      have hc := stopped.property.1
      have hb : stopped.val.1 = ReferenceInitializationRun.initial p :=
        stopped.property.2.1.trans (by rw [hindex, ReferenceInitializationRun.run_zero])
      rw [hb] at hc
      exact (hc rfl).elim

private theorem active_birthAt_next_is_clear
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hActive : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inl active)) (k : ℕ)
    (hBirth : birthAt rate rewards C_star C_h z i (r.val + 1) hNext k) :
    let x := sourceReferenceInput rate rewards C_star C_h z
    let a := active.val.2.1
    let state := active.val.2.2.2
    let own := ReferenceInitializationRun.ownEntry
      (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
      (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)) r
    let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
    let bank := state.downBatch
    let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
    let next := ReferencePrelaunchFollower.step i x.row a r own state
    let stamped := AffineBatchDecoder.entry p tr r
    state.status = .unoccupied ∧
      bank.completed.length + 1 = k ∧
      AffineBatchDecoder.eligible (tr r) ∧
      bank.pending.length + 1 = AffineBatchDecoder.quota p ∧
      stamped.time = r ∧
      source_prelaunch_down_current_test rate rewards C_star C_h z i r =
        some ⟨r, (tr r).sample, none⟩ ∧
      decoded = (⟨[], bank.completed ++ [bank.pending ++ [stamped]]⟩,
        AffineBatchDecoder.batchOutput (bank.pending ++ [stamped])) ∧
      next.downBatch = decoded.1 ∧
      next = {state with
        downBatch := ⟨[], bank.completed ++ [bank.pending ++ [stamped]]⟩
        buffer := state.buffer ++ ReferencePrelaunchFollower.logAt i x.row a r own
        initializationFailure := state.initializationFailure || decide
          (ReferencePrelaunchFollower.passing_at x.eta i x.row a r own bank)} := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let a := active.val.2.1
  let state := active.val.2.2.2
  let own := ReferenceInitializationRun.ownEntry
    (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
    (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)) r
  let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
  let bank := state.downBatch
  let next := ReferencePrelaunchFollower.step i x.row a r own state
  have hnext := currentCohort_active_next rate rewards C_star C_h z i r active hActive
  have hv := (birthAt_currentCohort rate rewards C_star C_h z i
    (r.val + 1) hNext k).mp hBirth
  rcases hv with ⟨a', state', hv, hlen, hempty, hbirth⟩
  rw [hnext] at hv
  have heq := Option.some.inj hv
  cases Prod.mk.inj heq with
  | intro ha hs =>
    subst a'
    subst state'
    have hc := source_prelaunch_down_active_step_census rate rewards C_star C_h z i r
    rw [hActive] at hc
    rcases hc with ⟨hstatus, _, _, _, hdecode, _, _, hcurrent, _, hgap,
      hsizes, hsub, hquota, _⟩
    by_cases he : AffineBatchDecoder.eligible (tr r)
    · rcases hsizes he with hsmall | hfull
      · have happend := (hsub he hsmall).1
        rw [happend] at hempty
        simp at hempty
      · have hq := hquota he hfull
        have hdecoded := ReferencePrelaunchFollower.decodeAt_complete i x.row a r own bank he hfull
        refine ⟨hstatus, ?_, he, hfull, rfl, ?_, hdecoded, hdecode, ?_⟩
        · rw [hq.2.2.1] at hlen
          exact hlen
        · simpa [he, tr, own, x, a] using hcurrent
        · have hd : (ReferencePrelaunchFollower.decodeAt i x.row a r own bank).1 =
                ⟨[], bank.completed ++ [bank.pending ++ [AffineBatchDecoder.entry p tr r]]⟩ :=
              congrArg Prod.fst hdecoded
          dsimp only [bank, tr, a, state, own, x] at hd
          simp only [ReferencePrelaunchFollower.step, hstatus, ite_true, hd]
    · have hb := source_prelaunch_down_prefix_birth_bounds rate rewards C_star C_h z i r
      rw [hActive] at hb
      obtain ⟨beta, hbeta, hbound, _⟩ := hb
      have hsame := (hgap he).2.2.2
      have heq : beta = r.val + 1 := Option.some.inj
        (hbeta.symm.trans (hsame.symm.trans hbirth))
      omega

private theorem inactive_birthAt_next_is_creation
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (inactive : InactiveProjection p i r.val (Nat.le_of_lt r.isLt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hInactive : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inr inactive)) (k : ℕ)
    (hBirth : birthAt rate rewards C_star C_h z i (r.val + 1) hNext k) :
    k = 0 ∧
      ∃ q : Fin (n_boot p),
        let b := inactive.val.1.val
        let hblock := inactive.val.1.property.1
        let f := ActualReferenceInitializationBlock.refFollower i
        let x := sourceReferenceInput rate rewards C_star C_h z
        let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
          ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2 inactive.property.2.1⟩
        let candidate := ReferenceInitializationRun.candidate x b hblock ui
        let after := ReferenceInitializationRun.finishBlock x b hblock
        let a := ReferenceInitializationRun.boundaryActivation b
        q = roundBlockIndex p r ∧ b = inactive.val.1.val ∧
          b = ReferenceInitializationRun.run x q.val ∧ b.crossing = none ∧
          b.completed < n_boot p ∧ b.activation f = none ∧
          r.val + 1 = ReferenceInitializationRun.elapsed p (b.completed + 1) ∧
          after.activation f = some a ∧ a.val = r.val + 2 ∧
          ReferenceInitializationRun.ordinary x after f =
            ReferencePrelaunchFollower.initial p x.eta ∧
          ((candidate.pending = true ∧
              ReferenceInitializationRun.declaredActivation x b hblock f = some a ∧
              after.forcedFailure f = false) ∨
            (candidate.pending = false ∧
              ReferenceInitializationRun.forced x b hblock f = true ∧
              after.forcedFailure f = true ∧
              ReferenceInitializationRun.declaredActivation x b hblock f = none)) := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  let b := inactive.val.1.val
  let hblock := inactive.val.1.property.1
  let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
    ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2 inactive.property.2.1⟩
  let candidate := ReferenceInitializationRun.candidate x b hblock ui
  let after := ReferenceInitializationRun.finishBlock x b hblock
  let a := ReferenceInitializationRun.boundaryActivation b
  by_cases hStrict : r.val + 1 < p.T
  · let rn : Fin p.T := ⟨r.val + 1, hStrict⟩
    have hSuccessor := source_prelaunch_down_inactive_successor
      rate rewards C_star C_h z i r hStrict
    rw [hInactive] at hSuccessor
    rcases hSuccessor with ⟨_, _, hNextCase⟩
    cases hNextPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
    | inl branch =>
        cases branch with
        | inl nextActive =>
            rw [hNextPrefix] at hNextCase
            rcases hNextCase with
              ⟨_, aNext, hProjection, hBoundary, hActivation, hVal,
                hState, hPending, hDeclared⟩
            have haBoundary : a = aNext := by
              have hu : f ∈ ReferenceInitializationRun.uninformed b := ui.property
              have hdeclaredBoundary :
                  ReferenceInitializationRun.declaredActivation x b hblock f = some a := by
                unfold ReferenceInitializationRun.declaredActivation
                rw [dite_eq_left hu, hPending]
                rfl
              exact (Option.some.inj (hDeclared.symm.trans hdeclaredBoundary)).symm
            have hBirthNext :
                nextActive.val.2.2.2.downBatch.completed.length = k := by
              rw [birthAt_prefix_view rate rewards C_star C_h z i
                (r.val + 1) hNext hStrict k] at hBirth
              rw [hNextPrefix] at hBirth
              exact hBirth.1
            have hk : k = 0 := by
              rw [hState, ReferencePrelaunchFollower.initial,
                AffineBatchDecoder.initial] at hBirthNext
              exact hBirthNext.symm
            have hRun : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
              inactive.val.1.property.2.2
            have hCrossRun : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing =
                none := by
              rw [← hRun]
              exact inactive.val.1.property.2.1
            have hbefore : b.forcedFailure f = false := by
              rw [hRun]
              exact ReferenceInitializationRun.run_no_forced_before_launch x
                (roundBlockIndex p r).val hCrossRun f
            have hforced : ReferenceInitializationRun.forced x b hblock f = false := by
              simpa [ui] using
                ReferenceInitializationRun.saved_not_forced x b hblock ui hPending
            have hAfterActivation : after.activation f = some a := by
              simpa [after, a] using
                ReferenceInitializationRun.saved_activation x b hblock ui hPending
            have hAfterOrdinary :
                ReferenceInitializationRun.ordinary x after f =
                  ReferencePrelaunchFollower.initial p x.eta := by
              simpa [after] using ReferenceInitializationRun.ordinary_finishBlock_of_saved
                x b hblock ui hPending hbefore
            have hAfterFailure : after.forcedFailure f = false := by
              simp [after, ReferenceInitializationRun.finishBlock, hbefore, hforced]
            have hcompleted : b.completed = (roundBlockIndex p r).val := by
              have hprogress := ReferenceInitializationRun.run_progress x
                (roundBlockIndex p r).val (roundBlockIndex p r).isLt.le
              rw [← hRun] at hprogress
              exact hprogress.resolve_left (by
                rw [inactive.val.1.property.2.1]
                exact Bool.false_ne_true)
            have hTime : r.val + 1 =
                ReferenceInitializationRun.elapsed p (b.completed + 1) := by
              have htiming := ReferenceInitializationRun.boundaryActivation_timing b hblock
              have htiming' : a.val =
                  ReferenceInitializationRun.elapsed p (b.completed + 1) + 1 := by
                simpa [a, ReferenceInitializationRun.elapsed,
                  ReferenceInitializationRun.nextBlock] using htiming
              have hvalue : a.val = r.val + 2 := by
                rw [haBoundary]
                exact hVal
              omega
            refine ⟨hk, ?_⟩
            refine ⟨roundBlockIndex p r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · rfl
            · rfl
            · exact inactive.val.1.property.2.2
            · exact inactive.val.1.property.2.1
            · exact inactive.val.1.property.1
            · exact inactive.property.2.1
            · exact hTime
            · exact hAfterActivation
            · have hvalue : a.val = r.val + 2 := by
                rw [haBoundary]
                exact hVal
              exact hvalue
            · refine ⟨hAfterOrdinary, ?_⟩
              left
              have hDeclaredBoundary :
                  ReferenceInitializationRun.declaredActivation x b hblock f = some a := by
                rw [← haBoundary] at hDeclared
                exact hDeclared
              exact ⟨hPending, hDeclaredBoundary, hAfterFailure⟩
        | inr _ =>
            have hBirthView := hBirth
            rw [birthAt_prefix_view rate rewards C_star C_h z i
              (r.val + 1) hNext hStrict k] at hBirthView
            rw [hNextPrefix] at hBirthView
            exact False.elim hBirthView
    | inr nextStopped =>
        rw [hNextPrefix] at hNextCase
        rcases hNextCase with
          ⟨_, aNext, hBoundary, hActivation, hval, hState, hOrigin⟩
        have hBirthNext : nextStopped.val.2.downBatch.completed.length = k := by
          rw [birthAt_prefix_view rate rewards C_star C_h z i
            (r.val + 1) hNext hStrict k] at hBirth
          rw [hNextPrefix] at hBirth
          rcases hBirth with ⟨_, _, hlen, _, _⟩
          exact hlen
        have hk : k = 0 := by
          rw [hState, ReferencePrelaunchFollower.initial,
            AffineBatchDecoder.initial] at hBirthNext
          exact hBirthNext.symm
        have hAfterActivationRoot : after.activation f = some aNext := by
          simpa [after, hBoundary] using hActivation
        have hAfterActivation : after.activation f = some a := by
          rcases hOrigin with hSaved | hForced
          · simpa [after, a] using
              ReferenceInitializationRun.saved_activation x b hblock ui hSaved.1
          · have hforced : ReferenceInitializationRun.forced x b hblock f = true :=
              hForced.2.1
            simp [after, ReferenceInitializationRun.finishBlock,
              ReferenceInitializationRun.finalActivation, hforced, a]
        have haBoundary : a = aNext :=
          Option.some.inj (hAfterActivation.symm.trans hAfterActivationRoot)
        have hRun : b = ReferenceInitializationRun.run x (roundBlockIndex p r).val :=
          inactive.val.1.property.2.2
        have hCrossRun : (ReferenceInitializationRun.run x (roundBlockIndex p r).val).crossing =
            none := by
          rw [← hRun]
          exact inactive.val.1.property.2.1
        have hbefore : b.forcedFailure f = false := by
          rw [hRun]
          exact ReferenceInitializationRun.run_no_forced_before_launch x
            (roundBlockIndex p r).val hCrossRun f
        have hAfterOrdinary :
            ReferenceInitializationRun.ordinary x after f =
              ReferencePrelaunchFollower.initial p x.eta := by
          rcases hOrigin with hSaved | hForced
          · simpa [after] using ReferenceInitializationRun.ordinary_finishBlock_of_saved
              x b hblock ui hSaved.1 hbefore
          · have hforce : ReferenceInitializationRun.forced x b hblock f = true :=
              hForced.2.1
            calc
              ReferenceInitializationRun.ordinary x after f =
                  ReferencePrelaunchFollower.forcedAtLaunch p x.eta := by
                    simpa [after] using
                      ReferenceInitializationRun.forced_ordinary x b hblock f hforce
              _ = ReferencePrelaunchFollower.initial p x.eta := rfl
        have hTime : r.val + 1 =
            ReferenceInitializationRun.elapsed p (b.completed + 1) := by
          have htiming := ReferenceInitializationRun.boundaryActivation_timing b hblock
          have htiming' : a.val =
              ReferenceInitializationRun.elapsed p (b.completed + 1) + 1 := by
            simpa [a, ReferenceInitializationRun.elapsed,
              ReferenceInitializationRun.nextBlock] using htiming
          have hvalue : a.val = r.val + 2 := by
            rw [haBoundary]
            exact hval
          omega
        refine ⟨hk, ?_⟩
        refine ⟨roundBlockIndex p r, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rfl
        · rfl
        · exact inactive.val.1.property.2.2
        · exact inactive.val.1.property.2.1
        · exact inactive.val.1.property.1
        · exact inactive.property.2.1
        · exact hTime
        · exact hAfterActivation
        · have hvalue : a.val = r.val + 2 := by
            rw [haBoundary]
            exact hval
          exact hvalue
        · refine ⟨hAfterOrdinary, ?_⟩
          rcases hOrigin with hSaved | hForced
          · left
            have hdeclared : ReferenceInitializationRun.declaredActivation x b hblock f = some a := by
              have hdeclaredSaved := hSaved.2.2
              rw [← haBoundary] at hdeclaredSaved
              exact hdeclaredSaved
            have hAfterFailure : after.forcedFailure f = false := by
              simpa [after, hBoundary] using hSaved.2.1
            exact ⟨hSaved.1, hdeclared, hAfterFailure⟩
          · right
            have hAfterFailure : after.forcedFailure f = true := by
              simpa [after, hBoundary] using hForced.2.2.1
            exact ⟨hForced.1, hForced.2.1, hAfterFailure, hForced.2.2.2⟩
  · have hLast : r.val + 1 = p.T := by omega
    have hBirthAtTerminal : birthAt rate rewards C_star C_h z i p.T le_rfl k := by
      simpa only [hLast] using hBirth
    rw [birthAt_terminal_view rate rewards C_star C_h z i le_rfl k] at hBirthAtTerminal
    rcases hBirthAtTerminal with ⟨aOut, hActivationOut, hLengthOut, _, _⟩
    let q := roundBlockIndex p r
    have hblockEnd := last_round_block r hLast
    have hboundary : b = ReferenceInitializationRun.run x q.val :=
      inactive.val.1.property.2.2
    have hCrossRun : (ReferenceInitializationRun.run x q.val).crossing = none := by
      rw [← hboundary]
      exact inactive.val.1.property.2.1
    have hbefore : b.forcedFailure f = false := by
      rw [hboundary]
      exact ReferenceInitializationRun.run_no_forced_before_launch x q.val hCrossRun f
    have hrun : ReferenceInitializationRun.run x (q.val + 1) = after := by
      have hstep := ReferenceInitializationRun.run_succ x q.val
      rw [← hboundary] at hstep
      rw [ReferenceInitializationRun.advance_of_no_crossing x b
        inactive.val.1.property.2.1 hblock] at hstep
      exact hstep
    have hqLast : q.val + 1 = n_boot p := by
      simpa [q] using hblockEnd.2
    have houtput : ReferenceInitializationRun.output x = after := by
      change ReferenceInitializationRun.run x (n_boot p) = after
      rw [← hqLast]
      exact hrun
    have hcompleted : b.completed = q.val := by
      have hrunProgress := ReferenceInitializationRun.run_progress x q.val q.isLt.le
      rw [← hboundary] at hrunProgress
      exact hrunProgress.resolve_left (by
        rw [inactive.val.1.property.2.1]
        exact Bool.false_ne_true)
    have hTime : r.val + 1 = ReferenceInitializationRun.elapsed p (b.completed + 1) := by
      rw [hcompleted, hblockEnd.1]
      omega
    have hActivationAfter : after.activation f = some aOut := by
      change (ReferenceInitializationRun.output x).activation f = some aOut at hActivationOut
      rw [houtput] at hActivationOut
      exact hActivationOut
    have hLengthAfter :
        (ReferenceInitializationRun.ordinary x after f).downBatch.completed.length = k := by
      change ((ReferenceInitializationRun.ordinary x
        (ReferenceInitializationRun.output x) f).downBatch.completed.length) = k at hLengthOut
      rw [houtput] at hLengthOut
      exact hLengthOut
    by_cases hPending : candidate.pending = true
    · have hDeclared : ReferenceInitializationRun.declaredActivation x b hblock f = some a := by
        have hu : f ∈ ReferenceInitializationRun.uninformed b := ui.property
        unfold ReferenceInitializationRun.declaredActivation
        rw [dite_eq_left hu, hPending]
        rfl
      have hAfterActivation : after.activation f = some a := by
        simpa [after, a] using
          ReferenceInitializationRun.saved_activation x b hblock ui hPending
      have hAfterOrdinary : ReferenceInitializationRun.ordinary x after f =
          ReferencePrelaunchFollower.initial p x.eta := by
        simpa [after] using ReferenceInitializationRun.ordinary_finishBlock_of_saved
          x b hblock ui hPending hbefore
      have hAfterFailure : after.forcedFailure f = false := by
        have hnotforced := ReferenceInitializationRun.saved_not_forced
          x b hblock ui hPending
        change ReferenceInitializationRun.forced x b hblock f = false at hnotforced
        change (b.forcedFailure f || ReferenceInitializationRun.forced x b hblock f) = false
        rw [hbefore, hnotforced]
        rfl
      have hk : k = 0 := by
        rw [hAfterOrdinary, ReferencePrelaunchFollower.initial,
          AffineBatchDecoder.initial] at hLengthAfter
        exact hLengthAfter.symm
      have hvalue : a.val = r.val + 2 := by
        have htiming := ReferenceInitializationRun.boundaryActivation_timing b hblock
        have htiming' : a.val =
            min p.T ((b.completed + 1) * B_boot p) + 1 := by
          simpa [a, ReferenceInitializationRun.nextBlock] using htiming
        have hmin : min p.T ((b.completed + 1) * B_boot p) = p.T := by
          have hend := hblockEnd.1
          rw [← hcompleted] at hend
          change min p.T ((b.completed + 1) * B_boot p) = p.T at hend
          exact hend
        rw [hmin] at htiming'
        omega
      refine ⟨hk, ?_⟩
      refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rfl
      · rfl
      · exact inactive.val.1.property.2.2
      · exact inactive.val.1.property.2.1
      · exact inactive.val.1.property.1
      · exact inactive.property.2.1
      · exact hTime
      · exact hAfterActivation
      · exact hvalue
      · refine ⟨hAfterOrdinary, ?_⟩
        left
        exact ⟨hPending, hDeclared, hAfterFailure⟩
    · have hPendingFalse : candidate.pending = false := by
        cases hp : candidate.pending <;> simp_all
      have hDeclaredNone : ReferenceInitializationRun.declaredActivation x b hblock f = none := by
        have hu : f ∈ ReferenceInitializationRun.uninformed b := ui.property
        unfold ReferenceInitializationRun.declaredActivation
        rw [dite_eq_left hu, hPendingFalse]
        rfl
      by_cases hCross : ReferenceInitializationRun.crosses x b hblock = true
      · have hForced : ReferenceInitializationRun.forced x b hblock f = true := by
          simp [ReferenceInitializationRun.forced, hDeclaredNone, hCross]
        have hAfterActivation : after.activation f = some a := by
          change ReferenceInitializationRun.finalActivation x b hblock f = some a
          unfold ReferenceInitializationRun.finalActivation
          rw [hForced]
          rfl
        have hAfterOrdinary : ReferenceInitializationRun.ordinary x after f =
            ReferencePrelaunchFollower.initial p x.eta := by
          calc
            ReferenceInitializationRun.ordinary x after f =
                ReferencePrelaunchFollower.forcedAtLaunch p x.eta := by
                  simpa [after] using
                    ReferenceInitializationRun.forced_ordinary x b hblock f hForced
            _ = ReferencePrelaunchFollower.initial p x.eta := rfl
        have hAfterFailure : after.forcedFailure f = true := by
          simp [after, ReferenceInitializationRun.finishBlock, hbefore, hForced]
        have hk : k = 0 := by
          rw [hAfterOrdinary, ReferencePrelaunchFollower.initial,
            AffineBatchDecoder.initial] at hLengthAfter
          exact hLengthAfter.symm
        have hvalue : a.val = r.val + 2 := by
          have htiming := ReferenceInitializationRun.boundaryActivation_timing b hblock
          have htiming' : a.val =
              min p.T ((b.completed + 1) * B_boot p) + 1 := by
            simpa [a, ReferenceInitializationRun.nextBlock] using htiming
          have hmin : min p.T ((b.completed + 1) * B_boot p) = p.T := by
            have hend := hblockEnd.1
            rw [← hcompleted] at hend
            change min p.T ((b.completed + 1) * B_boot p) = p.T at hend
            exact hend
          rw [hmin] at htiming'
          omega
        refine ⟨hk, ?_⟩
        refine ⟨q, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rfl
        · rfl
        · exact inactive.val.1.property.2.2
        · exact inactive.val.1.property.2.1
        · exact inactive.val.1.property.1
        · exact inactive.property.2.1
        · exact hTime
        · exact hAfterActivation
        · exact hvalue
        · refine ⟨hAfterOrdinary, ?_⟩
          right
          exact ⟨hPendingFalse, hForced, hAfterFailure, hDeclaredNone⟩
      · have hCrossFalse : ReferenceInitializationRun.crosses x b hblock = false := by
          cases hc : ReferenceInitializationRun.crosses x b hblock with
          | false => rfl
          | true => exact (hCross hc).elim
        have hNoActivation : after.activation f = none := by
          change ReferenceInitializationRun.finalActivation x b hblock f = none
          simp [ReferenceInitializationRun.finalActivation,
            ReferenceInitializationRun.forced, hDeclaredNone, hCrossFalse]
        rw [hNoActivation] at hActivationAfter
        cases hActivationAfter

/-- A stopped predecessor cannot create a later birth. The actual stopped
prefix preserves its complete boundary and ordinary state through the
terminal output; the reviewed strict bounds then put its previous birth
before the proposed calendar time. -/
private theorem birthAt_next_of_stopped_false
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (stopped : StoppedProjection p (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p r) i)
    (hPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r = .inr stopped)
    (k : ℕ)
    (hBirth : birthAt rate rewards C_star C_h z i (r.val + 1) hNext k) : False := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let f := ActualReferenceInitializationBlock.refFollower i
  have hStopped := source_prelaunch_down_stopped_to_terminal
    rate rewards C_star C_h z i r
  rw [hPrefix] at hStopped
  rcases hStopped with ⟨hSameTerminal, _, _, _, hLater⟩
  by_cases hStrict : r.val + 1 < p.T
  · let rNext : Fin p.T := ⟨r.val + 1, hStrict⟩
    obtain ⟨stoppedNext, hNextPrefix, hSame, _, _, _⟩ :=
      hLater rNext (by dsimp [rNext]; omega)
    have hBirthNext := hBirth
    rw [birthAt_prefix_view rate rewards C_star C_h z i
      (r.val + 1) hNext hStrict k] at hBirthNext
    rw [hNextPrefix] at hBirthNext
    rcases hBirthNext with ⟨a, ha, _, _, hBirthNextBank⟩
    have hBounds := source_prelaunch_down_prefix_birth_bounds
      rate rewards C_star C_h z i r
    rw [hPrefix] at hBounds
    rcases hBounds with ⟨_, hStoppedBounds⟩
    obtain ⟨beta, hBirthStoppedBank, hBetaBound, hElapsedBound, _⟩ :=
      hStoppedBounds a (by simpa [hSame] using ha)
    rw [hSame] at hBirthNextBank
    have hBetaEq : beta = r.val + 1 :=
      Option.some.inj (hBirthStoppedBank.symm.trans hBirthNextBank)
    omega
  · have hLast : r.val + 1 = p.T := by omega
    have hBirthTerminal :
        birthAt rate rewards C_star C_h z i p.T (Nat.le_refl p.T) k := by
      simpa [hLast] using hBirth
    rw [birthAt_terminal_view rate rewards C_star C_h z i
      (Nat.le_refl p.T) k] at hBirthTerminal
    rcases hBirthTerminal with ⟨a, hActivation, _, _, hBirthOutputBank⟩
    have hActivationStopped : stopped.val.1.activation f = some a := by
      rw [hSameTerminal]
      simpa [source_prelaunch_down_terminal, x,
        sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
        using hActivation
    have hBounds := source_prelaunch_down_prefix_birth_bounds
      rate rewards C_star C_h z i r
    rw [hPrefix] at hBounds
    rcases hBounds with ⟨_, hStoppedBounds⟩
    obtain ⟨beta, hBirthStoppedBank, hBetaBound, hElapsedBound, _⟩ :=
      hStoppedBounds a hActivationStopped
    have hBirthOutputFromStopped :
        bankBirth a stopped.val.2.downBatch = some p.T := by
      rw [hSameTerminal]
      simpa [source_prelaunch_down_terminal, x,
        sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
        using hBirthOutputBank
    have hBetaEq : beta = p.T :=
      Option.some.inj (hBirthStoppedBank.symm.trans hBirthOutputFromStopped)
    omega

/-- Selector-free operational data for a birth at the next calendar time.
The predecessor case is split from the actual generated prefix. The active
case retains the literal raw solver output and the complete follower-state
update; the inactive case exposes the real declaration/force constructor. -/
theorem source_prelaunch_down_birthAt_next_operational_data
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T) (k : ℕ)
    (hBirth : birthAt rate rewards C_star C_h z i (r.val + 1) hNext k) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        let x := sourceReferenceInput rate rewards C_star C_h z
        let a := active.val.2.1
        let state := active.val.2.2.2
        let own := ReferenceInitializationRun.ownEntry
          (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
          (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)) r
        let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
        let bank := state.downBatch
        let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
        let next := ReferencePrelaunchFollower.step i x.row a r own state
        let stamped := AffineBatchDecoder.entry p tr r
        state.status = .unoccupied ∧
          bank.completed.length + 1 = k ∧
          AffineBatchDecoder.eligible (tr r) ∧
          bank.pending.length + 1 = AffineBatchDecoder.quota p ∧
          stamped.time = r ∧
          source_prelaunch_down_current_test rate rewards C_star C_h z i r =
            some ⟨r, (tr r).sample, none⟩ ∧
          decoded = (⟨[], bank.completed ++ [bank.pending ++ [stamped]]⟩,
            AffineBatchDecoder.batchOutput (bank.pending ++ [stamped])) ∧
          next.downBatch = decoded.1 ∧
          next = {state with
            downBatch := ⟨[], bank.completed ++ [bank.pending ++ [stamped]]⟩
            buffer := state.buffer ++ ReferencePrelaunchFollower.logAt i x.row a r own
            initializationFailure := state.initializationFailure || decide
              (ReferencePrelaunchFollower.passing_at x.eta i x.row a r own bank)}
    | .inl (.inr inactive) =>
        k = 0 ∧
          ∃ q : Fin (n_boot p),
            let b := inactive.val.1.val
            let hblock := inactive.val.1.property.1
            let f := ActualReferenceInitializationBlock.refFollower i
            let x := sourceReferenceInput rate rewards C_star C_h z
            let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
              ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
                inactive.property.2.1⟩
            let candidate := ReferenceInitializationRun.candidate x b hblock ui
            let after := ReferenceInitializationRun.finishBlock x b hblock
            let a := ReferenceInitializationRun.boundaryActivation b
            q = roundBlockIndex p r ∧ b = inactive.val.1.val ∧
              b = ReferenceInitializationRun.run x q.val ∧ b.crossing = none ∧
              b.completed < n_boot p ∧ b.activation f = none ∧
              r.val + 1 = ReferenceInitializationRun.elapsed p (b.completed + 1) ∧
              after.activation f = some a ∧ a.val = r.val + 2 ∧
              ReferenceInitializationRun.ordinary x after f =
                ReferencePrelaunchFollower.initial p x.eta ∧
              ((candidate.pending = true ∧
                  ReferenceInitializationRun.declaredActivation x b hblock f = some a ∧
                  after.forcedFailure f = false) ∨
                (candidate.pending = false ∧
                  ReferenceInitializationRun.forced x b hblock f = true ∧
                  after.forcedFailure f = true ∧
                  ReferenceInitializationRun.declaredActivation x b hblock f = none))
    | .inr _ => True := by
  classical
  cases hPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          simpa [sourceReferenceInput] using
            active_birthAt_next_is_clear rate rewards C_star C_h z i r
              hNext active hPrefix k hBirth
      | inr inactive =>
          simpa [sourceReferenceInput] using
            inactive_birthAt_next_is_creation rate rewards C_star C_h z i r
              hNext inactive hPrefix k hBirth
  | inr _ => trivial

/-- Operational birth iff, with the predecessor chosen from the real calendar.
The inactive alternative gives the genuine saved declaration before forcing;
the active alternative gives unconditional quota clearing with the exact raw
solver output (which may be `none`). All state equalities read the actual run.
Sources: `07_public_setup.tex:60-112,127-142`, `05_binary_transport.tex:20-42`. -/
theorem source_prelaunch_down_birthAt_iff
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (alpha : ℕ) (hAlpha : alpha ≤ p.T) (k : ℕ) :
    birthAt rate rewards C_star C_h z i alpha hAlpha k ↔
      ∃ r : Fin p.T, r.val + 1 = alpha ∧
        match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
        | .inl (.inl active) =>
            let x := sourceReferenceInput rate rewards C_star C_h z
            let a := active.val.2.1
            let state := active.val.2.2.2
            let own := ReferenceInitializationRun.ownEntry
              (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
              (PublicDiscreteDraws.followerPlayer p.two_le_m
                (ActualReferenceInitializationBlock.refFollower i)) r
            let tr := ReferencePrelaunchFollower.traceAt i x.row a r own
            let bank := state.downBatch
            let decoded := ReferencePrelaunchFollower.decodeAt i x.row a r own bank
            let next := ReferencePrelaunchFollower.step i x.row a r own state
            let stamped := AffineBatchDecoder.entry p tr r
            state.status = .unoccupied ∧
              bank.completed.length + 1 = k ∧
              AffineBatchDecoder.eligible (tr r) ∧
              bank.pending.length + 1 = AffineBatchDecoder.quota p ∧
              stamped.time = r ∧
              source_prelaunch_down_current_test rate rewards C_star C_h z i r =
                some ⟨r, (tr r).sample, none⟩ ∧
              decoded = (⟨[], bank.completed ++ [bank.pending ++ [stamped]]⟩,
                AffineBatchDecoder.batchOutput (bank.pending ++ [stamped])) ∧
              next.downBatch = decoded.1 ∧
              next = {state with
                downBatch := ⟨[], bank.completed ++ [bank.pending ++ [stamped]]⟩
                buffer := state.buffer ++ ReferencePrelaunchFollower.logAt i x.row a r own
                initializationFailure := state.initializationFailure || decide
                  (ReferencePrelaunchFollower.passing_at x.eta i x.row a r own bank)}
        | .inl (.inr inactive) =>
            k = 0 ∧
              ∃ q : Fin (n_boot p),
                let b := inactive.val.1.val
                let hblock := inactive.val.1.property.1
                let f := ActualReferenceInitializationBlock.refFollower i
                let x := sourceReferenceInput rate rewards C_star C_h z
                let ui : {f // f ∈ ReferenceInitializationRun.uninformed b} :=
                  ⟨f, (ReferenceInitializationRun.mem_uninformed b f).2
                    inactive.property.2.1⟩
                let candidate := ReferenceInitializationRun.candidate x b hblock ui
                let after := ReferenceInitializationRun.finishBlock x b hblock
                let a := ReferenceInitializationRun.boundaryActivation b
                q = roundBlockIndex p r ∧ b = inactive.val.1.val ∧
                  b = ReferenceInitializationRun.run x q.val ∧ b.crossing = none ∧
                  b.completed < n_boot p ∧ b.activation f = none ∧
                  r.val + 1 = ReferenceInitializationRun.elapsed p (b.completed + 1) ∧
                  after.activation f = some a ∧ a.val = r.val + 2 ∧
                  ReferenceInitializationRun.ordinary x after f =
                    ReferencePrelaunchFollower.initial p x.eta ∧
                  ((candidate.pending = true ∧
                      ReferenceInitializationRun.declaredActivation x b hblock f = some a ∧
                      after.forcedFailure f = false) ∨
                    (candidate.pending = false ∧
                      ReferenceInitializationRun.forced x b hblock f = true ∧
                      after.forcedFailure f = true ∧
                      ReferenceInitializationRun.declaredActivation x b hblock f = none))
        | .inr _ => False := by
  classical
  constructor
  · intro hb
    have hpos : 0 < alpha := by
      by_contra hn
      have hz : alpha = 0 := by omega
      subst alpha
      obtain ⟨a, state, hs, _⟩ :=
        (birthAt_currentCohort rate rewards C_star C_h z i 0 hAlpha k).mp hb
      rw [currentCohort_zero rate rewards C_star C_h z i] at hs
      cases hs
    let r : Fin p.T := ⟨alpha - 1, by omega⟩
    have hr : r.val + 1 = alpha := by dsimp [r]; omega
    have hbNext : birthAt rate rewards C_star C_h z i (r.val + 1) r.isLt k := by
      simpa only [hr] using hb
    have hd := source_prelaunch_down_birthAt_next_operational_data
      rate rewards C_star C_h z i r r.isLt k hbNext
    refine ⟨r, hr, ?_⟩
    cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
        cases branch with
        | inl active => rw [hp] at hd; exact hd
        | inr inactive => rw [hp] at hd; exact hd
    | inr stopped =>
        exact (birthAt_next_of_stopped_false rate rewards C_star C_h z i r
          r.isLt stopped hp k hbNext).elim
  · rintro ⟨r, hr, hd⟩
    subst alpha
    cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
        cases branch with
        | inl active =>
            rw [hp] at hd
            dsimp only at hd
            rcases hd with ⟨_, hk, _, _, _, _, hdecode, hdown, _⟩
            have hs := currentCohort_active_next rate rewards C_star C_h z i r active hp
            apply (birthAt_currentCohort rate rewards C_star C_h z i (r.val + 1) hAlpha k).mpr
            refine ⟨_, _, hs, ?_, ?_, ?_⟩
            · rw [hdown, hdecode]
              simpa only [List.length_append, List.length_singleton] using hk
            · rw [hdown, hdecode]
            · rw [hdown, hdecode, bankBirth_after_clear]
              simp only [AffineBatchDecoder.entry]
        | inr inactive =>
            rw [hp] at hd
            dsimp only at hd
            rcases hd with ⟨hk, q, _, _, _, _, _, _, htime, hact, haval, _⟩
            have hs := currentCohort_inactive_creation rate rewards C_star C_h z i r
              inactive hp htime hact
            apply (birthAt_currentCohort rate rewards C_star C_h z i (r.val + 1) hAlpha k).mpr
            refine ⟨_, _, hs, ?_, rfl, ?_⟩
            · simpa only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
                List.length_nil] using hk.symm
            · simp only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
                bankBirth, List.isEmpty_nil, ite_true]
              congr 1
              omega
    | inr stopped => rw [hp] at hd; exact hd.elim

/-- There is no ordinary cohort at the initial boundary. The operational
alternatives are also impossible there since a real predecessor has index ≥ 0. -/
theorem source_prelaunch_down_birthAt_zero
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (k : ℕ) :
    ¬ birthAt rate rewards C_star C_h z i 0 (Nat.zero_le _) k := by
  intro hb
  obtain ⟨r, hr, _⟩ :=
    (source_prelaunch_down_birthAt_iff rate rewards C_star C_h z i 0 (Nat.zero_le _) k).mp hb
  omega

/-- Per-round ancestry of the actual projection. The induction carries the
completed ordinal and the real `bankBirth` equation; pending emptiness is used
only in the new-birth branches, never to redate a retained bank. -/
private theorem currentCohort_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T)
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hs : currentCohort rate rewards C_star C_h z i n hn = some (a, state)) :
    ∃ beta, ∃ hBeta : beta ≤ p.T, beta ≤ n ∧
      bankBirth a state.downBatch = some beta ∧
      birthAt rate rewards C_star C_h z i beta hBeta state.downBatch.completed.length := by
  classical
  induction n generalizing a state with
  | zero =>
      rw [currentCohort_zero rate rewards C_star C_h z i] at hs
      cases hs
  | succ n ih =>
      let r : Fin p.T := ⟨n, by omega⟩
      cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
      | inl branch =>
          cases branch with
          | inl active =>
              have hnext := currentCohort_active_next rate rewards C_star C_h z i r active hp
              rw [hnext] at hs
              obtain ⟨ha, hstate⟩ := Prod.mk.inj (Option.some.inj hs)
              rw [← ha, ← hstate]
              have hc := source_prelaunch_down_active_step_census rate rewards C_star C_h z i r
              rw [hp] at hc
              rcases hc with ⟨hstatus, _, _, _, hdown, _, _, hcurrent, _, hgap,
                hsizes, hsub, hquota, _⟩
              let x := sourceReferenceInput rate rewards C_star C_h z
              let own := ReferenceInitializationRun.ownEntry
                (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
                (PublicDiscreteDraws.followerPlayer p.two_le_m
                  (ActualReferenceInitializationBlock.refFollower i)) r
              let tr := ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 r own
              let bank := active.val.2.2.2.downBatch
              have hprev : currentCohort rate rewards C_star C_h z i r.val r.isLt.le =
                  some (active.val.2.1, active.val.2.2.2) := by
                simp only [currentCohort, dite_eq_left r.isLt, hp]
                rfl
              obtain ⟨beta, hBeta, hbound, hbirth, hhistory⟩ := ih (by omega) _ _ hprev
              by_cases he : AffineBatchDecoder.eligible (tr r)
              · rcases hsizes he with hsmall | hfull
                · have hretain := hsub he hsmall
                  refine ⟨beta, hBeta, by omega, hretain.2.2.2.1.trans hbirth, ?_⟩
                  rw [hretain.2.2.1]
                  exact hhistory
                · have hclear := hquota he hfull
                  refine ⟨n + 1, hn, le_rfl, hclear.2.2.2.1, ?_⟩
                  apply (source_prelaunch_down_birthAt_iff rate rewards C_star C_h z i
                    (n + 1) hn _).mpr
                  refine ⟨r, rfl, ?_⟩
                  rw [hp]
                  have hd := ReferencePrelaunchFollower.decodeAt_complete i x.row
                    active.val.2.1 r own bank he hfull
                  refine ⟨hstatus, hclear.2.2.1.symm, he, hfull, rfl, ?_, hd, hdown, ?_⟩
                  · simpa [he, tr, own, x] using hcurrent
                  · have hdState := congrArg Prod.fst hd
                    dsimp only [bank, tr, own, x] at hdState
                    simp only [ReferencePrelaunchFollower.step, hstatus, ite_true, hdState]
              · have hretain := hgap he
                refine ⟨beta, hBeta, by omega, hretain.2.2.2.trans hbirth, ?_⟩
                rw [hretain.2.1]
                exact hhistory
          | inr inactive =>
              rcases currentCohort_inactive_next rate rewards C_star C_h z i r inactive hp with
                hnone | ⟨a', haval, hnew⟩
              · rw [hnone] at hs
                cases hs
              · rw [hnew] at hs
                obtain ⟨ha, hstate⟩ := Prod.mk.inj (Option.some.inj hs)
                rw [← ha, ← hstate]
                have hb : bankBirth a' (ReferencePrelaunchFollower.initial p rate.eta).downBatch =
                    some (n + 1) := by
                  simp only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
                    bankBirth, List.isEmpty_nil, ite_true]
                  congr 1
                  dsimp only [r] at haval
                  omega
                refine ⟨n + 1, hn, le_rfl, hb, ?_⟩
                exact (birthAt_currentCohort rate rewards C_star C_h z i (n + 1) hn _).mpr
                  ⟨_, _, hnew, rfl, rfl, hb⟩
      | inr stopped =>
          have hsame := currentCohort_stopped_next rate rewards C_star C_h z i r stopped hp
          obtain ⟨beta, hBeta, hbound, hb, hh⟩ := ih (by omega) a state (hsame.symm.trans hs)
          exact ⟨beta, hBeta, by omega, hb, hh⟩

/-- Every actual current cohort has its unique historical operational birth.
Stopped banks retain their birth bounded by their actual stopping boundary;
inactive/absent activation has no cohort. No ancestry is supplied as an input.
Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`. -/
theorem source_prelaunch_down_current_birth_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) :
    match source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | .inl (.inl active) =>
        ∃ beta, ∃ hBeta : beta ≤ p.T, beta ≤ r.val ∧
          bankBirth active.val.2.1 active.val.2.2.2.downBatch = some beta ∧
          birthAt rate rewards C_star C_h z i beta hBeta
            active.val.2.2.2.downBatch.completed.length ∧
          ∀ beta', bankBirth active.val.2.1 active.val.2.2.2.downBatch = some beta' → beta' = beta
    | .inl (.inr _) => source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r = none
    | .inr stopped =>
        (stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i) = none →
          source_prelaunch_down_prefix_birth rate rewards C_star C_h z i r = none) ∧
        ∀ a, stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i) = some a →
          ∃ beta, ∃ hBeta : beta ≤ p.T,
            beta ≤ ReferenceInitializationRun.elapsed p stopped.val.1.completed ∧
            bankBirth a stopped.val.2.downBatch = some beta ∧
            birthAt rate rewards C_star C_h z i beta hBeta stopped.val.2.downBatch.completed.length ∧
            ∀ beta', bankBirth a stopped.val.2.downBatch = some beta' → beta' = beta := by
  classical
  have hb := source_prelaunch_down_prefix_birth_bounds rate rewards C_star C_h z i r
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hs : currentCohort rate rewards C_star C_h z i r.val r.isLt.le =
              some (active.val.2.1, active.val.2.2.2) := by
            simp only [currentCohort, dite_eq_left r.isLt, hp]
            rfl
          obtain ⟨beta, hBeta, hbound, hb, hh⟩ :=
            currentCohort_history rate rewards C_star C_h z i r.val r.isLt.le _ _ hs
          exact ⟨beta, hBeta, hbound, hb, hh, fun _ he => Option.some.inj (he.symm.trans hb)⟩
      | inr inactive => rw [hp] at hb; exact hb
  | inr stopped =>
      rw [hp] at hb
      refine ⟨hb.1, ?_⟩
      intro a ha
      have hs : currentCohort rate rewards C_star C_h z i r.val r.isLt.le =
          some (a, stopped.val.2) := by
        simp only [currentCohort, dite_eq_left r.isLt, hp, ha, Option.map_some]
        rfl
      obtain ⟨beta, hBeta, _, hbirth, hh⟩ :=
        currentCohort_history rate rewards C_star C_h z i r.val r.isLt.le a _ hs
      obtain ⟨beta', hb', hbound, _⟩ := hb.2 a ha
      have heq : beta' = beta := Option.some.inj (hb'.symm.trans hbirth)
      exact ⟨beta, hBeta, heq ▸ hbound, hbirth, hh,
        fun _ he => Option.some.inj (he.symm.trans hbirth)⟩

/-- Terminal ancestry, including activation at `T+1` and final-round clearing.
The bound is the actual output elapsed time, even when it is strictly below `T`.
The launch-cohort/flag join is a separate successor obligation. -/
theorem source_prelaunch_down_terminal_birth_history
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) :
    let terminal := source_prelaunch_down_terminal rate rewards C_star C_h z i
    ∀ a, terminal.1.activation (ActualReferenceInitializationBlock.refFollower i) = some a →
      ∃ beta, ∃ hBeta : beta ≤ p.T,
        beta ≤ ReferenceInitializationRun.elapsed p terminal.1.completed ∧
        bankBirth a terminal.2.downBatch = some beta ∧
        birthAt rate rewards C_star C_h z i beta hBeta terminal.2.downBatch.completed.length ∧
        ∀ beta', bankBirth a terminal.2.downBatch = some beta' → beta' = beta := by
  classical
  dsimp only
  intro a ha
  have hs : currentCohort rate rewards C_star C_h z i p.T le_rfl =
      some (a, (source_prelaunch_down_terminal rate rewards C_star C_h z i).2) := by
    simp only [currentCohort, dite_eq_right (Nat.lt_irrefl p.T), ha, Option.map_some]
  obtain ⟨beta, hBeta, _, hb, hh⟩ :=
    currentCohort_history rate rewards C_star C_h z i p.T le_rfl a _ hs
  obtain ⟨beta', hb', hbound, _⟩ :=
    source_prelaunch_down_terminal_birth_bounds rate rewards C_star C_h z i a ha
  have heq : beta' = beta := Option.some.inj (hb'.symm.trans hb)
  exact ⟨beta, hBeta, heq ▸ hbound, hb, hh, fun _ he => Option.some.inj (he.symm.trans hb)⟩

end Bandits.Support.ReferenceGeneratedPrelaunchDownHistoricalBirth

end
