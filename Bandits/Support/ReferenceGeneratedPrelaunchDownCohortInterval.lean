/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedPrelaunchDownHistoricalBirth

import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Actual same-birth prelaunch DOWN cohort intervals

The exports in this module follow the one actual generated initialization
source through a current DOWN batch. They identify the last real activation or
quota clearing, and retain the actual generated state at every boundary in
that same cohort interval. The test and flag lists are projections of the
existing generated prefixes and terminal output; no launch condition or
alternate execution is introduced.

Sources: `appendix_a_local_protocol.tex:111-153`,
`appendix_b_communication.tex:724-736`, `07_public_setup.tex:60-112,127-142`,
and `05_binary_transport.tex:20-42`.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceGeneratedPrelaunchDownCohortInterval

open ConstructorDimensions BootstrapDimensions
open ReferenceInitializationRun ReferencePrelaunchFollower
open ReferenceGeneratedPrelaunchDownPrefix ReferenceGeneratedPrelaunchDownCohort
open ReferenceGeneratedPrelaunchDownHistoricalBirth
open ReferenceGeneratedPrelaunchDownActiveBridge
open ReferenceGeneratedPrelaunchDownInactiveBridge
open ReferenceGeneratedPrelaunchDownCohortStep
open ReferenceGeneratedDownBatchCalendar AffineBatchDecoder AffineChannelLaw
open scoped Classical

variable {p : ConstructorDimensions.Parameters}

/-- The actual activated ordinary state at a boundary. Strict boundaries read
the existing generated prefix; `T` reads the actual terminal pair. -/
def sourcePrelaunchDownActualCohort
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) :
    Option (Activation p × ReferencePrelaunchFollower.State p rate.eta) := by
  classical
  exact if h : u < p.T then
    match source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨u, h⟩ with
    | .inl (.inl active) => some (active.val.2.1, active.val.2.2.2)
    | .inl (.inr _) => none
    | .inr stopped =>
        (stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i)).map
          (fun a => (a, stopped.val.2))
  else
    let terminal := source_prelaunch_down_terminal rate rewards C_star C_h z i
    (terminal.1.activation (ActualReferenceInitializationBlock.refFollower i)).map
      (fun a => (a, terminal.2))

/-- The actual test census at a boundary, using the terminal census at `T`. -/
def sourcePrelaunchDownTestsAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (_hu : u ≤ p.T) :
    List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) := by
  classical
  exact if h : u < p.T then
    source_prelaunch_down_prefix_tests rate rewards C_star C_h z i ⟨u, h⟩
  else sourcePrelaunchDownTests rate rewards C_star C_h z i

/-- The manuscript's two candidate flags for one actual DOWN test. -/
def sourcePrelaunchDownCandidateFlag
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p))
    (test : ReferenceGeneratedDownBatchCalendar.ExecutedTest p) : Prop × Prop :=
  (test.sent ≠ some w, AffineChannelLaw.affineHash test.sample w = 1)

@[simp] theorem sourcePrelaunchDownActualCohort_of_active
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) (hlt : u < p.T)
    (active : ActiveProjection p i u
      (sourceReferenceInput rate rewards C_star C_h z).row
      (Nat.le_of_lt hlt) (sourceReferenceInput rate rewards C_star C_h z)
      (roundBlockIndex p ⟨u, hlt⟩))
    (hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨u, hlt⟩ =
      .inl (.inl active)) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu =
      some (active.val.2.1, active.val.2.2.2) := by
  simp only [sourcePrelaunchDownActualCohort, dif_pos hlt, hprefix]
  rfl

@[simp] theorem sourcePrelaunchDownActualCohort_of_inactive
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) (hlt : u < p.T)
    (inactive : InactiveProjection p i u (Nat.le_of_lt hlt)
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p ⟨u, hlt⟩))
    (hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨u, hlt⟩ =
      .inl (.inr inactive)) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu = none := by
  simp only [sourcePrelaunchDownActualCohort, dif_pos hlt, hprefix]

@[simp] theorem sourcePrelaunchDownActualCohort_of_stopped
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) (hlt : u < p.T)
    (stopped : StoppedProjection p
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p ⟨u, hlt⟩) i)
    (hprefix : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨u, hlt⟩ =
      .inr stopped) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu =
      (stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i)).map
        (fun a => (a, stopped.val.2)) := by
  simp only [sourcePrelaunchDownActualCohort, dif_pos hlt, hprefix]
  rfl

@[simp] theorem sourcePrelaunchDownActualCohort_at_terminal
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (hu : p.T ≤ p.T) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i p.T hu =
      ((source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
        (ActualReferenceInitializationBlock.refFollower i)).map
          (fun a => (a, (source_prelaunch_down_terminal rate rewards C_star C_h z i).2)) := by
  simp [sourcePrelaunchDownActualCohort]

@[simp] theorem sourcePrelaunchDownTestsAt_prefix
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) (hlt : u < p.T) :
    sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u hu =
      source_prelaunch_down_prefix_tests rate rewards C_star C_h z i ⟨u, hlt⟩ := by
  simp [sourcePrelaunchDownTestsAt, hlt]

@[simp] theorem sourcePrelaunchDownTestsAt_terminal
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (hu : p.T ≤ p.T) :
    sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T hu =
      sourcePrelaunchDownTests rate rewards C_star C_h z i := by
  simp [sourcePrelaunchDownTestsAt]

private theorem run_completed_le (x : ReferenceInitializationRun.Input p) :
    ∀ q, (ReferenceInitializationRun.run x q).completed ≤ q := by
  intro q
  induction q with
  | zero => simp [ReferenceInitializationRun.run_zero, ReferenceInitializationRun.initial]
  | succ q ih =>
      by_cases hc : (ReferenceInitializationRun.run x q).crossing.isSome = true
      · rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_crossing x _ hc]
        exact ih.trans (Nat.le_succ q)
      · have hNone : (ReferenceInitializationRun.run x q).crossing = none := by
          cases hcross : (ReferenceInitializationRun.run x q).crossing <;> simp_all
        by_cases hExhausted : n_boot p ≤ (ReferenceInitializationRun.run x q).completed
        · rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_exhausted x _ hExhausted]
          exact ih.trans (Nat.le_succ q)
        · have hAvailable : (ReferenceInitializationRun.run x q).completed < n_boot p :=
            Nat.lt_of_not_ge hExhausted
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hNone hAvailable]
          change (ReferenceInitializationRun.run x q).completed + 1 ≤ q + 1
          exact Nat.succ_le_succ ih

private theorem stopped_elapsed_le
    (x : ReferenceInitializationRun.Input p) (r : Fin p.T)
    (i : Fin (p.m - 1))
    (stopped : StoppedProjection p x (roundBlockIndex p r) i) :
    ReferenceInitializationRun.elapsed p stopped.val.1.completed ≤ r.val := by
  have hBoundary : stopped.val.1 = ReferenceInitializationRun.run x
      (roundBlockIndex p r).val := stopped.property.2.1
  have hCompleted : stopped.val.1.completed ≤ (roundBlockIndex p r).val := by
    rw [hBoundary]
    exact run_completed_le x _
  have hBlockStart : (roundBlockIndex p r).val * B_boot p ≤ r.val :=
    ((mem_calendarBlock_iff p (roundBlockIndex p r) r).mp
      (round_mem_quotient_block p r)).1
  calc
    ReferenceInitializationRun.elapsed p stopped.val.1.completed ≤
        ReferenceInitializationRun.elapsed p (roundBlockIndex p r).val :=
      ReferenceInitializationRun.elapsed_mono p hCompleted
    _ ≤ r.val := by
      change min p.T ((roundBlockIndex p r).val * B_boot p) ≤ r.val
      exact (Nat.min_le_right _ _).trans hBlockStart

private theorem actualState_of_birthAt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (beta : ℕ) (hBeta : beta ≤ p.T) (k : ℕ)
    (hBirth : birthAt rate rewards C_star C_h z i beta hBeta k) :
    ∃ a state,
      sourcePrelaunchDownActualCohort rate rewards C_star C_h z i beta hBeta =
        some (a, state) ∧
      state.downBatch.completed.length = k ∧ state.downBatch.pending = [] ∧
      bankBirth a state.downBatch = some beta := by
  classical
  by_cases hlt : beta < p.T
  · cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i ⟨beta, hlt⟩ with
    | inl branch =>
        cases branch with
        | inl active =>
            have hBirth' :
                active.val.2.2.2.downBatch.completed.length = k ∧
                  active.val.2.2.2.downBatch.pending = [] ∧
                  bankBirth active.val.2.1 active.val.2.2.2.downBatch = some beta := by
              simpa only [birthAt, dif_pos hlt, hp] using hBirth
            rcases hBirth' with ⟨hk, hpending, hbank⟩
            exact ⟨active.val.2.1, active.val.2.2.2,
              sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h z i
                beta hBeta hlt active hp, hk, hpending, hbank⟩
        | inr _ =>
            have hFalse : False := by simpa only [birthAt, dif_pos hlt, hp] using hBirth
            exact hFalse.elim
    | inr stopped =>
        have hBirth' :
            ∃ a, stopped.val.1.activation
                (ActualReferenceInitializationBlock.refFollower i) = some a ∧
              stopped.val.2.downBatch.completed.length = k ∧
              stopped.val.2.downBatch.pending = [] ∧
              bankBirth a stopped.val.2.downBatch = some beta := by
          simpa only [birthAt, dif_pos hlt, hp] using hBirth
        rcases hBirth' with ⟨a, ha, hk, hpending, hbank⟩
        refine ⟨a, stopped.val.2, ?_, hk, hpending, hbank⟩
        rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
          beta hBeta hlt stopped hp, ha]
        rfl
  · have hEq : beta = p.T := by omega
    subst beta
    have hBirth' :
        ∃ a,
          (ReferenceInitializationRun.output
            (sourceReferenceInput rate rewards C_star C_h z)).activation
              (ActualReferenceInitializationBlock.refFollower i) = some a ∧
          (ReferenceInitializationRun.ordinary
            (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed.length = k ∧
          (ReferenceInitializationRun.ordinary
            (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch.pending = [] ∧
          bankBirth a (ReferenceInitializationRun.ordinary
            (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch = some p.T := by
      simpa only [birthAt, dite_eq_right (Nat.lt_irrefl p.T)] using hBirth
    rcases hBirth' with ⟨a, ha, hk, hpending, hbank⟩
    refine ⟨a, ReferenceInitializationRun.ordinary
      (sourceReferenceInput rate rewards C_star C_h z)
      (ReferenceInitializationRun.output (sourceReferenceInput rate rewards C_star C_h z))
      (ActualReferenceInitializationBlock.refFollower i), ?_, hk, hpending, hbank⟩
    rw [sourcePrelaunchDownActualCohort_at_terminal]
    simp [source_prelaunch_down_terminal, ha]

private theorem actual_endpoint_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T)
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i n hn =
      some (a, state)) :
    ∃ beta, ∃ hBeta : beta ≤ p.T, beta ≤ n ∧
      bankBirth a state.downBatch = some beta ∧
      birthAt rate rewards C_star C_h z i beta hBeta state.downBatch.completed.length ∧
      ∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta := by
  classical
  by_cases hlt : n < p.T
  · let r : Fin p.T := ⟨n, hlt⟩
    cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
        cases branch with
        | inl active =>
            have hActual' :
                some (active.val.2.1, active.val.2.2.2) = some (a, state) := by
              rw [sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h z i
                n hn hlt active hp] at hActual
              exact hActual
            obtain ⟨ha, hstate⟩ := Prod.mk.inj (Option.some.inj hActual')
            subst a
            subst state
            have hh := source_prelaunch_down_current_birth_history
              rate rewards C_star C_h z i r
            rw [hp] at hh
            rcases hh with ⟨beta, hBeta, hbound, hbank, hBirth, hUnique⟩
            exact ⟨beta, hBeta, hbound, hbank, hBirth, hUnique⟩
        | inr _ =>
            have : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i n hn = none := by
              simp [sourcePrelaunchDownActualCohort, hlt, r, hp]
            rw [this] at hActual
            cases hActual
    | inr stopped =>
        have hActivation :
            stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i) = some a := by
          have hMap :
              (stopped.val.1.activation
                (ActualReferenceInitializationBlock.refFollower i)).map
                  (fun a' => (a', stopped.val.2)) = some (a, state) := by
            rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
              n hn hlt stopped hp] at hActual
            exact hActual
          cases ha : stopped.val.1.activation
              (ActualReferenceInitializationBlock.refFollower i) with
          | none => simp [ha] at hMap
          | some a' =>
              simp only [ha, Option.map_some] at hMap
              have hValue := (Prod.mk.inj (Option.some.inj hMap)).1
              simpa [hValue] using ha
        have hState : stopped.val.2 = state := by
          have hMap :
              (stopped.val.1.activation
                (ActualReferenceInitializationBlock.refFollower i)).map
                  (fun a' => (a', stopped.val.2)) = some (a, state) := by
            rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
              n hn hlt stopped hp] at hActual
            exact hActual
          rw [hActivation] at hMap
          simp only [Option.map_some] at hMap
          exact (Prod.mk.inj (Option.some.inj hMap)).2
        have hh := source_prelaunch_down_current_birth_history
          rate rewards C_star C_h z i r
        rw [hp] at hh
        rcases hh with ⟨_, hHistory⟩
        obtain ⟨beta, hBeta, hBoundElapsed, hbank, hBirth, hUnique⟩ :=
          hHistory a hActivation
        have hbank' : bankBirth a state.downBatch = some beta := by
          simpa [← hState] using hbank
        have hBirth' : birthAt rate rewards C_star C_h z i beta hBeta
            state.downBatch.completed.length := by
          simpa [← hState] using hBirth
        have hUnique' : ∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta := by
          intro beta' hb
          apply hUnique beta'
          simpa [← hState] using hb
        exact ⟨beta, hBeta,
          hBoundElapsed.trans (stopped_elapsed_le (sourceReferenceInput rate rewards C_star C_h z)
            r i stopped), hbank', hBirth', hUnique'⟩
  · have hnEq : n = p.T := by omega
    subst n
    have hTerm :
        ((source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
          (ActualReferenceInitializationBlock.refFollower i)).map
            (fun a' => (a', (source_prelaunch_down_terminal rate rewards C_star C_h z i).2)) =
          some (a, state) := by
      rw [sourcePrelaunchDownActualCohort_at_terminal] at hActual
      exact hActual
    have hActivation :
        (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
          (ActualReferenceInitializationBlock.refFollower i) = some a := by
      cases ha : (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
          (ActualReferenceInitializationBlock.refFollower i) with
      | none => simp [ha] at hTerm
      | some a' =>
              simp only [ha, Option.map_some] at hTerm
              have hValue := (Prod.mk.inj (Option.some.inj hTerm)).1
              simpa [hValue] using ha
    have hState : (source_prelaunch_down_terminal rate rewards C_star C_h z i).2 = state := by
      rw [hActivation] at hTerm
      simp only [Option.map_some] at hTerm
      exact (Prod.mk.inj (Option.some.inj hTerm)).2
    have hh := source_prelaunch_down_terminal_birth_history rate rewards C_star C_h z i
    dsimp only at hh
    obtain ⟨beta, hBeta, hElapsed, hbank, hBirth, hUnique⟩ := hh a hActivation
    have hElapsedT :
        ReferenceInitializationRun.elapsed p
            (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.completed ≤ p.T :=
      ReferenceInitializationRun.elapsed_le_T p
        (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.completed
    have hbank' : bankBirth a state.downBatch = some beta := by
      simpa [← hState] using hbank
    have hBirth' : birthAt rate rewards C_star C_h z i beta hBeta
        state.downBatch.completed.length := by
      simpa [← hState] using hBirth
    have hUnique' : ∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta := by
      intro beta' hb
      apply hUnique beta'
      simpa [← hState] using hb
    exact ⟨beta, hBeta, hElapsed.trans hElapsedT, hbank', hBirth', hUnique'⟩

private theorem active_actual_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (active : ActiveProjection p i r.val
      (sourceReferenceInput rate rewards C_star C_h z).row r.isLt.le
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inl active)) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i (r.val + 1) hNext =
      some (active.val.2.1,
        ReferencePrelaunchFollower.step i
          (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r
          (ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical
              (sourceReferenceInput rate rewards C_star C_h z)
              active.val.1.val active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r)
          active.val.2.2.2) ∧
    sourcePrelaunchDownTestsAt rate rewards C_star C_h z i (r.val + 1) hNext =
      source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
        (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
  classical
  let x := sourceReferenceInput rate rewards C_star C_h z
  let a := active.val.2.1
  let state := active.val.2.2.2
  let own := ReferenceInitializationRun.ownEntry
    (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
    (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)) r
  by_cases hStrict : r.val + 1 < p.T
  · let rn : Fin p.T := ⟨r.val + 1, hStrict⟩
    have hs := source_prelaunch_down_active_successor
      rate rewards C_star C_h z i r hStrict
    rw [hPrefix] at hs
    rcases hs with ⟨_, hBoundaryActivation, _, hTests, hNextBranch⟩
    cases hpNext : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
    | inl branch =>
        cases branch with
        | inl nextActive =>
            rw [hpNext] at hNextBranch
            rcases hNextBranch with ⟨_, _, hActivationNext, hStateNext⟩
            constructor
            · simp only [sourcePrelaunchDownActualCohort, dif_pos hStrict, rn, hpNext]
              rw [hActivationNext, hStateNext]
              rfl
            · rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
                (r.val + 1) hNext hStrict]
              simpa [rn] using hTests
        | inr _ =>
            rw [hpNext] at hNextBranch
            exact hNextBranch.elim
    | inr nextStopped =>
        rw [hpNext] at hNextBranch
        rcases hNextBranch with ⟨_, hNextBoundary, hStateNext⟩
        have hActivation : nextStopped.val.1.activation
            (ActualReferenceInitializationBlock.refFollower i) = some a :=
          (congrArg (fun b : ReferenceInitializationRun.Boundary p => b.activation
            (ActualReferenceInitializationBlock.refFollower i)) hNextBoundary).trans
              hBoundaryActivation
        constructor
        · simp only [sourcePrelaunchDownActualCohort, dif_pos hStrict, rn, hpNext]
          rw [hActivation, hStateNext]
          dsimp [a]
          rfl
        · rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
            (r.val + 1) hNext hStrict]
          simpa [rn] using hTests
  · have hLast : r.val + 1 = p.T := by omega
    have hs := source_prelaunch_down_active_terminal
      rate rewards C_star C_h z i r hLast
    rw [hPrefix] at hs
    rcases hs with ⟨_, _, _, _, _, _, hActivation, _, _, hState, hTests, _⟩
    constructor
    · have hTerminalActual :
          sourcePrelaunchDownActualCohort rate rewards C_star C_h z i p.T (Nat.le_refl p.T) =
            some (a, ReferencePrelaunchFollower.step i x.row a r own state) := by
        rw [sourcePrelaunchDownActualCohort_at_terminal]
        simp [hActivation, hState]
        rfl
      simpa [hLast] using hTerminalActual
    · have hTerminalTests :
          sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T (Nat.le_refl p.T) =
            source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r ++
              (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
        rw [sourcePrelaunchDownTestsAt_terminal]
        exact hTests
      simpa [hLast] using hTerminalTests

private theorem stopped_actual_successor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (stopped : StoppedProjection p
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r) i)
    (hPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inr stopped) :
    sourcePrelaunchDownActualCohort rate rewards C_star C_h z i (r.val + 1) hNext =
      sourcePrelaunchDownActualCohort rate rewards C_star C_h z i r r.isLt.le ∧
    sourcePrelaunchDownTestsAt rate rewards C_star C_h z i (r.val + 1) hNext =
      sourcePrelaunchDownTestsAt rate rewards C_star C_h z i r r.isLt.le ∧
    source_prelaunch_down_current_test rate rewards C_star C_h z i r = none := by
  classical
  have hs := source_prelaunch_down_stopped_to_terminal
    rate rewards C_star C_h z i r
  rw [hPrefix] at hs
  rcases hs with ⟨hTerminal, _, hTestsTerminal, hCurrentNone, hLater⟩
  by_cases hStrict : r.val + 1 < p.T
  · let rn : Fin p.T := ⟨r.val + 1, hStrict⟩
    obtain ⟨stoppedNext, hNextPrefix, hSame, hTestsSame, _, _⟩ :=
      hLater rn (by dsimp [rn]; omega)
    constructor
    · have hActualNext := sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
        (r.val + 1) hNext hStrict stoppedNext (by simpa [rn] using hNextPrefix)
      have hActualCurrent := sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
        r.val r.isLt.le r.isLt stopped hPrefix
      have hMaps :
          Option.map (fun a => (a, stoppedNext.val.2))
              (stoppedNext.val.1.activation (ActualReferenceInitializationBlock.refFollower i)) =
            Option.map (fun a => (a, stopped.val.2))
              (stopped.val.1.activation (ActualReferenceInitializationBlock.refFollower i)) := by
        rw [hSame]
      exact hActualNext.trans (hMaps.trans hActualCurrent.symm)
    · constructor
      · rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
          (r.val + 1) hNext hStrict,
          sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
            r.val r.isLt.le r.isLt]
        exact hTestsSame
      · exact hCurrentNone
  · have hLast : r.val + 1 = p.T := by omega
    constructor
    · have hActualTerminal := sourcePrelaunchDownActualCohort_at_terminal
        rate rewards C_star C_h z i (Nat.le_refl p.T)
      have hActualCurrent := sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
        r.val r.isLt.le r.isLt stopped hPrefix
      rw [← hTerminal] at hActualTerminal
      have hActualEq := hActualTerminal.trans hActualCurrent.symm
      simpa [hLast] using hActualEq
    · constructor
      · have hTestsTerminal' := sourcePrelaunchDownTestsAt_terminal
          rate rewards C_star C_h z i (Nat.le_refl p.T)
        have hTestsEq := hTestsTerminal'.trans hTestsTerminal.symm
        simpa [hLast] using hTestsEq
      · exact hCurrentNone

private theorem completed_flatten_length
    {α : Type} (q : ℕ) (batches : List (List α))
    (hbatch : ∀ batch ∈ batches, batch.length = q) :
    batches.flatten.length = q * batches.length := by
  induction batches with
  | nil => simp
  | cons batch batches ih =>
      have hhead : batch.length = q := hbatch batch (by simp)
      have htail : ∀ c ∈ batches, c.length = q := by
        intro c hc
        exact hbatch c (List.mem_cons_of_mem _ hc)
      have hrest := ih htail
      rw [List.flatten_cons, List.length_append, hhead, hrest,
        List.length_cons, Nat.mul_succ]
      omega

private theorem actual_pending_census
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T)
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu =
      some (a, state)) :
    let tests := sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u hu
    tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
        AffineBatchDecoder.collected state.downBatch ∧
      state.downBatch.pending =
        (tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry).drop
          (AffineBatchDecoder.quota p * state.downBatch.completed.length) ∧
      (∀ batch ∈ state.downBatch.completed,
        batch.length = AffineBatchDecoder.quota p) ∧
      state.downBatch.pending.length < AffineBatchDecoder.quota p := by
  classical
  by_cases hlt : u < p.T
  · let r : Fin p.T := ⟨u, hlt⟩
    cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
        cases branch with
        | inl active =>
            have hPair : some (active.val.2.1, active.val.2.2.2) = some (a, state) := by
              rw [sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h z i
                u hu hlt active hp] at hActual
              exact hActual
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hPair)
            have hc := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
            rw [hp] at hc
            simpa [sourcePrelaunchDownTestsAt, hlt, r, hp] using hc
        | inr _ =>
            have hh : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu = none := by
              exact sourcePrelaunchDownActualCohort_of_inactive rate rewards C_star C_h z i
                u hu hlt _ hp
            rw [hh] at hActual
            cases hActual
    | inr stopped =>
        have hMap :
            (stopped.val.1.activation
              (ActualReferenceInitializationBlock.refFollower i)).map
                (fun a' => (a', stopped.val.2)) = some (a, state) := by
          rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
            u hu hlt stopped hp] at hActual
          exact hActual
        cases ha : stopped.val.1.activation
            (ActualReferenceInitializationBlock.refFollower i) with
        | none => simp [ha] at hMap
        | some a' =>
            simp only [ha, Option.map_some] at hMap
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hMap)
            have hc := source_prelaunch_down_prefix_census rate rewards C_star C_h z i r
            rw [hp] at hc
            simpa [sourcePrelaunchDownTestsAt, hlt, r, hp] using hc
  · have huEq : u = p.T := by omega
    subst u
    have hTerm :
        ((source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
          (ActualReferenceInitializationBlock.refFollower i)).map
            (fun a' => (a', (source_prelaunch_down_terminal rate rewards C_star C_h z i).2)) =
          some (a, state) := by
      rw [sourcePrelaunchDownActualCohort_at_terminal] at hActual
      exact hActual
    have hAct : (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
        (ActualReferenceInitializationBlock.refFollower i) = some a := by
      cases ha : (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
          (ActualReferenceInitializationBlock.refFollower i) with
      | none => simp [ha] at hTerm
      | some a' =>
          simp only [ha, Option.map_some] at hTerm
          have hActivationValue := (Prod.mk.inj (Option.some.inj hTerm)).1
          simpa [hActivationValue] using ha
    have hState : (source_prelaunch_down_terminal rate rewards C_star C_h z i).2 = state := by
      rw [hAct] at hTerm
      simp only [Option.map_some] at hTerm
      exact (Prod.mk.inj (Option.some.inj hTerm)).2
    have hOrd :
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
          (ActualReferenceInitializationBlock.refFollower i)) = state := by
      change (source_prelaunch_down_terminal rate rewards C_star C_h z i).2 = state
      exact hState
    have hc := source_prelaunch_down_cohorts rate rewards C_star C_h z i
    dsimp only at hc
    rcases hc with ⟨hCollected, hPending, hCompleted, hShort⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · have hCollected' := hCollected
      rw [hOrd] at hCollected'
      simpa [sourcePrelaunchDownTestsAt_terminal] using hCollected'
    · have hPending' := hPending
      rw [hOrd] at hPending'
      simpa [sourcePrelaunchDownTestsAt_terminal] using hPending'
    · intro batch hBatch
      have hBatch' : batch ∈
          (ReferenceInitializationRun.ordinary
            (sourceReferenceInput rate rewards C_star C_h z)
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed := by
        simpa [sourceReferenceInput, hOrd] using hBatch
      obtain ⟨j, hj, hEntry⟩ := List.mem_iff_getElem.mp hBatch'
      have hAt := hCompleted j hj
      have hEntry' :
          (ReferenceInitializationRun.ordinary
            (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate))
            (ActualReferenceInitializationBlock.refFollower i)).downBatch.completed[j] = batch := by
        exact hEntry
      rw [hEntry'] at hAt
      exact hAt.2
    · simpa [hOrd] using hShort

private theorem actual_tests_time_lt
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T)
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu =
      some (a, state)) :
    ∀ test ∈ sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u hu,
      test.time.val < u := by
  classical
  intro test hTest
  by_cases hlt : u < p.T
  · let r : Fin p.T := ⟨u, hlt⟩
    cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
    | inl branch =>
        cases branch with
        | inl active =>
            have hmem : test ∈
                (List.ofFn (fun v : Fin r.val => v)).filterMap
                  (fun v => ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
                    (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1
                    (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) v)
                    (active.val.2.2.1 v)) := by
              rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i u hu hlt]
                at hTest
              simpa only [source_prelaunch_down_prefix_tests, r, hp] using hTest
            rcases List.mem_filterMap.mp hmem with ⟨v, _, hSome⟩
            have hTime : test.time =
                ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) v := by
              unfold ReferenceGeneratedPrelaunchDownCohort.prelaunchTest at hSome
              split_ifs at hSome with hSelected
              · have hEq := Option.some.inj hSome
                rw [← hEq]
            have hv : (ReferencePrelaunchFollower.calendar (Nat.le_of_lt r.isLt) v).val < u := by
              simpa [ReferencePrelaunchFollower.calendar, r] using v.isLt
            simpa [hTime] using hv
        | inr _ =>
            rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i u hu hlt]
              at hTest
            have hEmpty : source_prelaunch_down_prefix_tests rate rewards C_star C_h z i r = [] := by
              simp only [source_prelaunch_down_prefix_tests, r, hp]
            simp only [hEmpty, source_prelaunch_down_current_test, r, hp,
              List.nil_append] at hTest
            cases hTest
    | inr stopped =>
        have hs := source_prelaunch_down_stopped_to_terminal
          rate rewards C_star C_h z i r
        rw [hp] at hs
        rcases hs with ⟨hTerminal, _, hTests, _, _⟩
        rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i u hu hlt]
          at hTest
        have hmem : test ∈ sourcePrelaunchDownTests rate rewards C_star C_h z i := by
          rw [hTests] at hTest
          exact hTest
        obtain ⟨_, _, _, hTestTime, _⟩ :=
          source_prelaunch_down_test_provenance rate rewards C_star C_h z i test hmem
        have hBoundaryElapsed := stopped_elapsed_le
          (sourceReferenceInput rate rewards C_star C_h z) r i stopped
        have hOutputElapsed : ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (sourceReferenceInput rate rewards C_star C_h z)).completed ≤ u := by
          have hEq : ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z)).completed =
              ReferenceInitializationRun.elapsed p stopped.val.1.completed := by
            calc
              _ = ReferenceInitializationRun.elapsed p
                    (source_prelaunch_down_terminal rate rewards C_star C_h z i).1.completed := rfl
              _ = ReferenceInitializationRun.elapsed p stopped.val.1.completed :=
                congrArg (fun b : ReferenceInitializationRun.Boundary p =>
                  ReferenceInitializationRun.elapsed p b.completed)
                  (congrArg Prod.fst hTerminal).symm
          exact hEq ▸ hBoundaryElapsed
        exact lt_of_lt_of_le hTestTime hOutputElapsed
  · have huEq : u = p.T := by omega
    subst u
    have hmem : test ∈ sourcePrelaunchDownTests rate rewards C_star C_h z i := by
      rw [sourcePrelaunchDownTestsAt_terminal] at hTest
      exact hTest
    obtain ⟨_, _, _, hTestTime, _⟩ :=
      source_prelaunch_down_test_provenance rate rewards C_star C_h z i test hmem
    exact lt_of_lt_of_le hTestTime
      (ReferenceInitializationRun.elapsed_le_T p
        (ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).completed)

private theorem initial_bank_birth (a : Activation p)
    (eta : ReferencePrelaunchFollower.LearningRate) (u : ℕ)
    (hval : a.val = u + 2) :
    bankBirth a (ReferencePrelaunchFollower.initial p eta).downBatch = some (u + 1) := by
  simp only [ReferencePrelaunchFollower.initial, AffineBatchDecoder.initial,
    bankBirth, List.isEmpty_nil, ite_true]
  congr 1
  omega

private theorem inactive_actual_successor_birth
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (inactive : InactiveProjection p i r.val r.isLt.le
      (sourceReferenceInput rate rewards C_star C_h z) (roundBlockIndex p r))
    (hPrefix : source_prelaunch_down_prefix rate rewards C_star C_h z i r =
      .inl (.inr inactive))
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hNextState : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
      (r.val + 1) hNext = some (a, state)) :
    bankBirth a state.downBatch = some (r.val + 1) := by
  classical
  by_cases hStrict : r.val + 1 < p.T
  · let rn : Fin p.T := ⟨r.val + 1, hStrict⟩
    have hs := source_prelaunch_down_inactive_successor
      rate rewards C_star C_h z i r hStrict
    dsimp only at hs
    rw [hPrefix] at hs
    dsimp only [rn] at hs
    cases hpNext : source_prelaunch_down_prefix rate rewards C_star C_h z i rn with
    | inl branch =>
        cases branch with
        | inl nextActive =>
            rw [hpNext] at hs
            rcases hs with ⟨_, _, hCase⟩
            rcases hCase with ⟨_, hExists⟩
            let aBirth := Classical.choose hExists
            have hBirthData := Classical.choose_spec hExists
            rcases hBirthData with ⟨hEqA, _, _, hval, hInitial, _, _⟩
            have hActual :
                some (nextActive.val.2.1, nextActive.val.2.2.2) = some (a, state) := by
              rw [sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h z i
                (r.val + 1) hNext hStrict nextActive (by simpa [rn] using hpNext)] at hNextState
              exact hNextState
            obtain ⟨hAct, hState⟩ := Prod.mk.inj (Option.some.inj hActual)
            have hval' : nextActive.val.2.1.val = r.val + 2 := by
              calc
                nextActive.val.2.1.val = aBirth.val := congrArg Subtype.val hEqA
                _ = r.val + 2 := hval
            have hAct' : nextActive.val.2.1 = a := hAct
            have hInitial' : state = ReferencePrelaunchFollower.initial p rate.eta := by
              have hInitial'' := hState.symm.trans hInitial
              simpa [sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
                using hInitial''
            rw [← hAct', hInitial']
            exact initial_bank_birth _ rate.eta r.val hval'
        | inr nextInactive =>
            have hNone : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
                (r.val + 1) hNext = none := by
              exact sourcePrelaunchDownActualCohort_of_inactive rate rewards C_star C_h z i
                (r.val + 1) hNext hStrict nextInactive (by simpa [rn] using hpNext)
            rw [hNone] at hNextState
            cases hNextState
    | inr nextStopped =>
        rw [hpNext] at hs
        rcases hs with ⟨_, _, hCase⟩
        rcases hCase with ⟨_, hExists⟩
        let aBirth := Classical.choose hExists
        have hBirthData := Classical.choose_spec hExists
        rcases hBirthData with ⟨_, hActivation, hval, hInitial, _⟩
        have hActual :
            (nextStopped.val.1.activation
              (ActualReferenceInitializationBlock.refFollower i)).map
                (fun a' => (a', nextStopped.val.2)) = some (a, state) := by
          rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
            (r.val + 1) hNext hStrict nextStopped (by simpa [rn] using hpNext)] at hNextState
          exact hNextState
        rw [hActivation] at hActual
        simp only [Option.map_some] at hActual
        obtain ⟨hAct, hState⟩ := Prod.mk.inj (Option.some.inj hActual)
        have hval' : a.val = r.val + 2 := by
          calc
            a.val = aBirth.val := congrArg Subtype.val hAct.symm
            _ = r.val + 2 := hval
        have hInitial' : state = ReferencePrelaunchFollower.initial p rate.eta := by
          have hInitial'' := hState.symm.trans hInitial
          simpa [sourceReferenceInput, ActualReferenceInitializationBlock.referenceInput]
            using hInitial''
        rw [hInitial']
        exact initial_bank_birth a rate.eta r.val hval'
  · have hLast : r.val + 1 = p.T := by omega
    rcases r with ⟨rVal, hRVal⟩
    have hRValEq : rVal = p.T - 1 := by
      have hBound : rVal + 1 ≤ p.T := by simpa using hNext
      have hNot : ¬rVal + 1 < p.T := by simpa using hStrict
      omega
    subst rVal
    let rLast : Fin p.T := ⟨p.T - 1, by have := T_pos p; omega⟩
    change source_prelaunch_down_prefix rate rewards C_star C_h z i rLast =
      .inl (.inr inactive) at hPrefix
    have hs := source_prelaunch_down_inactive_terminal_handoff
      rate rewards C_star C_h z i
    dsimp only at hs
    rw [hPrefix] at hs
    rcases hs with ⟨_, _, _, hTerminalData⟩
    have hTerminal :
        ((source_prelaunch_down_terminal rate rewards C_star C_h z i).1.activation
          (ActualReferenceInitializationBlock.refFollower i)).map
            (fun a' => (a', (source_prelaunch_down_terminal rate rewards C_star C_h z i).2)) =
          some (a, state) := by
      have hEqT : (p.T - 1) + 1 = p.T := by omega
      simpa only [hEqT, sourcePrelaunchDownActualCohort_at_terminal] using hNextState
    rcases hTerminalData with hNone | ⟨aBirth, hActivation, hval, hInitial, _⟩
    · rcases hNone with ⟨hActivationNone, _, _, _, _⟩
      change ((ReferenceInitializationRun.output
        (sourceReferenceInput rate rewards C_star C_h z)).activation
          (ActualReferenceInitializationBlock.refFollower i)).map
            (fun a' => (a', ReferenceInitializationRun.ordinary
              (sourceReferenceInput rate rewards C_star C_h z)
              (ReferenceInitializationRun.output
                (sourceReferenceInput rate rewards C_star C_h z))
              (ActualReferenceInitializationBlock.refFollower i))) = some (a, state) at hTerminal
      rw [hActivationNone] at hTerminal
      simp at hTerminal
    · have hActual :
          some (aBirth, ReferencePrelaunchFollower.initial p rate.eta) = some (a, state) := by
        change ((ReferenceInitializationRun.output
          (sourceReferenceInput rate rewards C_star C_h z)).activation
            (ActualReferenceInitializationBlock.refFollower i)).map
              (fun a' => (a', ReferenceInitializationRun.ordinary
                (sourceReferenceInput rate rewards C_star C_h z)
                (ReferenceInitializationRun.output
                  (sourceReferenceInput rate rewards C_star C_h z))
                (ActualReferenceInitializationBlock.refFollower i))) = some (a, state) at hTerminal
        rw [hActivation, hInitial] at hTerminal
        simp only [Option.map_some] at hTerminal
        exact hTerminal
      obtain ⟨hAct, hState⟩ := Prod.mk.inj (Option.some.inj hActual)
      have hvalA : a.val = p.T + 1 := by simpa [hAct] using hval
      have hval' : a.val = (p.T - 1) + 2 := by
        have hT := T_pos p
        omega
      rw [← hState]
      exact initial_bank_birth a rate.eta (p.T - 1) hval'

private theorem actual_cohort_predecessor
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (r : Fin p.T) (hNext : r.val + 1 ≤ p.T)
    (beta : ℕ) (hBeta : beta ≤ r.val)
    (a : Activation p) (nextState : ReferencePrelaunchFollower.State p rate.eta)
    (hNextState : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
      (r.val + 1) hNext = some (a, nextState))
    (hBirthNext : bankBirth a nextState.downBatch = some beta) :
    ∃ state,
      sourcePrelaunchDownActualCohort rate rewards C_star C_h z i r.val r.isLt.le =
        some (a, state) ∧
      state.downBatch.completed = nextState.downBatch.completed ∧
      bankBirth a state.downBatch = some beta ∧
      sourcePrelaunchDownTestsAt rate rewards C_star C_h z i (r.val + 1) hNext =
        sourcePrelaunchDownTestsAt rate rewards C_star C_h z i r.val r.isLt.le ++
          (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
  classical
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hTransition := active_actual_successor
            rate rewards C_star C_h z i r hNext active hp
          obtain ⟨hActiveNext, hTestsNext⟩ := hTransition
          have hState : nextState =
              ReferencePrelaunchFollower.step i
                (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r
                (ReferenceInitializationRun.ownEntry
                  (ReferenceInitializationRun.physical
                    (sourceReferenceInput rate rewards C_star C_h z)
                    active.val.1.val active.val.1.property.1)
                  (PublicDiscreteDraws.followerPlayer p.two_le_m
                    (ActualReferenceInitializationBlock.refFollower i)) r)
                active.val.2.2.2 := by
            have hEq := hNextState.symm.trans hActiveNext
            exact (Prod.mk.inj (Option.some.inj hEq)).2
          have hActivation : a = active.val.2.1 := by
            have hEq := hNextState.symm.trans hActiveNext
            exact (Prod.mk.inj (Option.some.inj hEq)).1
          let x := sourceReferenceInput rate rewards C_star C_h z
          let state := active.val.2.2.2
          let own := ReferenceInitializationRun.ownEntry
            (ReferenceInitializationRun.physical x active.val.1.val active.val.1.property.1)
            (PublicDiscreteDraws.followerPlayer p.two_le_m
              (ActualReferenceInitializationBlock.refFollower i)) r
          let tr := ReferencePrelaunchFollower.traceAt i x.row active.val.2.1 r own
          have hCensus := source_prelaunch_down_active_step_census
            rate rewards C_star C_h z i r
          rw [hp] at hCensus
          rcases hCensus with
            ⟨_, hShort, _, _, _, _, _, _, _, hGap, hOrdinal, hSubStep, hQuotaStep, _⟩
          let bank := state.downBatch
          let nextBank := (ReferencePrelaunchFollower.step i x.row active.val.2.1 r own state).downBatch
          have hBirthStep : bankBirth active.val.2.1 nextBank = some beta := by
            rw [hActivation, hState] at hBirthNext
            exact hBirthNext
          have hBirthSame : bankBirth active.val.2.1 bank = some beta := by
            by_cases hEligible : AffineBatchDecoder.eligible (tr r)
            · rcases hOrdinal hEligible with hSubquota | hQuota
              · obtain ⟨_, _, _, hSameBirth, _⟩ := hSubStep hEligible hSubquota
                exact hSameBirth.symm.trans hBirthStep
              · obtain ⟨_, _, _, hClearedBirth, _⟩ := hQuotaStep hEligible hQuota
                have hDifferent : r.val + 1 = beta :=
                  Option.some.inj (hClearedBirth.symm.trans hBirthStep)
                omega
            · obtain ⟨_, _, _, hSameBirth⟩ := hGap hEligible
              exact hSameBirth.symm.trans hBirthStep
          have hCompleted : bank.completed = nextState.downBatch.completed := by
            by_cases hEligible : AffineBatchDecoder.eligible (tr r)
            · rcases hOrdinal hEligible with hSubquota | hQuota
              · obtain ⟨_, hCompletedStep, _, _, _⟩ := hSubStep hEligible hSubquota
                calc
                  bank.completed = nextBank.completed := hCompletedStep.symm
                  _ = nextState.downBatch.completed := by rw [hState]
              · obtain ⟨_, _, _, hClearedBirth, _⟩ := hQuotaStep hEligible hQuota
                have hDifferent : r.val + 1 = beta :=
                  Option.some.inj (hClearedBirth.symm.trans hBirthStep)
                omega
            · obtain ⟨hBatchStep, _, _, _⟩ := hGap hEligible
              have hCompletedStep : bank.completed = nextBank.completed :=
                congrArg (fun b : AffineBatchDecoder.State p.T
                  (AffineBatchDecoder.width p) => b.completed) hBatchStep.symm
              calc
                bank.completed = nextBank.completed := hCompletedStep
                _ = nextState.downBatch.completed := by rw [hState]
          have hBirthSame' : bankBirth a state.downBatch = some beta := by
            simpa [hActivation, bank, state] using hBirthSame
          refine ⟨state, ?_, hCompleted, hBirthSame', ?_⟩
          · rw [sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h z i
              r.val r.isLt.le r.isLt active hp, hActivation]
            rfl
          · by_cases hStrict : r.val + 1 < p.T
            · rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
                (r.val + 1) hNext hStrict,
                sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
                  r.val r.isLt.le r.isLt]
              have hTestsNext' := hTestsNext
              rw [sourcePrelaunchDownTestsAt_prefix rate rewards C_star C_h z i
                (r.val + 1) hNext hStrict] at hTestsNext'
              exact hTestsNext'
            · have hLast : r.val + 1 = p.T := by omega
              simpa [hLast, sourcePrelaunchDownTestsAt_terminal,
                sourcePrelaunchDownTestsAt_prefix] using hTestsNext
      | inr inactive =>
          have hBirth := inactive_actual_successor_birth
            rate rewards C_star C_h z i r hNext inactive hp a nextState hNextState
          have hEq := Option.some.inj (hBirth.symm.trans hBirthNext)
          omega
    | inr stopped =>
        have hTransition := stopped_actual_successor
          rate rewards C_star C_h z i r hNext stopped hp
        have hPrevious : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i
            r.val r.isLt.le = some (a, nextState) := by
          exact hTransition.1.symm.trans hNextState
        refine ⟨nextState, hPrevious, rfl, hBirthNext, ?_⟩
        rw [hTransition.2.2]
        have hTestsEq := hTransition.2.1
        simpa using hTestsEq

private theorem actual_interval_states
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (beta : ℕ) (hBeta : beta ≤ p.T) :
    ∀ n (hn : n ≤ p.T),
      ∀ a (state : ReferencePrelaunchFollower.State p rate.eta),
        sourcePrelaunchDownActualCohort rate rewards C_star C_h z i n hn =
          some (a, state) →
        bankBirth a state.downBatch = some beta →
        ∀ u, beta ≤ u → ∀ hu : u ≤ n,
          ∃ stateU,
            sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u (hu.trans hn) =
              some (a, stateU) ∧
            stateU.downBatch.completed = state.downBatch.completed ∧
            bankBirth a stateU.downBatch = some beta := by
  intro n
  induction n with
  | zero =>
      intro hn a state hActual hBirth u hLow hHigh
      have hBetaZero : beta = 0 := by omega
      have hUZero : u = 0 := by omega
      subst beta
      subst u
      exact ⟨state, hActual, rfl, hBirth⟩
  | succ n ih =>
      intro hn a state hActual hBirth u hLow hHigh
      by_cases hLast : beta = n + 1
      · have huLast : u = n + 1 := by omega
        subst u
        exact ⟨state, hActual, rfl, hBirth⟩
      · have hBetaN : beta ≤ n := by omega
        by_cases huLast : u = n + 1
        · subst u
          exact ⟨state, hActual, rfl, hBirth⟩
        · have hUN : u ≤ n := by omega
          have hnT : n ≤ p.T := by omega
          have hNlt : n < p.T := by omega
          let r : Fin p.T := ⟨n, hNlt⟩
          obtain ⟨stateN, hActualN, hCompletedN, hBirthN, _⟩ :=
            actual_cohort_predecessor rate rewards C_star C_h z i r hn
              beta hBetaN a state hActual hBirth
          have hIH := ih hnT a stateN hActualN hBirthN u hLow hUN
          obtain ⟨stateU, hActualU, hCompletedU, hBirthU⟩ := hIH
          refine ⟨stateU, ?_, ?_, hBirthU⟩
          · exact hActualU
          · exact hCompletedU.trans hCompletedN

private theorem source_current_test_time
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) (hlt : u < p.T) :
    ∀ test ∈ (source_prelaunch_down_current_test rate rewards C_star C_h z i
      ⟨u, hlt⟩).toList, test.time.val = u := by
  classical
  intro test hTest
  let r : Fin p.T := ⟨u, hlt⟩
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hPre : ReferenceGeneratedPrelaunchDownCohort.prelaunchTest i
              (sourceReferenceInput rate rewards C_star C_h z).row active.val.2.1 r
              (ReferenceInitializationRun.ownEntry
                (ReferenceInitializationRun.physical
                  (sourceReferenceInput rate rewards C_star C_h z)
                  active.val.1.val active.val.1.property.1)
                (PublicDiscreteDraws.followerPlayer p.two_le_m
                  (ActualReferenceInitializationBlock.refFollower i)) r) = some test := by
            simpa only [source_prelaunch_down_current_test, r, hp, Option.mem_toList] using hTest
          unfold ReferenceGeneratedPrelaunchDownCohort.prelaunchTest at hPre
          split_ifs at hPre with hSelected
          · have hEq := Option.some.inj hPre
            have hTime : test.time = r := by
              have hTime' := congrArg
                (fun executed : ReferenceGeneratedDownBatchCalendar.ExecutedTest p =>
                  executed.time) hEq
              exact hTime'.symm
            simpa [r] using congrArg Fin.val hTime
      | inr _ =>
          simp only [source_prelaunch_down_current_test, r, hp] at hTest
          cases hTest
  | inr _ =>
      simp only [source_prelaunch_down_current_test, r, hp] at hTest
      cases hTest

private theorem source_tests_append_from_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (beta : ℕ) (hBeta : beta ≤ p.T)
    (n : ℕ) (hn : n ≤ p.T) (a : Activation p)
    (stateN : ReferencePrelaunchFollower.State p rate.eta)
    (hEnd : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i n hn =
      some (a, stateN)) (hBirthN : bankBirth a stateN.downBatch = some beta) :
    ∀ u, beta ≤ u → ∀ t (hUt : u ≤ t) (hTN : t ≤ n),
      ∃ tail,
        sourcePrelaunchDownTestsAt rate rewards C_star C_h z i t (hTN.trans hn) =
          sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u
            ((hUt.trans hTN).trans hn) ++ tail ∧
        ∀ test ∈ tail, u ≤ test.time.val := by
  intro u hBetaU t hUt hTN
  induction t with
  | zero =>
      have hu : u = 0 := by omega
      subst u
      exact ⟨[], by simp, by simp⟩
  | succ t ih =>
      by_cases hStart : u = t + 1
      · subst u
        exact ⟨[], by simp, by simp⟩
      · have hUt' : u ≤ t := by omega
        obtain ⟨tail, hTailEq, hTailTimes⟩ := ih hUt' (by omega)
        have hStateAll := actual_interval_states
          rate rewards C_star C_h z i beta hBeta n hn a stateN hEnd hBirthN
        obtain ⟨stateNext, hActualNext, _, hBirthNext⟩ :=
          hStateAll (t + 1) (by omega) (by omega)
        have htT : t + 1 ≤ p.T := by omega
        have htLt : t < p.T := by omega
        let r : Fin p.T := ⟨t, htLt⟩
        obtain ⟨statePrev, hActualPrev, _, _, hAppend⟩ :=
          actual_cohort_predecessor rate rewards C_star C_h z i r htT
            beta (by dsimp [r]; omega) a stateNext hActualNext hBirthNext
        have hCurrentTime := source_current_test_time
          rate rewards C_star C_h z i t (Nat.le_of_lt htLt) htLt
        refine ⟨tail ++ (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList,
          ?_, ?_⟩
        · calc
            sourcePrelaunchDownTestsAt rate rewards C_star C_h z i (t + 1) (by omega) =
                sourcePrelaunchDownTestsAt rate rewards C_star C_h z i t (by omega) ++
                  (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
                    simpa [r] using hAppend
            _ = (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u (by omega) ++ tail) ++
                  (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList := by
                    rw [hTailEq]
            _ = sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u (by omega) ++
                  (tail ++ (source_prelaunch_down_current_test rate rewards C_star C_h z i r).toList) := by
                    rw [List.append_assoc]
        · intro test hTest
          rcases List.mem_append.mp hTest with hTail | hCurrent
          · exact hTailTimes test hTail
          · have hTime := hCurrentTime test hCurrent
            omega

private theorem actual_tests_length_ge
    (tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
    (bank : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hMap : tests.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
      AffineBatchDecoder.collected bank)
    (hQuota : ∀ batch ∈ bank.completed, batch.length = AffineBatchDecoder.quota p) :
    AffineBatchDecoder.quota p * bank.completed.length ≤ tests.length := by
  have hFlat := completed_flatten_length (AffineBatchDecoder.quota p)
    bank.completed hQuota
  have hLength : tests.length =
      AffineBatchDecoder.quota p * bank.completed.length + bank.pending.length := by
    have hLenMap := congrArg List.length hMap
    simpa [AffineBatchDecoder.collected, hFlat] using hLenMap
  omega

private theorem drop_filter_of_append
    (older suffix : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p))
    (q u : ℕ) (hLength : q ≤ older.length)
    (hBefore : ∀ test ∈ older, test.time.val < u)
    (hAfter : ∀ test ∈ suffix, u ≤ test.time.val) :
    ((older ++ suffix).drop q).filter (fun test => test.time.val < u) = older.drop q := by
  rw [List.drop_append_of_le_length hLength, List.filter_append]
  have hKeep : (older.drop q).filter (fun test => test.time.val < u) = older.drop q :=
    List.filter_eq_self.mpr (by
      intro test hmem
      simpa using hBefore test (List.mem_of_mem_drop hmem))
  have hEmpty : suffix.filter (fun test => test.time.val < u) = [] :=
    List.filter_eq_nil_iff.mpr (by
      intro test hmem hlt
      exact (Nat.not_lt_of_ge (hAfter test hmem)) (of_decide_eq_true hlt))
  rw [hKeep, hEmpty, List.append_nil]

private theorem actual_current_flags_drop
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (u : ℕ) (hu : u ≤ p.T) (hlt : u < p.T)
    (a : Activation p) (state : ReferencePrelaunchFollower.State p rate.eta)
    (hActual : sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u hu =
      some (a, state))
    (w : AffineChannelLaw.Word (AffineBatchDecoder.width p)) :
    source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i
        ⟨u, hlt⟩ w =
      ((sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u hu).map
        (sourcePrelaunchDownCandidateFlag w)).drop
          (AffineBatchDecoder.quota p * state.downBatch.completed.length) := by
  classical
  let r : Fin p.T := ⟨u, hlt⟩
  cases hp : source_prelaunch_down_prefix rate rewards C_star C_h z i r with
  | inl branch =>
      cases branch with
      | inl active =>
          have hActual' :
              some (active.val.2.1, active.val.2.2.2) = some (a, state) := by
            rw [sourcePrelaunchDownActualCohort_of_active rate rewards C_star C_h z i
              u hu hlt active hp] at hActual
            exact hActual
          obtain ⟨ha, hs⟩ := Prod.mk.inj (Option.some.inj hActual')
          subst a
          subst state
          simp only [source_prelaunch_down_current_cohort_flags,
            source_prelaunch_down_prefix_flags, sourcePrelaunchDownTestsAt,
            hlt, r, hp]
          rfl
      | inr _ =>
          have hNone : sourcePrelaunchDownActualCohort
              rate rewards C_star C_h z i u hu = none := by
            exact sourcePrelaunchDownActualCohort_of_inactive rate rewards C_star C_h z i
              u hu hlt _ hp
          rw [hNone] at hActual
          cases hActual
  | inr stopped =>
      have hMap :
          (stopped.val.1.activation
            (ActualReferenceInitializationBlock.refFollower i)).map
              (fun a' => (a', stopped.val.2)) = some (a, state) := by
          rw [sourcePrelaunchDownActualCohort_of_stopped rate rewards C_star C_h z i
            u hu hlt stopped hp] at hActual
          exact hActual
      cases ha : stopped.val.1.activation
          (ActualReferenceInitializationBlock.refFollower i) with
      | none => simp [ha] at hMap
      | some a' =>
          simp only [ha, Option.map_some] at hMap
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hMap)
          simp only [source_prelaunch_down_current_cohort_flags,
            source_prelaunch_down_prefix_flags, sourcePrelaunchDownTestsAt,
            hlt, r, hp, ha]
          rfl

/-- One actual same-birth interval of the generated DOWN cohort.  The old
tests are the endpoint test census after removing its completed batches.  At
each boundary from the birth through the endpoint, the actual activation and
completed batches persist, while pending entries and candidate flags are the
time-filtered old tests.  The terminal flag statement uses the explicit
terminal census because there is no current prefix test at `T`. -/
theorem source_prelaunch_down_same_birth_cohort_interval
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (z : BootstrapPrivateRoundStreams.SourceInput p)
    (i : Fin (p.m - 1)) (n : ℕ) (hn : n ≤ p.T) :
    ∀ a (state : ReferencePrelaunchFollower.State p rate.eta),
      sourcePrelaunchDownActualCohort rate rewards C_star C_h z i n hn =
        some (a, state) →
      ∃ beta, ∃ hBeta : beta ≤ p.T, beta ≤ n ∧
        bankBirth a state.downBatch = some beta ∧
        birthAt rate rewards C_star C_h z i beta hBeta
          state.downBatch.completed.length ∧
        (∀ beta', bankBirth a state.downBatch = some beta' → beta' = beta) ∧
        (let k := state.downBatch.completed.length
         let Old := (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i n hn).drop
           (AffineBatchDecoder.quota p * k)
         Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
             state.downBatch.pending ∧
         Old.length < AffineBatchDecoder.quota p ∧
         (∀ test ∈ Old, beta ≤ test.time.val ∧ test.time.val < n) ∧
         (∀ u, beta ≤ u → ∀ hu : u ≤ n,
           ∃ stateU,
             sourcePrelaunchDownActualCohort rate rewards C_star C_h z i u (hu.trans hn) =
               some (a, stateU) ∧
             stateU.downBatch.completed = state.downBatch.completed ∧
             bankBirth a stateU.downBatch = some beta ∧
             stateU.downBatch.pending =
               (Old.filter (fun test => test.time.val < u)).map
                 ReferenceGeneratedPrelaunchDownCohort.testEntry ∧
             ∀ w,
               (if hU : u < p.T then
                  source_prelaunch_down_current_cohort_flags rate rewards C_star C_h z i
                    ⟨u, hU⟩ w
                else
                  ((sourcePrelaunchDownTests rate rewards C_star C_h z i).map
                    (sourcePrelaunchDownCandidateFlag w)).drop
                      (AffineBatchDecoder.quota p * k)) =
                 (Old.filter (fun test => test.time.val < u)).map
                   (sourcePrelaunchDownCandidateFlag w))) := by
  classical
  intro a state hActual
  obtain ⟨beta, hBeta, hBetaN, hBirthBank, hBirth, hUnique⟩ :=
    actual_endpoint_birth rate rewards C_star C_h z i n hn a state hActual
  let k := state.downBatch.completed.length
  let qk := AffineBatchDecoder.quota p * k
  let Old := (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i n hn).drop qk
  have hCensus := actual_pending_census rate rewards C_star C_h z i n hn a state hActual
  rcases hCensus with ⟨hCollected, hPending, hCompletedQuota, hPendingShort⟩
  have hOldMap : Old.map ReferenceGeneratedPrelaunchDownCohort.testEntry =
      state.downBatch.pending := by
    dsimp [Old, qk]
    rw [List.map_drop]
    exact hPending.symm
  have hOldShort : Old.length < AffineBatchDecoder.quota p := by
    have hLength := congrArg List.length hOldMap
    have hLength' : Old.length = state.downBatch.pending.length := by
      simpa using hLength
    omega
  have hInterval := actual_interval_states rate rewards C_star C_h z i beta hBeta
    n hn a state hActual hBirthBank
  obtain ⟨birthActivation, birthState, hBirthActual, hBirthLength,
    hBirthPending, hBirthBankAt⟩ :=
      actualState_of_birthAt rate rewards C_star C_h z i beta hBeta k hBirth
  obtain ⟨stateBeta, hActualBeta, hCompletedBeta, hBirthBeta⟩ :=
    hInterval beta (Nat.le_refl beta) hBetaN
  have hBirthPair : (birthActivation, birthState) = (a, stateBeta) :=
    Option.some.inj (hBirthActual.symm.trans hActualBeta)
  have hBirthState : stateBeta = birthState := (Prod.mk.inj hBirthPair).2.symm
  have hBirthEmpty : stateBeta.downBatch.pending = [] := by
    rw [hBirthState]
    exact hBirthPending
  have hBirthCompletedLength : stateBeta.downBatch.completed.length = k := by
    rw [hBirthState]
    exact hBirthLength
  have hCensusBeta := actual_pending_census rate rewards C_star C_h z i beta hBeta
    a stateBeta hActualBeta
  rcases hCensusBeta with ⟨hCollectedBeta, hPendingBeta, hCompletedQuotaBeta,
    hPendingShortBeta⟩
  have hFlatBeta := completed_flatten_length (AffineBatchDecoder.quota p)
    stateBeta.downBatch.completed hCompletedQuotaBeta
  have hTestsBetaLength :
      (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i beta hBeta).length = qk := by
    have hLength := congrArg List.length hCollectedBeta
    simp only [List.length_map, AffineBatchDecoder.collected, List.length_append,
      hBirthEmpty, List.length_nil, hFlatBeta, hBirthCompletedLength] at hLength
    dsimp [qk, k]
    exact hLength
  obtain ⟨tailFromBirth, hAppendFromBirth, hBirthTailTimes⟩ :=
    source_tests_append_from_interval rate rewards C_star C_h z i beta hBeta n hn a
      state hActual hBirthBank beta (Nat.le_refl beta) n hBetaN (Nat.le_refl n)
  have hOldTail : Old = tailFromBirth := by
    dsimp [Old]
    rw [hAppendFromBirth]
    have hDrop : qk ≤
        (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i beta hBeta).length := by
      omega
    rw [List.drop_append_of_le_length hDrop]
    simp [hTestsBetaLength]
  have hOldTimeBounds : ∀ test ∈ Old, beta ≤ test.time.val ∧ test.time.val < n := by
    intro test hTest
    have hTail := hBirthTailTimes test (by rw [← hOldTail]; exact hTest)
    have hEndpointTime := actual_tests_time_lt rate rewards C_star C_h z i n hn a state
      hActual test (List.mem_of_mem_drop hTest)
    exact ⟨hTail, hEndpointTime⟩
  refine ⟨beta, hBeta, hBetaN, hBirthBank, hBirth, hUnique, ?_⟩
  dsimp [k, Old]
  refine ⟨hOldMap, hOldShort, hOldTimeBounds, ?_⟩
  intro u hBetaU hu
  have huLeT : u ≤ p.T := hu.trans hn
  obtain ⟨stateU, hActualU, hCompletedU, hBirthU⟩ :=
    hInterval u hBetaU hu
  have hCensusU := actual_pending_census rate rewards C_star C_h z i u huLeT a stateU hActualU
  rcases hCensusU with ⟨hCollectedU, hPendingU, hCompletedQuotaU, hPendingShortU⟩
  have hCompletedLengthU : stateU.downBatch.completed.length = k := by
    rw [hCompletedU]
  have hOldBoundU : qk ≤
      (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u huLeT).length := by
    have hBound := actual_tests_length_ge
      (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u huLeT)
      stateU.downBatch hCollectedU hCompletedQuotaU
    simpa [qk, k, hCompletedLengthU] using hBound
  obtain ⟨tailU, hAppendU, hTailUTimes⟩ :=
    source_tests_append_from_interval rate rewards C_star C_h z i beta hBeta n hn a state
      hActual hBirthBank u hBetaU n hu (Nat.le_refl n)
  have hFilteredU : Old.filter (fun test => test.time.val < u) =
      (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u huLeT).drop qk := by
    dsimp [Old]
    rw [hAppendU]
    exact drop_filter_of_append
      (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u huLeT) tailU qk u hOldBoundU
      (actual_tests_time_lt rate rewards C_star C_h z i u huLeT a stateU hActualU)
      hTailUTimes
  have hPendingFiltered : stateU.downBatch.pending =
      (Old.filter (fun test => test.time.val < u)).map
        ReferenceGeneratedPrelaunchDownCohort.testEntry := by
    calc
      stateU.downBatch.pending =
          (sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u huLeT |>.map
            ReferenceGeneratedPrelaunchDownCohort.testEntry).drop qk := by
              rw [hPendingU, hCompletedLengthU]
      _ = ((sourcePrelaunchDownTestsAt rate rewards C_star C_h z i u huLeT).drop qk).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry := by
            rw [List.map_drop]
      _ = (Old.filter (fun test => test.time.val < u)).map
          ReferenceGeneratedPrelaunchDownCohort.testEntry := by
            rw [hFilteredU]
  refine ⟨stateU, hActualU, hCompletedU, hBirthU, hPendingFiltered, ?_⟩
  intro w
  by_cases huLt : u < p.T
  · have hFlags := actual_current_flags_drop rate rewards C_star C_h z i u huLeT huLt
      a stateU hActualU w
    rw [hCompletedLengthU, ← List.map_drop] at hFlags
    have hMapFiltered := congrArg
      (fun tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) =>
        tests.map (sourcePrelaunchDownCandidateFlag w)) hFilteredU
    simpa [huLt, Old] using hFlags.trans hMapFiltered.symm
  · have huEq : u = p.T := by omega
    subst u
    have hnEq : n = p.T := by omega
    subst n
    have hTerminalTests : sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T hu =
        sourcePrelaunchDownTests rate rewards C_star C_h z i := by
      exact sourcePrelaunchDownTestsAt_terminal rate rewards C_star C_h z i
        (Nat.le_refl p.T)
    have hFlags :
        ((sourcePrelaunchDownTests rate rewards C_star C_h z i).map
          (sourcePrelaunchDownCandidateFlag w)).drop qk =
        ((sourcePrelaunchDownTestsAt rate rewards C_star C_h z i p.T hu).drop qk).map
          (sourcePrelaunchDownCandidateFlag w) := by
      rw [List.map_drop, hTerminalTests]
    have hFilteredFlags := congrArg
      (fun tests : List (ReferenceGeneratedDownBatchCalendar.ExecutedTest p) =>
        tests.map (sourcePrelaunchDownCandidateFlag w)) hFilteredU
    simpa [hTerminalTests] using hFlags.trans hFilteredFlags.symm

end Bandits.Support.ReferenceGeneratedPrelaunchDownCohortInterval

end
