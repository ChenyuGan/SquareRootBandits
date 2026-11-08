/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferencePrelaunchLifecycleReplay
public import Bandits.Support.ReferenceFollowerDecoderChronology

import Lean.Elab.Tactic.Omega

/-!
# Original-source corrected reference launch

Sources: `sources/zip4/manuscript/07_public_setup.tex:93-164`,
`sources/zip4/manuscript/06_interruptions.tex:235-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

This module constructs the first canonical active state from the original
source input, whole grid reward table, shared constants, and accepted
rate. It retains the generated reference boundary as the source of failure
provenance. It establishes no probability law, Borel property, comparison to
the unrestricted ordinary actual execution, or regret assertion. The next
consumers are the unconditional corrected complete-execution construction and
the selected-row Borel/prefix-locality producer.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.ActiveFollowerLifecycle
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferencePrelaunchPhysicalReplay
open Bandits.Support.InitializationFailureProvenance
open Bandits.Support.ReferenceFollowerDecoderChronology
open scoped Classical

namespace Bandits.Support.ReferenceCorrectedInitializationLaunch

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters}

private theorem run_crossing_origin (x : ReferenceInitializationRun.Input p)
    (r : ℕ) (hr : r ≤ n_boot p)
    (hc : (ReferenceInitializationRun.run x r).crossing.isSome = true) :
    ∃ q, ∃ _hq : q < n_boot p, ∃ hblock :
      (ReferenceInitializationRun.run x q).completed < n_boot p,
      (ReferenceInitializationRun.run x q).crossing = none ∧
      (ReferenceInitializationRun.run x q).completed = q ∧
      ReferenceInitializationRun.crosses x (ReferenceInitializationRun.run x q) hblock = true ∧
      ReferenceInitializationRun.run x r =
        ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hblock := by
  induction r with
  | zero =>
      simp [ReferenceInitializationRun.run, ReferenceInitializationRun.initial] at hc
  | succ r ih =>
      have hr' : r ≤ n_boot p := by omega
      by_cases hp : (ReferenceInitializationRun.run x r).crossing.isSome = true
      · have hsame : ReferenceInitializationRun.run x (r + 1) =
            ReferenceInitializationRun.run x r := by
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_crossing x _ hp]
        obtain ⟨q, hq, hblock, hnone, hcompleted, hcross, hfinish⟩ :=
          ih hr' (by simpa [hsame] using hc)
        refine ⟨q, hq, hblock, hnone, hcompleted, hcross, ?_⟩
        rw [hsame]
        exact hfinish
      · have hnone : (ReferenceInitializationRun.run x r).crossing = none := by
          cases hh : (ReferenceInitializationRun.run x r).crossing <;> simp_all
        have hcompleted : (ReferenceInitializationRun.run x r).completed = r :=
          (ReferenceInitializationRun.run_progress x r hr').resolve_left hp
        have hblock : (ReferenceInitializationRun.run x r).completed < n_boot p := by
          omega
        have hstep : ReferenceInitializationRun.run x (r + 1) =
            ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x r)
              hblock := by
          rw [ReferenceInitializationRun.run_succ,
            ReferenceInitializationRun.advance_of_no_crossing x _ hnone hblock]
        have hcross : ReferenceInitializationRun.crosses x
            (ReferenceInitializationRun.run x r) hblock = true := by
          rw [hstep] at hc
          cases h : ReferenceInitializationRun.crosses x
              (ReferenceInitializationRun.run x r) hblock <;>
            simp [ReferenceInitializationRun.finishBlock, h] at hc ⊢
        refine ⟨r, by omega, hblock, hnone, hcompleted, hcross, hstep⟩

/-- At the initial source boundary nobody has an effective declaration, so
no ordinary lifecycle or proposal memory has yet been instantiated. -/
theorem generated_initial_boundary
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    (ReferenceInitializationRun.run x 0).completed = 0 ∧
      (∀ i, (ReferenceInitializationRun.run x 0).activation i = none ∧
        (ReferenceInitializationRun.run x 0).forcedFailure i = false) ∧
      ReferenceInitializationRun.coordinatorLearner (ReferenceInitializationRun.run x 0) = none := by
  exact ⟨rfl, fun _ => ⟨rfl, rfl⟩, rfl⟩

/-- A noncrossing undeclared follower has no ordinary lifecycle to continue.
The initial ordinary projection is dormant; it is not an installed memory. -/
theorem generated_undeclared_boundary
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ)
    (hnone : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).crossing = none)
    (i : ActiveRoundActions.Follower p.m)
    (ha : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).activation i = none) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.run x r
    b.forcedFailure i = false ∧
      (¬ ∃ a, b.activation i = some a) ∧
      ReferenceInitializationRun.ordinary x b i = ReferencePrelaunchFollower.initial p rate.eta := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  have hf := ReferenceInitializationRun.run_no_forced_before_launch x r hnone i
  dsimp only [x] at hf
  refine ⟨hf, ?_, ?_⟩
  · rintro ⟨a, hactivation⟩
    rw [ha] at hactivation
    cases hactivation
  · simp only [ReferenceInitializationRun.ordinary, hf, Bool.false_eq_true, ↓reduceIte, ha]
    rfl

/-- Crossing and exhaustion both stop the original boundary recursion. All
histories, declarations and failure markers are retained by this identity. -/
theorem generated_stopped_boundary
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ)
    (hstop : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).crossing.isSome = true ∨
      n_boot p ≤ (ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).completed) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    ReferenceInitializationRun.run x (r + 1) = ReferenceInitializationRun.run x r := by
  dsimp only
  rw [ReferenceInitializationRun.run_succ]
  rcases hstop with hc | hexhausted
  · exact ReferenceInitializationRun.advance_of_crossing _ _ hc
  · exact ReferenceInitializationRun.advance_of_exhausted _ _ hexhausted

/-- Every generated noncrossing boundary's already-declared follower has the
unique local memory trajectory initialized at its source declaration. The
theorem retains the actual corrected replay, including suppression and decoder
resets; it does not install memory in the boundary carrier. -/
theorem generated_boundary_memory
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ)
    (hnone : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).crossing = none)
    (i : Fin (p.m - 1)) (a : ReferencePrelaunchFollower.Activation p)
    (ha : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.run x r
    ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i) =
      ReferencePrelaunchFollower.replay rate.eta i x.row a
        (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)))
        (ReferenceInitializationRun.elapsed_le_T p b.completed) ∧
    (let n := ReferenceInitializationRun.elapsed p b.completed
    let history : ReferencePrelaunchFollower.LocalHistory p n :=
      b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))
    let alpha := a
    let hn : n ≤ p.T := ReferenceInitializationRun.elapsed_le_T p b.completed
    let hcut : alpha.val ≤ n + 1 :=
      b.activation_le (ActualReferenceInitializationBlock.refFollower i) a ha
    let a0 := alpha.val - 1
    let stateAt : (k : ℕ) → k ≤ n → ReferencePrelaunchFollower.State p rate.eta :=
      fun k hk => ReferencePrelaunchFollower.replay rate.eta i x.row alpha
        (ReferencePrelaunchLifecycleReplay.prefixHistory history k hk) (Nat.le_trans hk hn)
    stateAt a0 (by omega) = ReferencePrelaunchFollower.initial p rate.eta ∧
    (∃! memory : Fin (n - a0 + 1) → ActiveFollowerLifecycle.LocalMemory p,
      memory ⟨0, by omega⟩ = ActiveFollowerLifecycle.initialMemory p ∧
      (∀ k (hactive : a0 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history k hk) (Nat.le_trans hk hn)
        let nextState := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history (k + 1)
            (Nat.succ_le_of_lt hbefore)) (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - a0 + 1) := ⟨k - a0, by omega⟩
        let nextIndex : Fin (n - a0 + 1) := ⟨k + 1 - a0, by omega⟩
        ActiveFollowerLifecycle.startRound rate.eta ⟨k, by omega⟩ state
            (memory index) = .ok (state, memory index) ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i x.row ⟨k, by omega⟩
            (history ⟨k, by omega⟩).2 state (memory index) nextState =
              .ok (nextState, memory nextIndex))) ∧
    (∀ memory : Fin (n - a0 + 1) → ActiveFollowerLifecycle.LocalMemory p,
      memory ⟨0, by omega⟩ = ActiveFollowerLifecycle.initialMemory p →
      (∀ k (hactive : a0 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history k hk) (Nat.le_trans hk hn)
        let nextState := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history (k + 1)
            (Nat.succ_le_of_lt hbefore)) (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - a0 + 1) := ⟨k - a0, by omega⟩
        let nextIndex : Fin (n - a0 + 1) := ⟨k + 1 - a0, by omega⟩
        ActiveFollowerLifecycle.startRound rate.eta ⟨k, by omega⟩ state
            (memory index) = .ok (state, memory index) ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i x.row ⟨k, by omega⟩
            (history ⟨k, by omega⟩).2 state (memory index) nextState =
              .ok (nextState, memory nextIndex)) →
      (∀ j, memory j = ActiveFollowerLifecycle.initialMemory p) ∧
        memory (Fin.last (n - a0)) = ActiveFollowerLifecycle.initialMemory p)) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.run x r
  have hforce := ReferenceInitializationRun.run_no_forced_before_launch x r hnone
    (ActualReferenceInitializationBlock.refFollower i)
  have hforceRoot : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).forcedFailure
      (ActualReferenceInitializationBlock.refFollower i) = false := by
    simpa [x] using hforce
  refine ⟨?_, ?_⟩
  · simp [ReferenceInitializationRun.ordinary, hforceRoot, ha,
      ReferencePrelaunchFollower.atLaunch,
      BootstrapPhysicalInput.sourceFollowerIndex,
      ActualReferenceInitializationBlock.refFollower]
    rfl
  · exact ReferencePrelaunchLifecycleReplay.replay_proposal_memory_characterization
      rate i x.row a
      (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i)))
      (ReferenceInitializationRun.elapsed_le_T p b.completed)
      (b.activation_le (ActualReferenceInitializationBlock.refFollower i) a ha)

/-- An already declared follower continues through the actual generated block
append. The activation is retained, `run_ordinary_successor` supplies the full
ordinary block replay, and the accepted `run_append_block` equation preserves
all prior logs and in-progress or completed DOWN batches. -/
theorem generated_ordinary_successor_memory
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ)
    (hnone : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).crossing = none)
    (hblock : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).completed <
        n_boot p)
    (i : Fin (p.m - 1)) (a : ReferencePrelaunchFollower.Activation p)
    (ha : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.run x r
    let z := ReferenceInitializationRun.replayInput x b hblock i a ha
    (ReferenceInitializationRun.run x (r + 1)).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a ∧
    ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.run x (r + 1))
        (ActualReferenceInitializationBlock.refFollower i) =
      ReferencePrelaunchPhysicalReplay.blockReplay z ∧
    ReferencePrelaunchFollower.run (ReferencePrelaunchPhysicalReplay.followerIndex z)
      z.physical.row z.activation
      (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
      (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (ReferenceInitializationRun.nextBlock b hblock))
      (ReferencePrelaunchPhysicalReplay.prefixIndices z ++
        ReferencePrelaunchPhysicalReplay.blockIndices z)
      (ReferencePrelaunchFollower.initial p z.eta) =
        ReferencePrelaunchPhysicalReplay.blockReplay z ∧
    (∀ k (_hafter : ReferencePrelaunchPhysicalReplay.blockStart p
          (ReferenceInitializationRun.nextBlock b hblock) ≤ k)
        (hbefore : k < ReferencePrelaunchPhysicalReplay.blockEnd p
          (ReferenceInitializationRun.nextBlock b hblock))
        (memory : ActiveFollowerLifecycle.LocalMemory p),
      let history := ReferencePrelaunchPhysicalReplay.chronologicalHistory z
      let hn := ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
        (ReferenceInitializationRun.nextBlock b hblock)
      let state := ReferencePrelaunchFollower.replay rate.eta i x.row a
        (ReferencePrelaunchLifecycleReplay.prefixHistory history k (Nat.le_of_lt hbefore))
        (Nat.le_trans (Nat.le_of_lt hbefore) hn)
      let nextState := ReferencePrelaunchFollower.replay rate.eta i x.row a
        (ReferencePrelaunchLifecycleReplay.prefixHistory history (k + 1)
          (Nat.succ_le_of_lt hbefore)) (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
      ActiveFollowerLifecycle.startRound rate.eta ⟨k, by omega⟩ state memory =
          .ok (state, memory) ∧
        DeclaredFollowerLocalRound.releaseAndFinish rate i x.row ⟨k, by omega⟩
          (history ⟨k, by omega⟩).2 state memory nextState = .ok (nextState, memory)) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.run x r
  let z := ReferenceInitializationRun.replayInput x b hblock i a ha
  have hactivation := ReferenceInitializationRun.activated_activation x b hblock
    (ActualReferenceInitializationBlock.refFollower i) a ha
  have hnext : ReferenceInitializationRun.run x (r + 1) =
      ReferenceInitializationRun.finishBlock x b hblock := by
    rw [ReferenceInitializationRun.run_succ,
      ReferenceInitializationRun.advance_of_no_crossing x b hnone hblock]
  have hnextActivation : (ReferenceInitializationRun.run x (r + 1)).activation
      (ActualReferenceInitializationBlock.refFollower i) = some a := by
    rw [hnext]
    exact hactivation
  have hsuccessor := ReferenceInitializationRun.run_ordinary_successor x r hnone hblock
    (ActualReferenceInitializationBlock.refFollower i) a ha
  have happend := ReferencePrelaunchPhysicalReplay.run_append_block z
  refine ⟨hnextActivation, hsuccessor, happend, ?_⟩
  intro k hafter hbefore memory
  have hactive : a.val ≤ k + 1 :=
    z.activation_le_blockStart.trans (Nat.add_le_add_right hafter 1)
  exact ReferencePrelaunchLifecycleReplay.replay_prefix_step_lifecycle rate i x.row a
    (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
    (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
      (ReferenceInitializationRun.nextBlock b hblock)) k hbefore hactive memory

/-- A newly saved true-row declaration is initialized at the clipped block
end plus one, with no earlier ordinary lifecycle call or proposal read. -/
theorem generated_saved_boundary_memory
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ) (hr : r < n_boot p)
    (hnone : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).crossing = none)
    (i : ActiveRoundActions.Follower p.m)
    (hi : i ∈ ReferenceInitializationRun.uninformed
      (ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r))
    (hsaved : (ReferenceInitializationRun.candidate
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r)
      (ReferencePrelaunchLifecycleReplay.run_completed_lt_of_no_crossing
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r hr hnone)
      ⟨i, hi⟩).pending = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.run x r
    let h := ReferencePrelaunchLifecycleReplay.run_completed_lt_of_no_crossing x r hr hnone
    (ReferenceInitializationRun.finishBlock x b h).activation i =
      some (ReferenceInitializationRun.boundaryActivation b) ∧
    ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h) i =
      ReferencePrelaunchFollower.initial p rate.eta ∧
    ReferenceInitializationRun.elapsed p (b.completed + 1) <
      (ReferenceInitializationRun.boundaryActivation b).val ∧
    ActiveFollowerLifecycle.initialMemory p = ⟨none⟩ := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  simpa [x, ActualReferenceInitializationBlock.referenceInput] using
    ReferencePrelaunchLifecycleReplay.saved_declaration_initial_lifecycle x r hr hnone i hi hsaved

/-- A newly forced follower is initialized at the first strict crossing after
pending saves. Its forced-failure marker remains true and there are zero
preceding ordinary local calls. -/
theorem generated_forced_boundary_memory
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ) (hr : r < n_boot p)
    (hnone : (ReferenceInitializationRun.run
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r).crossing = none)
    (i : ActiveRoundActions.Follower p.m)
    (hforced : ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.run
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r)
      (ReferencePrelaunchLifecycleReplay.run_completed_lt_of_no_crossing
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) r hr hnone) i = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.run x r
    let h := ReferencePrelaunchLifecycleReplay.run_completed_lt_of_no_crossing x r hr hnone
    (ReferenceInitializationRun.finishBlock x b h).activation i =
      some (ReferenceInitializationRun.boundaryActivation b) ∧
    ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h) i =
      ReferencePrelaunchFollower.initial p rate.eta ∧
    (ReferenceInitializationRun.finishBlock x b h).forcedFailure i = true ∧
    ReferenceInitializationRun.elapsed p (b.completed + 1) <
      (ReferenceInitializationRun.boundaryActivation b).val ∧
    ActiveFollowerLifecycle.initialMemory p = ⟨none⟩ := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  simpa [x, ActualReferenceInitializationBlock.referenceInput] using
    ReferencePrelaunchLifecycleReplay.forced_correction_initial_lifecycle x r hr hnone i hforced

private theorem output_predecessor (x : ReferenceInitializationRun.Input p)
    (hc : (ReferenceInitializationRun.output x).crossing.isSome = true) :
    ∃ q, ∃ _hq : q < n_boot p, ∃ hblock :
      (ReferenceInitializationRun.run x q).completed < n_boot p,
      (ReferenceInitializationRun.run x q).crossing = none ∧
      (ReferenceInitializationRun.run x q).completed = q ∧
      ReferenceInitializationRun.crosses x (ReferenceInitializationRun.run x q) hblock = true ∧
      ReferenceInitializationRun.output x =
        ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hblock := by
  exact run_crossing_origin x (n_boot p) le_rfl hc

/-- The unique memory trajectory beside the actual output history. The
activation equality selects its computed payload; no trajectory or local
success is supplied. This also includes activation at `T+1` with zero calls. -/
theorem output_replay_memory_characterization
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p)
    (i : Fin (p.m - 1)) (a : ReferencePrelaunchFollower.Activation p)
    (ha : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).activation
        (ActualReferenceInitializationBlock.refFollower i) = some a) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    (let n := ReferenceInitializationRun.elapsed p b.completed
    let history : ReferencePrelaunchFollower.LocalHistory p n :=
      b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
        (ActualReferenceInitializationBlock.refFollower i))
    let alpha := a
    let hn : n ≤ p.T := ReferenceInitializationRun.elapsed_le_T p b.completed
    let hcut : alpha.val ≤ n + 1 :=
      b.activation_le (ActualReferenceInitializationBlock.refFollower i) a ha
    let a0 := alpha.val - 1
    let stateAt : (k : ℕ) → k ≤ n → ReferencePrelaunchFollower.State p rate.eta :=
      fun k hk => ReferencePrelaunchFollower.replay rate.eta i x.row alpha
        (ReferencePrelaunchLifecycleReplay.prefixHistory history k hk) (Nat.le_trans hk hn)
    stateAt a0 (by omega) = ReferencePrelaunchFollower.initial p rate.eta ∧
    (∃! memory : Fin (n - a0 + 1) → ActiveFollowerLifecycle.LocalMemory p,
      memory ⟨0, by omega⟩ = ActiveFollowerLifecycle.initialMemory p ∧
      (∀ k (hactive : a0 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history k hk) (Nat.le_trans hk hn)
        let nextState := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history (k + 1)
            (Nat.succ_le_of_lt hbefore)) (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - a0 + 1) := ⟨k - a0, by omega⟩
        let nextIndex : Fin (n - a0 + 1) := ⟨k + 1 - a0, by omega⟩
        ActiveFollowerLifecycle.startRound rate.eta ⟨k, by omega⟩ state
            (memory index) = .ok (state, memory index) ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i x.row ⟨k, by omega⟩
            (history ⟨k, by omega⟩).2 state (memory index) nextState =
              .ok (nextState, memory nextIndex))) ∧
    (∀ memory : Fin (n - a0 + 1) → ActiveFollowerLifecycle.LocalMemory p,
      memory ⟨0, by omega⟩ = ActiveFollowerLifecycle.initialMemory p →
      (∀ k (hactive : a0 ≤ k) (hbefore : k < n),
        let hk : k ≤ n := Nat.le_of_lt hbefore
        let state := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history k hk) (Nat.le_trans hk hn)
        let nextState := ReferencePrelaunchFollower.replay rate.eta i x.row alpha
          (ReferencePrelaunchLifecycleReplay.prefixHistory history (k + 1)
            (Nat.succ_le_of_lt hbefore)) (Nat.le_trans (Nat.succ_le_of_lt hbefore) hn)
        let index : Fin (n - a0 + 1) := ⟨k - a0, by omega⟩
        let nextIndex : Fin (n - a0 + 1) := ⟨k + 1 - a0, by omega⟩
        ActiveFollowerLifecycle.startRound rate.eta ⟨k, by omega⟩ state
            (memory index) = .ok (state, memory index) ∧
          DeclaredFollowerLocalRound.releaseAndFinish rate i x.row ⟨k, by omega⟩
            (history ⟨k, by omega⟩).2 state (memory index) nextState =
              .ok (nextState, memory nextIndex)) →
      (∀ j, memory j = ActiveFollowerLifecycle.initialMemory p) ∧
        memory (Fin.last (n - a0)) = ActiveFollowerLifecycle.initialMemory p)) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  exact ReferencePrelaunchLifecycleReplay.replay_proposal_memory_characterization
    rate i x.row a
    (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
      (ActualReferenceInitializationBlock.refFollower i)))
    (ReferenceInitializationRun.elapsed_le_T p b.completed)
    (b.activation_le (ActualReferenceInitializationBlock.refFollower i) a ha)

/-- Source memory provenance at crossing comes first. A previously declared
follower is continued by the real block append; a fresh true-row save has a
zero-call base; a correction uses its forced branch and keeps `forcedFailure`.
The unique lifecycle characterization supplies the initialized memory path on
the generated replay, including passing suppressed parses and decoder resets. -/
theorem output_memory_provenance
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (i : Fin (p.m - 1)) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    ∃ a : ReferencePrelaunchFollower.Activation p,
      ∃ _ha : b.activation (ActualReferenceInitializationBlock.refFollower i) = some a,
      ((b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true ∧
          ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.initial p rate.eta ∧
          a.val = ReferenceInitializationRun.elapsed p b.completed + 1 ∧
          ActiveFollowerLifecycle.initialMemory p = ⟨none⟩) ∨
       (b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false ∧
          ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.replay rate.eta i x.row a
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
                  (ActualReferenceInitializationBlock.refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed) ∧
          ((ReferenceInitializationRun.ordinary x b
              (ActualReferenceInitializationBlock.refFollower i) =
              ReferencePrelaunchFollower.initial p rate.eta) ∨
            ∃ q, ∃ _hq : q < n_boot p,
              ∃ hblock : (ReferenceInitializationRun.run x q).completed < n_boot p,
              (ReferenceInitializationRun.run x q).crossing = none ∧
              ∃ aPrev, ∃ haPrev : (ReferenceInitializationRun.run x q).activation
                  (ActualReferenceInitializationBlock.refFollower i) = some aPrev,
                ReferenceInitializationRun.ordinary x b
                  (ActualReferenceInitializationBlock.refFollower i) =
                  ReferencePrelaunchPhysicalReplay.blockReplay
                    (ReferenceInitializationRun.replayInput x
                      (ReferenceInitializationRun.run x q) hblock i aPrev haPrev) ∧
                (let z := ReferenceInitializationRun.replayInput x
                    (ReferenceInitializationRun.run x q) hblock i aPrev haPrev
                 ReferencePrelaunchFollower.run
                    (ReferencePrelaunchPhysicalReplay.followerIndex z)
                    z.physical.row z.activation
                    (ReferencePrelaunchPhysicalReplay.chronologicalHistory z)
                    (ReferencePrelaunchPhysicalReplay.blockEnd_le_T p
                      (ReferenceInitializationRun.nextBlock (ReferenceInitializationRun.run x q) hblock))
                    (ReferencePrelaunchPhysicalReplay.prefixIndices z ++
                      ReferencePrelaunchPhysicalReplay.blockIndices z)
                    (ReferencePrelaunchFollower.initial p z.eta) =
                  ReferencePrelaunchPhysicalReplay.blockReplay z)))) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  have hlaunch := ReferenceInitializationRun.output_launch_state x hc
    (ActualReferenceInitializationBlock.refFollower i)
  obtain ⟨a, ha⟩ : ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a := by
    cases hactivation : b.activation (ActualReferenceInitializationBlock.refFollower i) with
    | none => simp [b, hactivation] at hlaunch
    | some a => exact ⟨a, rfl⟩
  have hpred := output_predecessor x hc
  rcases hpred with ⟨q, hq, hblock, hnone, hcompleted, hcross, houtput⟩
  have hfinish : b = ReferenceInitializationRun.finishBlock x
      (ReferenceInitializationRun.run x q) hblock := by
    simpa [b] using houtput
  have hprior := ReferenceInitializationRun.run_no_forced_before_launch x q hnone
    (ActualReferenceInitializationBlock.refFollower i)
  by_cases hf : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true
  · have hfout := hf
    rw [hfinish] at hfout
    change (ReferenceInitializationRun.run x q).forcedFailure
        (ActualReferenceInitializationBlock.refFollower i) ||
      ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x q) hblock
        (ActualReferenceInitializationBlock.refFollower i) = true at hfout
    rw [hprior] at hfout
    have hforced : ReferenceInitializationRun.forced x (ReferenceInitializationRun.run x q)
        hblock (ActualReferenceInitializationBlock.refFollower i) = true := by
      simpa using hfout
    have hfresh := ReferencePrelaunchLifecycleReplay.forced_correction_initial_lifecycle
      x q hq hnone (ActualReferenceInitializationBlock.refFollower i) hforced
    have hstate : ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i) =
        ReferencePrelaunchFollower.initial p rate.eta := by
      rw [hfinish]
      simpa [x, ActualReferenceInitializationBlock.referenceInput] using hfresh.2.1
    have hactivationFresh : b.activation (ActualReferenceInitializationBlock.refFollower i) =
        some (ReferenceInitializationRun.boundaryActivation (ReferenceInitializationRun.run x q)) := by
      rw [hfinish]
      exact hfresh.1
    have haFresh := Option.some.inj (ha.symm.trans hactivationFresh)
    have htime : a.val = ReferenceInitializationRun.elapsed p b.completed + 1 := by
      rw [haFresh, hfinish]
      rfl
    exact ⟨a, ha, Or.inl ⟨hf, hstate, htime, hfresh.2.2.2.2⟩⟩
  · have hfalse : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = false := by
      cases hvalue : b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) with
      | false => rfl
      | true => exact False.elim (hf hvalue)
    have hordinaryReplay : ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i) =
        ReferencePrelaunchFollower.replay rate.eta i x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
            (ActualReferenceInitializationBlock.refFollower i)))
          (ReferenceInitializationRun.elapsed_le_T p b.completed) := by
      simp [ReferenceInitializationRun.ordinary, hfalse, ha,
        ReferencePrelaunchFollower.atLaunch,
        BootstrapPhysicalInput.sourceFollowerIndex,
        ActualReferenceInitializationBlock.refFollower, x,
        ActualReferenceInitializationBlock.referenceInput]
    by_cases hprevious : (ReferenceInitializationRun.run x q).activation
        (ActualReferenceInitializationBlock.refFollower i) = none
    · have hi : ActualReferenceInitializationBlock.refFollower i ∈
          ReferenceInitializationRun.uninformed (ReferenceInitializationRun.run x q) :=
        (ReferenceInitializationRun.mem_uninformed (ReferenceInitializationRun.run x q) _).2 hprevious
      have hfout : (ReferenceInitializationRun.finishBlock x
          (ReferenceInitializationRun.run x q) hblock).forcedFailure
          (ActualReferenceInitializationBlock.refFollower i) = false := by
        simpa [hfinish] using hfalse
      have hforcedFalse : ReferenceInitializationRun.forced x
          (ReferenceInitializationRun.run x q) hblock
          (ActualReferenceInitializationBlock.refFollower i) = false := by
        cases hforcedNow : ReferenceInitializationRun.forced x
            (ReferenceInitializationRun.run x q) hblock
            (ActualReferenceInitializationBlock.refFollower i) with
        | false => rfl
        | true =>
            have hfinishTrue : (ReferenceInitializationRun.finishBlock x
                (ReferenceInitializationRun.run x q) hblock).forcedFailure
                (ActualReferenceInitializationBlock.refFollower i) = true := by
              simp [ReferenceInitializationRun.finishBlock, hprior, hforcedNow]
            exact False.elim (Bool.noConfusion (hfinishTrue.symm.trans hfout))
      have hdecl : ReferenceInitializationRun.declaredActivation x
          (ReferenceInitializationRun.run x q) hblock
          (ActualReferenceInitializationBlock.refFollower i) = some a := by
        have hactivation := ha
        rw [hfinish] at hactivation
        change ReferenceInitializationRun.finalActivation x
          (ReferenceInitializationRun.run x q) hblock
          (ActualReferenceInitializationBlock.refFollower i) = some a at hactivation
        rw [ReferenceInitializationRun.finalActivation, hforcedFalse] at hactivation
        exact hactivation
      have hsave : (ReferenceInitializationRun.candidate x
          (ReferenceInitializationRun.run x q) hblock
          ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩).pending = true := by
        by_cases hpending : (ReferenceInitializationRun.candidate x
            (ReferenceInitializationRun.run x q) hblock
            ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩).pending = true
        · exact hpending
        · have hpendingFalse := Bool.eq_false_iff.mpr hpending
          simp [ReferenceInitializationRun.declaredActivation, hi, hpendingFalse] at hdecl
      have hsaved := ReferencePrelaunchLifecycleReplay.saved_declaration_initial_lifecycle
        x q hq hnone (ActualReferenceInitializationBlock.refFollower i) hi hsave
      have hstate : ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i) =
          ReferencePrelaunchFollower.initial p rate.eta := by
        rw [hfinish]
        simpa [x, ActualReferenceInitializationBlock.referenceInput] using hsaved.2.1
      exact ⟨a, ha, Or.inr ⟨hfalse, hordinaryReplay, Or.inl hstate⟩⟩
    · obtain ⟨aPrev, hprevious⟩ : ∃ aPrev,
          (ReferenceInitializationRun.run x q).activation
            (ActualReferenceInitializationBlock.refFollower i) = some aPrev := by
        cases hactivation : (ReferenceInitializationRun.run x q).activation
            (ActualReferenceInitializationBlock.refFollower i) with
        | none => exact False.elim (hprevious hactivation)
        | some aPrev => exact ⟨aPrev, rfl⟩
      have hsuccessor := generated_ordinary_successor_memory source rewards C_star C_h rate q
        hnone hblock i aPrev hprevious
      have hrunSucc : ReferenceInitializationRun.run x (q + 1) =
          ReferenceInitializationRun.finishBlock x (ReferenceInitializationRun.run x q) hblock := by
        rw [ReferenceInitializationRun.run_succ,
          ReferenceInitializationRun.advance_of_no_crossing x _ hnone hblock]
      have hordinaryBlock : ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i) =
          ReferencePrelaunchPhysicalReplay.blockReplay
            (ReferenceInitializationRun.replayInput x
              (ReferenceInitializationRun.run x q) hblock i aPrev hprevious) := by
        rw [hfinish, ← hrunSucc]
        exact hsuccessor.2.1
      have happend := hsuccessor.2.2.1
      exact ⟨a, ha, Or.inr ⟨hfalse, hordinaryReplay,
        Or.inr ⟨q, hq, hblock, hnone, aPrev, hprevious, hordinaryBlock, happend⟩⟩⟩

/-- The literal first-launch handoff. Its root retains the original complete
source, shared constants, capped rate, and whole reward table. -/
def correctedLaunch (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) : Option (ReferenceActivePhysicalStep.State p rate) :=
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  if hc : b.crossing.isSome = true then
    some {
      coordinator := .first
      upDecoderBank := CoordinatorUpReception.initialUpDecoderBank p
      activations := fun i =>
        (b.activation (ActualReferenceInitializationBlock.refFollower i)).get
          (ReferenceInitializationRun.run_all_activated_at_crossing x (n_boot p) hc
            (ActualReferenceInitializationBlock.refFollower i))
      followers := fun i => .ordinary
        (ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i))
        (ActiveFollowerLifecycle.initialMemory p)
    }
  else
    none

/-- The constructor is `none` exactly on the no-crossing branch. -/
theorem correctedLaunch_eq_none_iff (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    correctedLaunch rate source rewards C_star C_h = none ↔
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing = none := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  constructor
  · intro hnone
    by_contra hcross
    cases hh : b.crossing with
    | none => exact hcross hh
    | some crossing =>
        have hc : b.crossing.isSome = true := by simp [hh]
        simp [correctedLaunch, x, b, hc] at hnone
  · intro hcross
    simp [correctedLaunch, hcross]

/-- The option has a state exactly on the generated crossing branch. -/
theorem correctedLaunch_isSome_iff_crossing (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (correctedLaunch rate source rewards C_star C_h).isSome = true ↔
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  constructor
  · intro hsome
    by_contra hcross
    have hnone : b.crossing = none := by
      cases hh : b.crossing with
      | none => rfl
      | some crossing =>
          have hcrossB : b.crossing.isSome = true := by simp [hh]
          have hcrossRoot : (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true := by
            simpa [b] using hcrossB
          exact False.elim (hcross hcrossRoot)
    have hlaunchNone := (correctedLaunch_eq_none_iff rate source rewards C_star C_h).2
      (by simpa [b] using hnone)
    rw [hlaunchNone] at hsome
    cases hsome
  · intro hcross
    simp [correctedLaunch, hcross]

/-- Complete field characterization and uniqueness of the crossing state.
The activation getter is the unique source `Option` payload, not a fallback or
nonunique choice. -/
private theorem state_ext {rate : RateInput p} {s t : ReferenceActivePhysicalStep.State p rate}
    (hcoord : s.coordinator = t.coordinator)
    (hbank : s.upDecoderBank = t.upDecoderBank)
    (hactivation : ∀ i, s.activations i = t.activations i)
    (hfollowers : ∀ i, s.followers i = t.followers i) : s = t := by
  cases s with
  | mk sc sb sa sf =>
    cases t with
    | mk tc tb ta tf =>
      have hc : sc = tc := hcoord
      have hb : sb = tb := hbank
      have ha : sa = ta := funext hactivation
      have hf : sf = tf := funext hfollowers
      cases hc
      cases hb
      cases ha
      cases hf
      rfl

theorem correctedLaunch_crossing_characterization (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ∃! active : ReferenceActivePhysicalStep.State p rate,
      correctedLaunch rate source rewards C_star C_h = some active ∧
      active.coordinator = .first ∧
      active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      (∀ i, some (active.activations i) =
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).activation
          (ActualReferenceInitializationBlock.refFollower i)) ∧
      (∀ i, active.followers i = .ordinary
        (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate))
          (ActualReferenceInitializationBlock.refFollower i))
        (ActiveFollowerLifecycle.initialMemory p)) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  let active : ReferenceActivePhysicalStep.State p rate := {
    coordinator := .first
    upDecoderBank := CoordinatorUpReception.initialUpDecoderBank p
    activations := fun i =>
      (b.activation (ActualReferenceInitializationBlock.refFollower i)).get
        (ReferenceInitializationRun.run_all_activated_at_crossing x (n_boot p) hc
          (ActualReferenceInitializationBlock.refFollower i))
    followers := fun i => .ordinary
      (ReferenceInitializationRun.ordinary x b (ActualReferenceInitializationBlock.refFollower i))
      (ActiveFollowerLifecycle.initialMemory p)
  }
  have hlaunch : correctedLaunch rate source rewards C_star C_h = some active := by
    simp [correctedLaunch, x, b, active, hc]
  refine ⟨active, ?_, ?_⟩
  · refine ⟨hlaunch, rfl, rfl, ?_, ?_⟩
    · intro i
      exact Option.some_get _
    · intro i
      obtain ⟨a, ha, hprovenance⟩ := output_memory_provenance source rewards C_star C_h rate hc i
      rcases hprovenance with hforced | hordinary
      · rw [hforced.2.2.2]
        rfl
      · have hmemory := output_replay_memory_characterization
          source rewards C_star C_h rate i a ha
        obtain ⟨memory, hrecurrence, _⟩ := hmemory.2.1
        have hterminal := hmemory.2.2 memory hrecurrence.1 hrecurrence.2
        change active.followers i = .ordinary (ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i)) (ActiveFollowerLifecycle.initialMemory p)
        rw [← hterminal.2]
        exact congrArg (fun m => DeclaredFollowerLocalRound.LocalConfiguration.ordinary
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i)) m) hterminal.2.symm
  · intro other hother
    rcases hother with ⟨_, hcoord, hbank, hacts, hfollowers⟩
    apply state_ext
    · exact hcoord
    · exact hbank
    · intro i
      have hactive : some (active.activations i) = b.activation
          (ActualReferenceInitializationBlock.refFollower i) := by
        have hsome := ReferenceInitializationRun.run_all_activated_at_crossing
          x (n_boot p) hc (ActualReferenceInitializationBlock.refFollower i)
        change (b.activation (ActualReferenceInitializationBlock.refFollower i)).isSome = true at hsome
        cases hactivation : b.activation (ActualReferenceInitializationBlock.refFollower i) with
        | none => simp [hactivation] at hsome
        | some a => simp [active, hactivation]
      exact Option.some.inj ((hacts i).trans hactive.symm)
    · intro i
      simpa [active, x, b] using hfollowers i

/-- The exhaustion branch has all `T` source history entries, launch round
`T+1`, and no learner. -/
theorem correctedLaunch_no_crossing_source (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hnone : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing = none) :
    correctedLaunch rate source rewards C_star C_h = none ∧
    ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T ∧
    ReferenceInitializationRun.launchRound
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) = p.T + 1 ∧
    ReferenceInitializationRun.coordinatorLearner
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) = none := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  refine ⟨(correctedLaunch_eq_none_iff rate source rewards C_star C_h).2 hnone,
    ReferenceInitializationRun.output_elapsed_of_no_crossing x hnone, ?_, ?_⟩
  · simp [ReferenceInitializationRun.launchRound, hnone]
  · simp [ReferenceInitializationRun.coordinatorLearner, hnone]

/-- The output activation bounds give precisely the existing physical
all-active mode at the computed first launch. -/
theorem correctedLaunch_all_active_at_start (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ∃ active, correctedLaunch rate source rewards C_star C_h = some active ∧
      ReferenceActivePhysicalHorizon.allActiveAtStart active
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed) := by
  obtain ⟨active, ⟨hlaunch, _, _, hactivation, _⟩, _⟩ :=
    correctedLaunch_crossing_characterization rate source rewards C_star C_h hc
  refine ⟨active, hlaunch, ?_⟩
  intro i
  exact (ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).activation_le
      (ActualReferenceInitializationBlock.refFollower i) (active.activations i)
      (hactivation i).symm

/-- A genuine crossing produces a first active state at its exact clipped
boundary time. The launch round is `start + 1`, including `start = T`. -/
theorem correctedLaunch_crossing_source (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    ∃ active, correctedLaunch rate source rewards C_star C_h = some active ∧
      ReferenceInitializationRun.elapsed p b.completed ≤ p.T ∧
      ReferenceInitializationRun.launchRound x =
        ReferenceInitializationRun.elapsed p b.completed + 1 ∧
      (∀ i : Fin (p.m - 1), (active.activations i).val ≤
        ReferenceInitializationRun.elapsed p b.completed + 1) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  obtain ⟨active, ⟨hlaunch, _, _, hactivation, _⟩, _⟩ :=
    correctedLaunch_crossing_characterization rate source rewards C_star C_h hc
  refine ⟨active, hlaunch, ReferenceInitializationRun.elapsed_le_T p b.completed, ?_, ?_⟩
  · have hcross : b.crossing.isSome = true := by simpa [b] using hc
    change (if b.crossing.isSome then
      ReferenceInitializationRun.elapsed p b.completed + 1 else p.T + 1) =
        ReferenceInitializationRun.elapsed p b.completed + 1
    simp [hcross]
  · intro i
    exact b.activation_le (ActualReferenceInitializationBlock.refFollower i)
      (active.activations i) (hactivation i).symm

/-- The first active state retains every complete source local state and a
fresh proposal memory. The source launch registers, unoccupied status, and all
local domains are proved follower by follower. -/
theorem correctedLaunch_follower_source_fields (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    ∃ active, correctedLaunch rate source rewards C_star C_h = some active ∧
      (∀ i : Fin (p.m - 1),
        let state := ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i)
        active.followers i = .ordinary state (ActiveFollowerLifecycle.initialMemory p) ∧
        state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
        state.status = .unoccupied ∧
        ActiveFollowerLifecycle.localStateDomainValid state) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  obtain ⟨active, ⟨hlaunch, _, _, _, hfollowers⟩, _⟩ :=
    correctedLaunch_crossing_characterization rate source rewards C_star C_h hc
  refine ⟨active, hlaunch, ?_⟩
  intro i
  let follower := ActualReferenceInitializationBlock.refFollower i
  let state := ReferenceInitializationRun.ordinary x b follower
  have hfields := ReferenceInitializationRun.output_launch_state x hc follower
  have hdomain : ActiveFollowerLifecycle.localStateDomainValid state := by
    obtain ⟨a, ha, hmemory⟩ := output_memory_provenance source rewards C_star C_h rate hc i
    cases hmemory with
    | inl hforced =>
        rcases hforced with ⟨_, hstate, _⟩
        let empty : ReferencePrelaunchFollower.LocalHistory p 0 := fun u => Fin.elim0 u
        have hdomain0 := ActualReferenceInitializationBlock.replay_domain_valid
          rate.eta i x.row a empty (by omega)
        have hinitial := ReferencePrelaunchFollower.replay_before_activation
          rate.eta i x.row a empty (by omega) (by have := a.property.1; omega)
        rw [hinitial] at hdomain0
        change ActiveFollowerLifecycle.localStateDomainValid
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i))
        rw [hstate]
        exact hdomain0
    | inr hordinary =>
        rcases hordinary with ⟨_, hstate, _sourceBranch⟩
        have hdomainReplay := ActualReferenceInitializationBlock.replay_domain_valid
          rate.eta i x.row a
          (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m follower))
          (ReferenceInitializationRun.elapsed_le_T p b.completed)
        change ActiveFollowerLifecycle.localStateDomainValid
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i))
        rw [hstate]
        exact hdomainReplay
  exact ⟨hfollowers i, hfields.2.1, hfields.2.2.1, hfields.2.2.2.1,
    hfields.2.2.2.2.1, hfields.2.2.2.2.2.1, hfields.2.2.2.2.2.2, hdomain⟩

/-- Ordinary UP reception is disabled at every generated prefix boundary.
Before crossing there is no ordinary coordinator learner. Thus the first
handoff carries the original initial UP bank, without a later-bank reset. -/
theorem generated_coordinator_inactive_prefix
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (rate : RateInput p) (r : ℕ) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.run x r
    ReferenceInitializationRun.coordinatorUpEnabled b = false ∧
      (b.crossing = none → ReferenceInitializationRun.coordinatorLearner b = none) := by
  refine ⟨rfl, ?_⟩
  intro hc
  simp only [ReferenceInitializationRun.coordinatorLearner, hc, Option.isSome_none,
    Bool.false_eq_true, ↓reduceIte]

/-- Coordinator provenance for the first handoff: UP reception is disabled
through the inactive prefix, so the original bank is still its initial bank.
The first crossing also has the source zero-learner registers. -/
theorem correctedLaunch_coordinator_provenance (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ∃ active, correctedLaunch rate source rewards C_star C_h = some active ∧
      active.coordinator = .first ∧
      active.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p ∧
      ReferenceInitializationRun.coordinatorUpEnabled
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) = false ∧
      ReferenceInitializationRun.coordinatorLearner
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)) =
        some (RecordedQueueRun.initialState p.K) ∧
      (∀ arm : Fin p.K,
        (RecordedQueueRun.initialState p.K).registers arm = (0, 0) ∧
        (RecordedQueueRun.initialState p.K).records arm = [] ∧
        (RecordedQueueRun.initialState p.K).overflow = false) := by
  obtain ⟨active, ⟨hlaunch, hcoord, hbank, _, _⟩, _⟩ :=
    correctedLaunch_crossing_characterization rate source rewards C_star C_h hc
  have hup := (generated_coordinator_inactive_prefix source rewards C_star C_h rate
    (n_boot p)).1
  refine ⟨active, hlaunch, hcoord, hbank, hup,
    ReferenceInitializationRun.coordinatorLearner_at_crossing _ hc, ?_⟩
  intro arm
  exact ReferenceInitializationRun.coordinatorLearner_zero arm

/-- Initialization failure remains the existing forced-correction OR
suppressed-DOWN event, with its original selected-row source. -/
theorem correctedLaunch_failure_provenance (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    (∃ i : ActiveRoundActions.Follower p.m,
      ReferenceInitializationRun.initializationFailure x
        (ReferenceInitializationRun.output x) i = true) ↔
      InitializationFailureProvenance.operationalInitializationFailure x := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  exact InitializationFailureProvenance.initializationFailure_iff_operational x

/-- A forced correction keeps its global failure bit even though its newly
initialized ordinary state has no suppression flag. Its first local call is
at the computed next round, including `T+1` on terminal crossing. -/
theorem output_forced_failure_retained (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (i : Fin (p.m - 1)) :
    let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b := ReferenceInitializationRun.output x
    b.forcedFailure (ActualReferenceInitializationBlock.refFollower i) = true →
      ReferenceInitializationRun.initializationFailure x b
        (ActualReferenceInitializationBlock.refFollower i) = true ∧
      (ReferenceInitializationRun.ordinary x b
        (ActualReferenceInitializationBlock.refFollower i)).initializationFailure = false ∧
      ∃ a, b.activation (ActualReferenceInitializationBlock.refFollower i) = some a ∧
        a.val = ReferenceInitializationRun.elapsed p b.completed + 1 := by
  dsimp only
  intro hf
  obtain ⟨a, ha, hprovenance⟩ := output_memory_provenance source rewards C_star C_h rate hc i
  rcases hprovenance with hforced | hordinary
  · refine ⟨?_, ?_, a, ha, hforced.2.2.1⟩
    · simp only [ReferenceInitializationRun.initializationFailure, hf, Bool.true_or]
    · rw [hforced.2.1]
      rfl
  · rw [hordinary.1] at hf
    cases hf

/-- The terminal crossing remains `some`, even though its launch round is the
sentinel `T+1`. -/
theorem correctedLaunch_terminal_crossing (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hterminal : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T) :
    correctedLaunch rate source rewards C_star C_h ≠ none ∧
    ReferenceInitializationRun.launchRound
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) = p.T + 1 := by
  refine ⟨?_, ?_⟩
  · intro hnone
    have hcross := (correctedLaunch_eq_none_iff rate source rewards C_star C_h).mp hnone
    simp [hcross] at hc
  · simp [ReferenceInitializationRun.launchRound, hc, hterminal]

/-- The generated boundary supplies the DOWN seed to the existing canonical
postlaunch run. No seed, state, or all-active premise is an input. -/
theorem correctedLaunch_downBatchSeed (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true) :
    ∃ active, correctedLaunch rate source rewards C_star C_h = some active ∧
      ReferenceFollowerDecoderChronology.downBatchSeed active
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  obtain ⟨active, ⟨hlaunch, _, _, hactivation, hfollowers⟩, _⟩ :=
    correctedLaunch_crossing_characterization rate source rewards C_star C_h hc
  refine ⟨active, hlaunch, ?_⟩
  intro i
  obtain ⟨a, ha, hmemory⟩ := output_memory_provenance source rewards C_star C_h rate hc i
  cases hmemory with
  | inl hforced =>
      rcases hforced with ⟨_, hstate, _⟩
      obtain ⟨hwell, hchron, hstamp⟩ :=
        ReferenceFollowerDecoderChronology.initial_downBatchEndpoint
          (ReferenceInitializationRun.elapsed p b.completed)
      refine ⟨ReferencePrelaunchFollower.initial p rate.eta,
        ActiveFollowerLifecycle.initialMemory p, ?_, rfl, hwell, hchron, hstamp⟩
      rw [hfollowers i, hstate]
  | inr hordinary =>
      rcases hordinary with ⟨_, hstate, _sourceBranch⟩
      have hdown := ReferenceFollowerDecoderChronology.replay_downBatchEndpoint
        (rate := rate)
        (i := i) (row := x.row) (activation := a)
        (history := b.history (PublicDiscreteDraws.followerPlayer p.two_le_m
          (ActualReferenceInitializationBlock.refFollower i)))
        (hn := ReferenceInitializationRun.elapsed_le_T p b.completed)
      have hdownSource :
          (ReferenceInitializationRun.ordinary x b
            (ActualReferenceInitializationBlock.refFollower i)).status = .unoccupied ∧
          ReferenceFollowerDecoderChronology.downBatchWellFormed
            (ReferenceInitializationRun.ordinary x b
              (ActualReferenceInitializationBlock.refFollower i)).downBatch ∧
          ReferenceFollowerDecoderChronology.downCollectedChronological
            (ReferenceInitializationRun.ordinary x b
              (ActualReferenceInitializationBlock.refFollower i)).downBatch ∧
          (∀ entry ∈ AffineBatchDecoder.collected
              (ReferenceInitializationRun.ordinary x b
                (ActualReferenceInitializationBlock.refFollower i)).downBatch,
            entry.time.val < ReferenceInitializationRun.elapsed p b.completed) := by
        rw [← hstate] at hdown
        exact hdown
      refine ⟨ReferenceInitializationRun.ordinary x b
          (ActualReferenceInitializationBlock.refFollower i),
        ActiveFollowerLifecycle.initialMemory p, ?_, hdownSource.1, hdownSource.2.1,
        hdownSource.2.2.1, hdownSource.2.2.2⟩
      rw [hfollowers i]

/-- The selected original row, all complete rows, and whole reward table are
passed to the existing horizon with the constructed state and computed mode.
For terminal `count = 0`, the existing zero-run equations preserve the empty
suffix without an action at calendar coordinate `T`. -/
theorem correctedLaunch_run_downBatch_spec (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    ∃ active, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed),
      ∃ _hseed : ReferenceFollowerDecoderChronology.downBatchSeed active
        (ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed),
      correctedLaunch rate source rewards C_star C_h = some active ∧
      ∀ i state memory,
        (hordinary : (ReferenceActivePhysicalHorizon.run active source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
          count hspan hmode).finalState.followers i = .ordinary state memory) →
        ReferenceFollowerDecoderChronology.downBatchEndpoint state
          (ReferenceInitializationRun.elapsed p
            (ReferenceInitializationRun.output
              (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count) ∧
        (state.status ≠ .unoccupied → state.downBatch.pending = []) := by
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b := ReferenceInitializationRun.output x
  obtain ⟨active, ⟨hlaunch, _, _, hactivation, _⟩, _⟩ :=
    correctedLaunch_crossing_characterization rate source rewards C_star C_h hc
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active
      (ReferenceInitializationRun.elapsed p b.completed) := by
    intro i
    exact b.activation_le (ActualReferenceInitializationBlock.refFollower i)
      (active.activations i) (hactivation i).symm
  obtain ⟨active', hlaunch', hseed'⟩ :=
    correctedLaunch_downBatchSeed rate source rewards C_star C_h hc
  have hactive : active = active' := Option.some.inj (hlaunch.symm.trans hlaunch')
  subst active'
  refine ⟨active, hmode, hseed', hlaunch, ?_⟩
  intro i state memory hordinary
  exact ReferenceFollowerDecoderChronology.run_downBatch_spec active source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
    (ReferenceInitializationRun.elapsed p b.completed) count hspan hmode hseed' i state memory
    hordinary

/-- A terminal crossing still constructs the active state, and the existing
`run_zero_final`/`run_zero_records` equations give its empty physical suffix. -/
theorem correctedLaunch_terminal_run_zero (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hterminal : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed = p.T) :
    ∃ active, ∃ hmode : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T,
      correctedLaunch rate source rewards C_star C_h = some active ∧
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T 0
        (by omega) hmode).finalState = active ∧
      (ReferenceActivePhysicalHorizon.run active source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T 0
        (by omega) hmode).records = [] := by
  obtain ⟨active, hlaunch, hmode⟩ :=
    correctedLaunch_all_active_at_start rate source rewards C_star C_h hc
  have hmodeT : ReferenceActivePhysicalHorizon.allActiveAtStart active p.T := by
    simpa [hterminal] using hmode
  refine ⟨active, hmodeT, hlaunch, ?_, ?_⟩
  · exact ReferenceActivePhysicalHorizon.run_zero_final active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T (by omega) hmodeT
  · exact ReferenceActivePhysicalHorizon.run_zero_records active source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards p.T (by omega) hmodeT

end Bandits.Support.ReferenceCorrectedInitializationLaunch

end
