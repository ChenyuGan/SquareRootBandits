/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationTerminalBoundary
public import Bandits.Support.ReferenceActivePhysicalStep

import Lean.Elab.Tactic.Omega

/-!
# Canonical physical state at an actual initialization launch

Sources: `sources/zip4/manuscript/07_public_setup.tex:39-57,63-140`,
`sources/zip4/manuscript/06_interruptions.tex:41-70`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`.

This module converts the actual computed launched boundary handoff into the
existing postlaunch state. It consumes the accepted terminal one-block
comparison under its explicit prior-prefix and current-event inputs. The
conversion performs no physical round, draws no private coordinate, and does
not construct an assignment.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.ReferenceInitializationRun
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualReferenceInitializationTerminalBoundary
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.DeclaredFollowerLocalRound

namespace Bandits.Support.ActualInitializationLaunchState

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters}

/-- The activation carried by one boundary output when its actual handoff
certificate rules out bootstrap continuation. -/
def outputActivation {rate : RateInput p} (selected : Fin (M p))
    (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate)
    (hordinary : ∃ activation state memory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
        .declared selected activation (.ordinary state memory)) :
    ReferencePrelaunchFollower.Activation p := by
  cases output with
  | continueBootstrap numerators lowerBound activation =>
      have hfalse : False := by
        rcases hordinary with ⟨activation, state, memory, hcarry⟩
        simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
      exact False.elim hfalse
  | firstDeclaration row activation state memory => exact activation
  | preserveDeclared row activation configuration => exact activation

/-- The existing local configuration stored by a boundary output. A first
declaration uses its own output state and memory; a preserved declaration
returns its carried ordinary configuration unchanged. -/
def outputConfiguration {rate : RateInput p} (selected : Fin (M p))
    (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate)
    (hordinary : ∃ activation state memory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
        .declared selected activation (.ordinary state memory)) :
    DeclaredFollowerLocalRound.LocalConfiguration p rate := by
  cases output with
  | continueBootstrap numerators lowerBound activation =>
      have hfalse : False := by
        rcases hordinary with ⟨activation, state, memory, hcarry⟩
        simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
      exact False.elim hfalse
  | firstDeclaration row activation state memory => exact .ordinary state memory
  | preserveDeclared row activation configuration =>
      cases configuration with
      | ordinary state memory => exact .ordinary state memory
      | dagger =>
          have hfalse : False := by
            rcases hordinary with ⟨activation, state, memory, hcarry⟩
            simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
          exact False.elim hfalse

private theorem outputActivation_eq_of_carry {rate : RateInput p}
    (selected : Fin (M p)) (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate)
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hcarry : ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
      .declared selected activation (.ordinary state memory)) :
    outputActivation selected output ⟨activation, state, memory, hcarry⟩ = activation := by
  cases output with
  | continueBootstrap numerators lowerBound outputActivation =>
      simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
  | firstDeclaration row outputActivation outputState outputMemory =>
      simp only [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
      cases hcarry
      rfl
  | preserveDeclared row outputActivation configuration =>
      cases configuration with
      | ordinary outputState outputMemory =>
          simp only [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
          cases hcarry
          rfl
      | dagger => simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry

private theorem outputConfiguration_eq_of_carry {rate : RateInput p}
    (selected : Fin (M p)) (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate)
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hcarry : ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
      .declared selected activation (.ordinary state memory)) :
    outputConfiguration selected output ⟨activation, state, memory, hcarry⟩ =
      .ordinary state memory := by
  cases output with
  | continueBootstrap numerators lowerBound outputActivation =>
      simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
  | firstDeclaration row outputActivation outputState outputMemory =>
      simp only [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
      cases hcarry
      rfl
  | preserveDeclared row outputActivation configuration =>
      cases configuration with
      | ordinary outputState outputMemory =>
          simp only [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
          cases hcarry
          rfl
      | dagger => simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry

private theorem outputConfiguration_preserveDeclared {rate : RateInput p}
    (selected : Fin (M p)) (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate)
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∃ outputActivation state memory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
        .declared selected outputActivation (.ordinary state memory))
    (houtput : output = .preserveDeclared selected activation (.ordinary state memory)) :
    outputConfiguration selected output hordinary = .ordinary state memory := by
  subst output
  rfl

private theorem outputCarry_eq {rate : RateInput p} (selected : Fin (M p))
    (output : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate)
    (hordinary : ∃ activation state memory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
        .declared selected activation (.ordinary state memory)) :
    ActualInitializationRun.followerCarryOfBoundaryOutput rate output =
      .declared selected (outputActivation selected output hordinary)
        (outputConfiguration selected output hordinary) := by
  cases output with
  | continueBootstrap numerators lowerBound activation =>
      have hfalse : False := by
        rcases hordinary with ⟨activation, state, memory, hcarry⟩
        simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
      exact False.elim hfalse
  | firstDeclaration row activation state memory =>
      rcases hordinary with ⟨witnessActivation, witnessState, witnessMemory, hcarry⟩
      have hrow : some row = some selected := by
        have hrow := congrArg
          (fun carry : ActualInitializationRun.FollowerCarry p rate =>
            match carry with
            | .bootstrap _ _ => none
            | .declared row _ _ => some row) hcarry
        simpa [ActualInitializationRun.followerCarryOfBoundaryOutput] using hrow
      have hrow' : row = selected := Option.some.inj hrow
      simp [outputActivation, outputConfiguration,
        ActualInitializationRun.followerCarryOfBoundaryOutput, hrow']
  | preserveDeclared row activation configuration =>
      cases configuration with
      | ordinary state memory =>
          rcases hordinary with ⟨witnessActivation, witnessState, witnessMemory, hcarry⟩
          have hrow : some row = some selected := by
            have hrow := congrArg
              (fun carry : ActualInitializationRun.FollowerCarry p rate =>
                match carry with
                | .bootstrap _ _ => none
                | .declared row _ _ => some row) hcarry
            simpa [ActualInitializationRun.followerCarryOfBoundaryOutput] using hrow
          have hrow' : row = selected := Option.some.inj hrow
          simp [outputActivation, outputConfiguration,
            ActualInitializationRun.followerCarryOfBoundaryOutput, hrow']
      | dagger =>
          have hfalse : False := by
            rcases hordinary with ⟨activation, state, memory, hcarry⟩
            simp [ActualInitializationRun.followerCarryOfBoundaryOutput] at hcarry
          exact False.elim hfalse

/-- The canonical state immediately after the actual combined handoff has
launched `launch` with its accepted `learnerSeed`. The original full source,
reward table, shared constants, prior boundary and carry, chronological past,
prior `BlockStartRelated` proof, generated-DOWN exclusion, selected-row clean
prefix, post-pending force complement, and computed handoff equality remain
explicit inputs. -/
noncomputable def ofActualLaunchedBoundary
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
      (ActualReferenceInitializationBlock.referenceInput
            source rewards C_star C_h rate) b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    ReferenceActivePhysicalStep.State p rate := by
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h folded
  have hrelated := ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hordinary : ∀ i, ∃ activation state memory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
        .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
          (.ordinary state memory) := by
    intro i
    rcases hrelated.2.2.2.2 i with
      ⟨activation, state, memory, hcarry, _, _, _, _, _, _, _⟩
    exact ⟨activation, state, memory, hcarry⟩
  exact {
    coordinator := .first
    upDecoderBank := CoordinatorUpReception.initialUpDecoderBank p
    activations := fun i => outputActivation
      (ActualInitializationPhysicalStep.selectedRowIndex p source) (handoff.followers i)
      (hordinary i)
    followers := fun i => outputConfiguration
      (ActualInitializationPhysicalStep.selectedRowIndex p source) (handoff.followers i)
      (hordinary i)
  }

section LaunchInputs

variable
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ)
    (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < BootstrapDimensions.n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate
      (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : ActualReferenceInitializationBlock.BlockStartRelated source rewards
      C_star C_h rate (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : ActualReferenceInitializationBlock.refFollower i ∈
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          b h)
        source.1.2 ⟨ActualReferenceInitializationBlock.refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed)

include source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched

/-- The actual first postlaunch coordinator phase is the existing `.first`
phase. Its first physical StartRound will make the accepted first assignment. -/
theorem ofActualLaunchedBoundary_coordinator :
    (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).coordinator = .first := rfl

/-- The UP decoder is initialized once at launch, after being disabled during
initialization. Later assignment and cutoff transitions carry this bank. -/
theorem ofActualLaunchedBoundary_upDecoderBank :
    (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).upDecoderBank =
        CoordinatorUpReception.initialUpDecoderBank p := rfl

omit hclean hforce in
/-- The seed actually selected by the computed crossing has zero base scores
and queues; the launch conversion does not introduce a second seed. -/
theorem ofActualLaunchedBoundary_seed_zero :
    ∀ arm, learnerSeed.baseScores arm = 0 ∧ learnerSeed.queues arm = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hzero, _, _⟩ :=
    ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_crossing
      source rewards rate C_star C_h b h actual past hr hdown launch learnerSeed hlaunched
  exact hzero

omit hclean hforce in
/-- The accepted strict crossing places the source launch monitor exactly at
the exclusive end of this clipped block. -/
theorem ofActualLaunchedBoundary_launchPosition_eq_blockStop :
    launch.monitor.launchPosition =
      BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) := by
  obtain ⟨_, _, _, _, _, _, _, _, hposition, _, _, _, _⟩ :=
    ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_crossing
      source rewards rate C_star C_h b h actual past hr hdown launch learnerSeed hlaunched
  exact hposition

omit hclean hforce in
/-- The same accepted crossing identifies the reference activation endpoint
with the actual monitor launch position plus one. -/
theorem ofActualLaunchedBoundary_activationEndpoint :
    (ReferenceInitializationRun.boundaryActivation b).val = launch.monitor.launchPosition + 1 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hendpoint, _, _, _⟩ :=
    ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_crossing
      source rewards rate C_star C_h b h actual past hr hdown launch learnerSeed hlaunched
  exact hendpoint

omit hclean hforce in
/-- The terminal source endpoint is `T + 1`; this is only an activation
coordinate, with no physical time or action at that value. -/
theorem ofActualLaunchedBoundary_terminalEndpoint
    (hstop : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) = p.T) :
    launch.monitor.launchPosition + 1 = p.T + 1 := by
  rw [ofActualLaunchedBoundary_launchPosition_eq_blockStop source rewards rate C_star C_h
    b h actual past hr hdown launch learnerSeed hlaunched]
  rw [hstop]

/-- Every follower's converted carry is the actual selected-row declaration,
with the activation and whole local configuration stored in the canonical
state itself. -/
theorem ofActualLaunchedBoundary_followerCarry (i : Fin (p.m - 1)) :
    let block := ReferenceInitializationRun.nextBlock b h
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate block source rewards actual)
    ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
      .declared (ActualInitializationPhysicalStep.selectedRowIndex p source)
        ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
          hforce launch learnerSeed hlaunched).activations i)
        ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
          hforce launch learnerSeed hlaunched).followers i) := by
  let block := ReferenceInitializationRun.nextBlock b h
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h
    (ActualInitializationRun.foldBlock p rate block source rewards actual)
  have hrelated := ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  have hordinary : ∃ activation state memory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
        .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
          (.ordinary state memory) := by
    rcases hrelated.2.2.2.2 i with
      ⟨activation, state, memory, hcarry, _, _, _, _, _, _, _⟩
    exact ⟨activation, state, memory, hcarry⟩
  change ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
    .declared (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (outputActivation (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (handoff.followers i) hordinary)
      (outputConfiguration (ActualInitializationPhysicalStep.selectedRowIndex p source)
        (handoff.followers i) hordinary)
  exact outputCarry_eq _ _ hordinary

omit hclean hforce launch learnerSeed hlaunched in
/-- For an incoming ordinary declaration, the actual boundary adapter uses
`preserveDeclared`: it retains the original proposal memory and carries the
ordinary state after this block's accepted replay. -/
theorem ofActualLaunchedBoundary_preserveDeclared
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hactual : actual.followers i = .declared row activation (.ordinary state memory)) :
    let block := ReferenceInitializationRun.nextBlock b h
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate block source rewards actual)
    handoff.followers i =
      .preserveDeclared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
        (.ordinary (ReferenceInitializationRun.ordinary
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
          (ReferenceInitializationRun.finishBlock
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
            b h) (ActualReferenceInitializationBlock.refFollower i)) memory) := by
  exact ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_preserveDeclared
    source rewards rate C_star C_h b h actual past hr hdown i row activation state memory hactual

/-- The canonical follower configuration on an incoming ordinary declaration
retains its exact proposal memory. Its state is the accepted replay of the
full original history, including any existing buffer and incomplete DOWN bank. -/
theorem ofActualLaunchedBoundary_preservedConfiguration
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hactual : actual.followers i = .declared row activation (.ordinary state memory)) :
    (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).followers i =
      .ordinary (ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.finishBlock
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        (ActualReferenceInitializationBlock.refFollower i)) memory := by
  let block := ReferenceInitializationRun.nextBlock b h
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h
    (ActualInitializationRun.foldBlock p rate block source rewards actual)
  have hrelated := ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  rcases hrelated.2.2.2.2 i with
    ⟨outputActivation, outputState, outputMemory, hcarry, _, _, _, _, _, _, _⟩
  have hordinary : ∃ outputActivation outputState outputMemory,
      ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
        .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) outputActivation
          (.ordinary outputState outputMemory) :=
    ⟨outputActivation, outputState, outputMemory, hcarry⟩
  have houtput := ofActualLaunchedBoundary_preserveDeclared source rewards rate C_star C_h b h
    actual past hr hdown i row activation state memory hactual
  change outputConfiguration (ActualInitializationPhysicalStep.selectedRowIndex p source)
    (handoff.followers i) _ = .ordinary (ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.finishBlock
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
      (ActualReferenceInitializationBlock.refFollower i)) memory
  exact outputConfiguration_preserveDeclared (ActualInitializationPhysicalStep.selectedRowIndex p source)
    (handoff.followers i) activation
    (ReferenceInitializationRun.ordinary
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
      (ReferenceInitializationRun.finishBlock
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
      (ActualReferenceInitializationBlock.refFollower i)) memory hordinary houtput

/-- Every stored ordinary follower state equals the state computed by the
reference `finishBlock` replay. The existential memory is the actual carried
memory from the computed boundary output. -/
theorem ofActualLaunchedBoundary_follower_replay (i : Fin (p.m - 1)) :
    ∃ (state : ReferencePrelaunchFollower.State p rate.eta)
      (memory : ActiveFollowerLifecycle.LocalMemory p),
      (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
        hforce launch learnerSeed hlaunched).followers i = .ordinary state memory ∧
      state = ReferenceInitializationRun.ordinary
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
        (ReferenceInitializationRun.finishBlock
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) b h)
        (ActualReferenceInitializationBlock.refFollower i) ∧
      state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
      state.status = .unoccupied ∧ state.initializationFailure = false := by
  let block := ReferenceInitializationRun.nextBlock b h
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h
    (ActualInitializationRun.foldBlock p rate block source rewards actual)
  have hrelated := ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  rcases hrelated.2.2.2.2 i with
    ⟨activation, state, memory, hcarry, hlast, haccepted, hscore, hdelta, hbacklog, hstatus,
      hfailure⟩
  have hrelation := hrelated.2.2.2.1 i
  rw [hcarry] at hrelation
  simp only [ActualReferenceInitializationBlock.follower_start_related] at hrelation
  obtain ⟨_, _, hstate, _, _, _, _, _, _, _, _⟩ := hrelation
  have hconfig :
      (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
        hforce launch learnerSeed hlaunched).followers i = .ordinary state memory := by
    change outputConfiguration (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (handoff.followers i) _ = .ordinary state memory
    exact outputConfiguration_eq_of_carry (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (handoff.followers i) activation state memory hcarry
  exact ⟨state, memory, hconfig, hstate, hlast, haccepted, hscore, hdelta, hbacklog, hstatus,
    hfailure⟩

/-- The full declared branch of `launched_related` supplies zero ordinary
registers and a false initialization-failure flag for each actual follower. -/
theorem ofActualLaunchedBoundary_follower_registers (i : Fin (p.m - 1)) :
    ∃ state memory,
      (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
        hforce launch learnerSeed hlaunched).followers i = .ordinary state memory ∧
      state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
      state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
      state.status = .unoccupied ∧ state.initializationFailure = false := by
  rcases ofActualLaunchedBoundary_follower_replay source rewards rate C_star C_h b h actual
      past hr hdown hclean hforce launch learnerSeed hlaunched i with
      ⟨state, memory, hconfig, _, hlast, haccepted, hscore, hdelta, hbacklog, hstatus, hfailure⟩
  exact ⟨state, memory, hconfig, hlast, haccepted, hscore, hdelta, hbacklog, hstatus, hfailure⟩

/-- The converted activation is bounded by the exact completed-block endpoint,
as obtained from the reference activation relation and its `activation_le`
field. -/
theorem ofActualLaunchedBoundary_activation_le_blockStop (i : Fin (p.m - 1)) :
    ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).activations i).val ≤
      BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1 := by
  let block := ReferenceInitializationRun.nextBlock b h
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h
    (ActualInitializationRun.foldBlock p rate block source rewards actual)
  let x := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let finished := ReferenceInitializationRun.finishBlock x b h
  have hrelated := ActualReferenceInitializationTerminalBoundary.combinedBoundaryHandoff_launched_related
    source rewards rate C_star C_h b h actual past hr hdown hclean hforce launch learnerSeed hlaunched
  rcases hrelated.2.2.2.2 i with
    ⟨activation, state, memory, hcarry, _, _, _, _, _, _, _⟩
  have hrelation := hrelated.2.2.2.1 i
  rw [hcarry] at hrelation
  simp only [ActualReferenceInitializationBlock.follower_start_related] at hrelation
  have hfinishActivation : finished.activation (ActualReferenceInitializationBlock.refFollower i) =
      some activation := hrelation.2.1
  have hbound := finished.activation_le
    (ActualReferenceInitializationBlock.refFollower i) activation hfinishActivation
  have hendpoint : ReferenceInitializationRun.elapsed p (b.completed + 1) =
      BootstrapObservedFollower.blockStop p block := by
    simp [ReferenceInitializationRun.elapsed, BootstrapObservedFollower.blockStop,
      ReferenceInitializationRun.nextBlock, block]
  have hbound' : activation.val ≤ BootstrapObservedFollower.blockStop p block + 1 := by
    rw [← hendpoint]
    exact hbound
  have hactivation :
      (ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
        hforce launch learnerSeed hlaunched).activations i = activation := by
    change outputActivation (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (handoff.followers i) _ = activation
    exact outputActivation_eq_of_carry (ActualInitializationPhysicalStep.selectedRowIndex p source)
      (handoff.followers i) activation state memory hcarry
  rw [hactivation]
  exact hbound'

/-- The accepted crossing theorem identifies the bound's endpoint with the
actual launch monitor's `launchPosition + 1`. -/
theorem ofActualLaunchedBoundary_activation_le_launchPosition (i : Fin (p.m - 1)) :
    ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).activations i).val ≤ launch.monitor.launchPosition + 1 := by
  have hbound := ofActualLaunchedBoundary_activation_le_blockStop source rewards rate C_star C_h
    b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  have hposition := ofActualLaunchedBoundary_launchPosition_eq_blockStop source rewards rate
    C_star C_h b h actual past hr hdown launch learnerSeed hlaunched
  calc
    ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).activations i).val ≤
        BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h) + 1 :=
      hbound
    _ = launch.monitor.launchPosition + 1 := congrArg (fun n : ℕ => n + 1) hposition.symm

/-- Any genuine calendar time at or after the zero-based block endpoint is
active for every converted follower. Its source round number is `time.val + 1`. -/
theorem ofActualLaunchedBoundary_activeAtTime (time : Fin p.T)
    (htime : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) ≤ time.val) :
    ∀ i, ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
      hforce launch learnerSeed hlaunched).activations i).val ≤ time.val + 1 := by
  intro i
  have hactivation := ofActualLaunchedBoundary_activation_le_blockStop source rewards rate C_star C_h
    b h actual past hr hdown hclean hforce launch learnerSeed hlaunched i
  omega

/-- If the exclusive block endpoint is a real zero-based index below `T`,
the first physical source round in the active suffix is exactly `start + 1`. -/
theorem ofActualLaunchedBoundary_firstSourceRound
    (hstart : BootstrapObservedFollower.blockStop p
      (ReferenceInitializationRun.nextBlock b h) < p.T) :
    let start := BootstrapObservedFollower.blockStop p (ReferenceInitializationRun.nextBlock b h)
    let firstTime : Fin p.T := ⟨start, hstart⟩
    firstTime.val + 1 = start + 1 ∧
      ∀ i, ((ofActualLaunchedBoundary source rewards rate C_star C_h b h actual past hr hdown hclean
        hforce launch learnerSeed hlaunched).activations i).val ≤ firstTime.val + 1 := by
  dsimp
  constructor
  · rfl
  · intro i
    exact ofActualLaunchedBoundary_activeAtTime source rewards rate C_star C_h b h actual past hr
      hdown hclean hforce launch learnerSeed hlaunched ⟨_, hstart⟩ (by rfl) i

end LaunchInputs

end Bandits.Support.ActualInitializationLaunchState

end
