/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualReferenceInitializationBoundary

import Lean.Elab.Tactic.Omega

/-!
# Terminal one-block actual/reference initialization comparison

Sources: `sources/zip4/manuscript/07_public_setup.tex:39-57,63-140` and
`sources/zip4/manuscript/08_main_theorem.tex:29-42,67-83`.

Internal deterministic consumers of the accepted actual fold and boundary
comparison. Incoming relations concern only the prior physical prefix. The
current generated DOWN and incorrect-row prefix obstructions remain explicit;
only launch requires the literal post-pending force complement. No horizon
induction, probability estimate, postlaunch transition or manuscript closure
is asserted. Physical observations are indexed by `Fin T`, including when a
terminal declaration or launch becomes effective at `T + 1`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualReferenceInitializationBlock
open Bandits.Support.ActualReferenceInitializationFold
open Bandits.Support.ActualReferenceInitializationBoundary
open scoped Classical

namespace Bandits.Support.ActualReferenceInitializationTerminalBoundary

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := Bandits.Support.ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters}

private theorem boundary_follower_start_related
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (referenceInput source rewards C_star C_h rate) b h i = false)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (i : Fin (p.m - 1)) :
    follower_start_related (referenceInput source rewards C_star C_h rate)
      source rate rfl (ReferenceInitializationRun.finishBlock
        (referenceInput source rewards C_star C_h rate) b h) i (ActualInitializationRun.followerCarryAtBlockBoundary p rate
        (ReferenceInitializationRun.nextBlock b h)
        ((ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
          source rewards actual).followers i)) := by
  classical
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  let hrOriginal := hr
  rcases hr with ⟨hcompleted, hcrossing, hforced, hcounter, hstar, hch, hpast, hfollower⟩
  let boundaryCarry := ActualInitializationRun.followerCarryAtBlockBoundary p rate block
    (folded.followers i)
  change follower_start_related x source rate rfl
    (ReferenceInitializationRun.finishBlock x b h) i boundaryCarry
  have hforceNow : ReferenceInitializationRun.forced x b h (refFollower i) = false :=
    hforce (refFollower i)
  have hfinishForced :
      (ReferenceInitializationRun.finishBlock x b h).forcedFailure (refFollower i) = false := by
    change (b.forcedFailure (refFollower i) || ReferenceInitializationRun.forced x b h
      (refFollower i)) = false
    rw [hforced (refFollower i), hforceNow]
    rfl
  obtain ⟨hm, hcursor, _, _⟩ := foldBlock_related source rewards rate C_star C_h b h
    actual past hrOriginal hdown
  cases hactual : actual.followers i with
  | bootstrap numerators lower =>
      have hstart : b.activation (refFollower i) = none ∧ numerators = b.numerators i := by
        simpa [ActualReferenceInitializationBlock.follower_start_related, hactual] using
          hfollower i
      have hhi : refFollower i ∈
          (ReferenceInitializationRun.physical x b h).uninformed :=
        (ReferenceInitializationRun.mem_uninformed b (refFollower i)).2 hstart.1
      have hhiBare : refFollower i ∈ ReferenceInitializationRun.uninformed b := by
        change refFollower i ∈ (ReferenceInitializationRun.physical x b h).uninformed
        exact hhi
      obtain ⟨state, hout, _, _, _, hupdated, hpending, _, _⟩ :=
        foldBlock_bootstrap_comparison source rewards rate C_star C_h b h actual past hrOriginal hdown
          i hhi (hclean i hhi)
      have hpendingBare : BootstrapObservedFollower.pendingDeclaration state.blockCase =
          if (ReferenceInitializationRun.candidate x b h
            ⟨refFollower i, hhiBare⟩).pending = true then
            some (ActualInitializationPhysicalStep.selectedRowIndex p source) else none := by
        exact hpending
      cases hpend : BootstrapObservedFollower.pendingDeclaration state.blockCase with
      | none =>
          have hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending = false := by
            cases hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending with
            | false => rfl
            | true =>
                have heq := hpendingBare
                rw [hpend, hcand] at heq
                simp at heq
          have hactivation : (ReferenceInitializationRun.finishBlock x b h).activation
              (refFollower i) = none := by
            change ReferenceInitializationRun.finalActivation x b h (refFollower i) = none
            rw [ReferenceInitializationRun.finalActivation, hforceNow]
            simp [ReferenceInitializationRun.declaredActivation, hhiBare, hcand]
          have hmap : boundaryCarry = ActualInitializationRun.followerCarryAtBlockBoundary
              p rate block (folded.followers i) := rfl
          rw [hout] at hmap
          simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower, hpend] at hmap
          rw [hmap]
          change (ReferenceInitializationRun.finishBlock x b h).activation (refFollower i) = none ∧
            BootstrapObservedFollower.updatedNumerators p block state =
              (ReferenceInitializationRun.finishBlock x b h).numerators i
          refine ⟨hactivation, ?_⟩
          simpa [ReferenceInitializationRun.finishBlock] using hupdated
      | some row =>
          have hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending = true := by
            cases hcand : (ReferenceInitializationRun.candidate x b h
              ⟨refFollower i, hhiBare⟩).pending with
            | false =>
                have heq := hpendingBare
                rw [hpend, hcand] at heq
                simp at heq
            | true => rfl
          have hrow : row = ActualInitializationPhysicalStep.selectedRowIndex p source := by
            have heq := hpendingBare
            rw [hpend, hcand] at heq
            exact Option.some.inj heq
          have hstop : ReferenceInitializationRun.elapsed p (b.completed + 1) =
              BootstrapObservedFollower.blockStop p block := by
            simp [ReferenceInitializationRun.elapsed, block,
              ReferenceInitializationRun.nextBlock, BootstrapObservedFollower.blockStop]
          have hactivation : BootstrapObservedFollower.nextActivationRound p block =
              ReferenceInitializationRun.boundaryActivation b := by
            apply Subtype.ext
            simpa [BootstrapObservedFollower.nextActivationRound,
              ReferenceInitializationRun.boundaryActivation] using hstop.symm
          have hfinishActivation : (ReferenceInitializationRun.finishBlock x b h).activation
              (refFollower i) = some (BootstrapObservedFollower.nextActivationRound p block) := by
            rw [ReferenceInitializationRun.saved_activation x b h ⟨refFollower i, hhi⟩ hcand,
              hactivation]
          have hfinishOrd := ReferenceInitializationRun.ordinary_finishBlock_of_saved x b h
            ⟨refFollower i, hhi⟩ hcand (hforced (refFollower i))
          have hmap : boundaryCarry = ActualInitializationRun.followerCarryAtBlockBoundary
              p rate block (folded.followers i) := rfl
          rw [hout] at hmap
          simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower, hpend, Option.elim_some]
            at hmap
          have hmap' : boundaryCarry =
              .declared (ActualInitializationPhysicalStep.selectedRowIndex p source)
                (BootstrapObservedFollower.nextActivationRound p block)
                (.ordinary (ReferenceInitializationRun.ordinary x
                  (ReferenceInitializationRun.finishBlock x b h) (refFollower i))
                  (ActiveFollowerLifecycle.initialMemory p)) := by
            rw [hrow] at hmap
            rw [hfinishOrd]
            exact hmap
          have hfresh : ReferencePrelaunchFollower.replay rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) =
              ReferencePrelaunchFollower.initial p rate.eta := by
            exact ReferencePrelaunchFollower.replay_before_activation rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1)) (by
                rw [hactivation]
                simp [ReferenceInitializationRun.boundaryActivation,
                  ReferenceInitializationRun.finishBlock])
          have hfreshBuffer : (ReferencePrelaunchFollower.replay rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).buffer = [] := by
            simpa [ReferencePrelaunchFollower.initial] using
              congrArg (fun state => state.buffer) hfresh
          have hfreshDownBatch : (ReferencePrelaunchFollower.replay rate.eta i x.row
              (BootstrapObservedFollower.nextActivationRound p block)
              ((ReferenceInitializationRun.finishBlock x b h).history
                (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
              (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).downBatch =
              AffineBatchDecoder.initial p := by
            simpa [ReferencePrelaunchFollower.initial] using
              congrArg (fun state => state.downBatch) hfresh
          rw [hmap']
          unfold ActualReferenceInitializationBlock.follower_start_related
          refine ⟨rfl, hfinishActivation, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.2
          · simp [hfinishOrd, ReferencePrelaunchFollower.initial]
          · simpa [hfinishOrd, ReferencePrelaunchFollower.initial] using hfreshBuffer.symm
          · simpa [hfinishOrd, ReferencePrelaunchFollower.initial] using hfreshDownBatch.symm
  | declared row activation configuration =>
      cases configuration with
      | dagger =>
          have hfalse := hfollower i
          simp [hactual, ActualReferenceInitializationBlock.follower_start_related] at hfalse
      | ordinary state memory =>
          have hstart : row = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
              b.activation (refFollower i) = some activation ∧
              state = ReferenceInitializationRun.ordinary x b (refFollower i) ∧
              state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
              state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
              state.status = .unoccupied ∧ state.initializationFailure = false ∧
              state.buffer = (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed)).buffer ∧
              state.downBatch = (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                (b.history (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                (ReferenceInitializationRun.elapsed_le_T p b.completed)).downBatch := by
            simpa [ActualReferenceInitializationBlock.follower_start_related, hactual] using
              hfollower i
          have hout := foldBlock_declared_comparison source rewards rate C_star C_h b h
            actual past hrOriginal hdown i row activation state memory hactual
          have hmap : boundaryCarry = ActualInitializationRun.followerCarryAtBlockBoundary
              p rate block (folded.followers i) := rfl
          rw [hout] at hmap
          simp only [ActualInitializationRun.followerCarryAtBlockBoundary,
            ActualInitializationRun.followerCarryOfBoundaryOutput,
            ActualInitializationRun.boundaryOutputFromFollower] at hmap
          have hfinishActivation : (ReferenceInitializationRun.finishBlock x b h).activation
              (refFollower i) = some activation :=
            ReferenceInitializationRun.activated_activation x b h (refFollower i) activation hstart.2.1
          have hmap' : boundaryCarry =
              .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
                (.ordinary (ReferenceInitializationRun.ordinary x
                  (ReferenceInitializationRun.finishBlock x b h) (refFollower i)) memory) := by
            exact hmap
          have hrelOut := (hcursor.2.2.2.2 i).1
          rw [hout] at hrelOut
          simp only [ActualReferenceInitializationBlock.round_follower_related] at hrelOut
          obtain ⟨_, _, hstateReplay, hfailure⟩ := hrelOut
          have hordinaryFields :
              (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h)
                (refFollower i)).buffer =
                (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                  ((ReferenceInitializationRun.finishBlock x b h).history
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                  (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).buffer ∧
              (ReferenceInitializationRun.ordinary x (ReferenceInitializationRun.finishBlock x b h)
                (refFollower i)).downBatch =
                (ReferencePrelaunchFollower.replay rate.eta i x.row activation
                  ((ReferenceInitializationRun.finishBlock x b h).history
                    (PublicDiscreteDraws.followerPlayer p.two_le_m (refFollower i)))
                  (ReferenceInitializationRun.elapsed_le_T p (b.completed + 1))).downBatch := by
            unfold ReferenceInitializationRun.ordinary
            rw [hfinishForced, hfinishActivation]
            exact ReferencePrelaunchFollower.atLaunch_preserves _
          rw [hmap']
          unfold ActualReferenceInitializationBlock.follower_start_related
          refine ⟨rfl, hfinishActivation, rfl, ?_, ?_, ?_, ?_, ?_, ?_, hfailure, ?_, ?_⟩
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.1
          · exact (ReferenceInitializationRun.ordinary_registers x
              (ReferenceInitializationRun.finishBlock x b h) (refFollower i)).2.2.2.2.2
          · exact hordinaryFields.1
          · exact hordinaryFields.2

private theorem launched_handoff_phase
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : SourceInput p} {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards C_star C_h 0)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .launched launch learnerSeed) :
    folded.phase = .launched launch := by
  cases folded with
  | mk consumed phase followers records invariant consumed_eq_blockLength record_count chronological =>
      cases phase with
      | prelaunch live =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hlaunched
          by_cases hlast : block.val + 1 = n_boot p
          · simp [hlast] at hlaunched
          · simp [hlast] at hlaunched
      | launched active =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hlaunched
          cases hlaunched
          rfl

/-- The computed actual launch yields the reference's exact strict crossing,
whole updated counter vector, original constants, physical trigger and next
activation endpoint. The learner seed uses the accepted zero APIs. No follower
force complement is needed to compare the monitor. -/
theorem combinedBoundaryHandoff_launched_crossing
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    let x := referenceInput source rewards C_star C_h rate
    let block := ReferenceInitializationRun.nextBlock b h
    let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
    folded.phase = .launched launch ∧
      launch.data.block = block ∧
      launch.monitor.counters = (ReferenceInitializationRun.finishBlock x b h).counters ∧
      launch.data.C_star = C_star ∧ launch.data.C_h = C_h ∧
      ReferenceInitializationRun.crosses x b h = true ∧
      (ReferenceInitializationRun.finishBlock x b h).crossing = some block ∧
      launch.triggerRound.val + 1 = BootstrapObservedFollower.blockStop p block ∧
      launch.monitor.launchPosition = BootstrapObservedFollower.blockStop p block ∧
      (ReferenceInitializationRun.boundaryActivation b).val = launch.monitor.launchPosition + 1 ∧
      (∀ arm, learnerSeed.baseScores arm = 0 ∧ learnerSeed.queues arm = 0) ∧
      (∀ record ∈ folded.records, record.time.val < p.T) ∧
      (ReferenceInitializationRun.elapsed p (b.completed + 1) = p.T →
        (ReferenceInitializationRun.boundaryActivation b).val = p.T + 1 ∧
        launch.monitor.launchPosition + 1 = p.T + 1) := by
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  have hphase : folded.phase = .launched launch :=
    launched_handoff_phase folded launch learnerSeed hlaunched
  have haligned := folded.invariant.1
  rw [hphase] at haligned
  change launch.data.block = block ∧ launch.data.ids = source.1.1 ∧
    launch.data.row = source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) ∧
    launch.data.target = BootstrapPhysicalInput.targetArmMap p block source.2 ∧
    launch.data.C_star = actual.C_star ∧ launch.data.C_h = actual.C_h at haligned
  have hstar := haligned.2.2.2.2.1
  have hch := haligned.2.2.2.2.2
  have hstrict : BootstrapLaunchMonitor.monitorValue p folded.phase.monitorState.counters >
      4 * BootstrapStartupCostScale.Q actual.C_star actual.C_h p := by
    rw [hphase]
    change BootstrapLaunchMonitor.monitorValue p launch.monitor.counters > _
    rw [← hstar, ← hch]
    exact launch.strictThreshold
  have hcross : ReferenceInitializationRun.crosses x b h = true :=
    (foldBlock_strictCrossing_eq source rewards rate C_star C_h b h actual past hr hdown).mp hstrict
  have hcounters := foldBlock_updatedCounters_eq source rewards rate C_star C_h b h
    actual past hr hdown
  have hstop : launch.monitor.launchPosition = BootstrapObservedFollower.blockStop p block := by
    rw [ActualInitializationHorizon.launchedBlock_launchPosition_eq_blockStop, haligned.1]
  have helapsed : ReferenceInitializationRun.elapsed p (b.completed + 1) =
      BootstrapObservedFollower.blockStop p block := by
    simp only [ReferenceInitializationRun.elapsed, BootstrapObservedFollower.blockStop,
      block, ReferenceInitializationRun.nextBlock]
  have hactivation : (ReferenceInitializationRun.boundaryActivation b).val =
      launch.monitor.launchPosition + 1 := by
    rw [hstop]
    exact congrArg (fun n => n + 1) helapsed
  refine ⟨hphase, haligned.1, ?_, hstar.trans hr.2.2.2.2.1,
    hch.trans hr.2.2.2.2.2.1, hcross, ?_, ?_, hstop, hactivation, ?_, ?_, ?_⟩
  · change folded.phase.monitorState.counters = ReferenceInitializationRun.updatedCounters x b h
      at hcounters
    rw [hphase] at hcounters
    exact hcounters
  · change (if ReferenceInitializationRun.crosses x b h then some block else none) = some block
    rw [hcross]
    rfl
  · exact launch.launchPosition.symm.trans hstop
  · intro arm
    exact ⟨learnerSeed.baseScores_zero arm, learnerSeed.queues_zero arm⟩
  · intro record _
    exact record.time.isLt
  · intro hterminal
    have ha : (ReferenceInitializationRun.boundaryActivation b).val = p.T + 1 := by
      change ReferenceInitializationRun.elapsed p (b.completed + 1) + 1 = p.T + 1
      rw [hterminal]
    exact ⟨ha, hactivation.symm.trans ha⟩

/-- An old declaration produces the actual `preserveDeclared` output with
its original proposal memory, whole ordinary state, history buffer and partial
DOWN bank. Initial memory is used only by first declarations. -/
theorem combinedBoundaryHandoff_preserveDeclared
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (i : Fin (p.m - 1)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (state : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hactual : actual.followers i = .declared row activation (.ordinary state memory)) :
    let x := referenceInput source rewards C_star C_h rate
    let block := ReferenceInitializationRun.nextBlock b h
    let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
    (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h folded).followers i =
      .preserveDeclared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
        (.ordinary (ReferenceInitializationRun.ordinary x
          (ReferenceInitializationRun.finishBlock x b h) (refFollower i)) memory) := by
  change ActualInitializationRun.boundaryOutputFromFollower p rate
    (ReferenceInitializationRun.nextBlock b h)
    ((ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
      source rewards actual).followers i) = _
  rw [foldBlock_declared_comparison source rewards rate C_star C_h b h actual past hr hdown
    i row activation state memory hactual]
  rfl

/-- At actual launch, pending saves already agree with the selected true row.
The only extra event input is the literal post-pending force complement.
Every computed follower output is related to the completed reference boundary
and is an ordinary true-row declaration with the prescribed zero registers.
The entire actual record accumulator is consumed. -/
theorem combinedBoundaryHandoff_launched_related
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (hforce : ∀ i, ReferenceInitializationRun.forced
      (referenceInput source rewards C_star C_h rate) b h i = false)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunched : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .launched launch learnerSeed) :
    let x := referenceInput source rewards C_star C_h rate
    let block := ReferenceInitializationRun.nextBlock b h
    let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h folded
    let finished := ReferenceInitializationRun.finishBlock x b h
    (∀ i, (ReferenceInitializationRun.declaredActivation x b h i).isSome = true) ∧
      past_related (past ++ folded.records) finished ∧
      (∀ i, finished.forcedFailure i = false) ∧
      (∀ i, follower_start_related x source rate rfl finished i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i))) ∧
      (∀ i, ∃ activation state memory,
        ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i) =
          .declared (ActualInitializationPhysicalStep.selectedRowIndex p source) activation
            (.ordinary state memory) ∧
        state.lastDown = none ∧ ReferencePrelaunchFollower.acceptedStart state = 0 ∧
        state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0 ∧
        state.status = .unoccupied ∧ state.initializationFailure = false) := by
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h folded
  let finished := ReferenceInitializationRun.finishBlock x b h
  have hcross : ReferenceInitializationRun.crosses x b h = true :=
    (combinedBoundaryHandoff_launched_crossing source rewards rate C_star C_h b h
      actual past hr hdown launch learnerSeed hlaunched).2.2.2.2.2.1
  have hrelations (i : Fin (p.m - 1)) :
      follower_start_related x source rate rfl finished i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i)) := by
    exact boundary_follower_start_related source rewards rate C_star C_h b h
      actual past hr hdown hforce hclean i
  refine ⟨?_, foldBlock_past_related source rewards rate C_star C_h b h
    actual past hr hdown, ?_, hrelations, ?_⟩
  · intro i
    have hf := hforce i
    change ReferenceInitializationRun.forced x b h i = false at hf
    unfold ReferenceInitializationRun.forced at hf
    rw [hcross] at hf
    cases hd : ReferenceInitializationRun.declaredActivation x b h i with
    | none => simp only [hd, Option.isNone_none, Bool.and_self, Bool.true_eq_false] at hf
    | some activation => rfl
  · intro i
    change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = false
    rw [hr.2.2.1 i, hforce i]
    rfl
  · intro i
    have hrel := hrelations i
    have ha := ReferenceInitializationRun.finishBlock_all_activated x b h hcross (refFollower i)
    generalize he : ActualInitializationRun.followerCarryOfBoundaryOutput rate
      (handoff.followers i) = carry at hrel ⊢
    cases carry with
    | bootstrap numerators lower =>
        change finished.activation (refFollower i) = none ∧ _ at hrel
        change (finished.activation (refFollower i)).isSome = true at ha
        rw [hrel.1] at ha
        cases ha
    | declared row activation configuration =>
        cases configuration with
        | dagger => exact False.elim hrel
        | ordinary state memory =>
            obtain ⟨hrow, _, _, hlast, haccepted, hscore, hdelta, hbacklog, hstatus,
              hfailure, _, _⟩ := hrel
            refine ⟨activation, state, memory, ?_, hlast, haccepted, hscore, hdelta,
              hbacklog, hstatus, hfailure⟩
            rw [hrow]

/-- Complete exhausted-boundary correspondence, including pending first
activation at `T + 1`. The accepted no-crossing theorem produces the force
complement here. A follower without a pending save can remain bootstrap;
all physical records are strictly before the terminal activation endpoint. -/
theorem combinedBoundaryHandoff_exhausted_related
    (source : SourceInput p) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (rate : RateInput p) (C_star C_h : ℝ) (b : ReferenceInitializationRun.Boundary p)
    (h : b.completed < n_boot p)
    (actual : ActualInitializationRun.BlockCarry p rate (ReferenceInitializationRun.nextBlock b h))
    (past : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hr : BlockStartRelated source rewards C_star C_h rate
      (ReferenceInitializationRun.nextBlock b h) actual b past)
    (hdown : ∀ i, ¬ InitializationFailureProvenance.generatedBlockDown
      (referenceInput source rewards C_star C_h rate) b h i)
    (hclean : ∀ (i : Fin (p.m - 1))
      (hi : refFollower i ∈ (ReferenceInitializationRun.physical
        (referenceInput source rewards C_star C_h rate) b h).uninformed),
      BootstrapAllCandidateController.cleanPrefix
        (ReferenceInitializationRun.physical (referenceInput source rewards C_star C_h rate) b h)
        source.1.2 ⟨refFollower i, hi⟩
        (ActualInitializationPhysicalStep.selectedRowIndex p source) p.T)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (hexhausted : (ActualInitializationRun.combinedBoundaryHandoff p rate
      (ReferenceInitializationRun.nextBlock b h) source rewards actual.C_star actual.C_h
      (ActualInitializationRun.foldBlock p rate (ReferenceInitializationRun.nextBlock b h)
        source rewards actual)).disposition = .exhausted live) :
    let x := referenceInput source rewards C_star C_h rate
    let block := ReferenceInitializationRun.nextBlock b h
    let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
    let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      actual.C_star actual.C_h folded
    let finished := ReferenceInitializationRun.finishBlock x b h
    block.val + 1 = n_boot p ∧
      ReferenceInitializationRun.crosses x b h = false ∧
      finished.crossing = none ∧
      folded.phase.monitorState.counters = finished.counters ∧
      (∀ i, ReferenceInitializationRun.forced x b h i = false) ∧
      (∀ i, finished.forcedFailure i = false) ∧
      past_related (past ++ folded.records) finished ∧
      (∀ i, follower_start_related x source rate rfl finished i
        (ActualInitializationRun.followerCarryOfBoundaryOutput rate (handoff.followers i))) ∧
      BootstrapObservedFollower.blockStop p block = p.T ∧
      (ReferenceInitializationRun.boundaryActivation b).val = p.T + 1 ∧
      (∀ record ∈ folded.records, record.time.val < p.T) ∧
      (∀ i, match handoff.followers i with
        | .continueBootstrap _ _ activation => activation.val = p.T + 1
        | .firstDeclaration _ activation _ _ => activation.val = p.T + 1
        | .preserveDeclared _ _ _ => True) := by
  let x := referenceInput source rewards C_star C_h rate
  let block := ReferenceInitializationRun.nextBlock b h
  let folded := ActualInitializationRun.foldBlock p rate block source rewards actual
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    actual.C_star actual.C_h folded
  let finished := ReferenceInitializationRun.finishBlock x b h
  obtain ⟨hlast, _, hcross, _, hstop, hrecords, _⟩ :=
    exhausted_reference_no_crossing source rewards rate C_star C_h b h actual past hr hdown
      live hexhausted
  change ReferenceInitializationRun.crosses x b h = false at hcross
  have hforce (i : ActiveRoundActions.Follower p.m) :
      ReferenceInitializationRun.forced x b h i = false := by
    simp only [ReferenceInitializationRun.forced, hcross, Bool.false_and]
  refine ⟨hlast, hcross, ?_, ?_, hforce, ?_,
    foldBlock_past_related source rewards rate C_star C_h b h actual past hr hdown,
    ?_, hstop, ?_, hrecords, ?_⟩
  · change (if ReferenceInitializationRun.crosses x b h then some block else none) = none
    rw [hcross]
    rfl
  · exact foldBlock_updatedCounters_eq source rewards rate C_star C_h b h actual past hr hdown
  · intro i
    change (b.forcedFailure i || ReferenceInitializationRun.forced x b h i) = false
    rw [hr.2.2.1 i, hforce i]
    rfl
  · intro i
    exact boundary_follower_start_related source rewards rate C_star C_h b h
      actual past hr hdown hforce hclean i
  · change ReferenceInitializationRun.elapsed p (b.completed + 1) + 1 = p.T + 1
    have helapsed : ReferenceInitializationRun.elapsed p (b.completed + 1) =
        BootstrapObservedFollower.blockStop p block := by
      simp only [ReferenceInitializationRun.elapsed, BootstrapObservedFollower.blockStop,
        block, ReferenceInitializationRun.nextBlock]
    rw [helapsed, hstop]
  · intro i
    change (match ActualInitializationRun.boundaryOutputFromFollower p rate block
      (folded.followers i) with
      | .continueBootstrap _ _ activation => activation.val = p.T + 1
      | .firstDeclaration _ activation _ _ => activation.val = p.T + 1
      | .preserveDeclared _ _ _ => True)
    cases hf : folded.followers i with
    | bootstrap state =>
        exact ActualInitializationRun.bootstrapBoundaryOutput_finalActivation state hlast
    | declared row activation configuration => trivial

end Bandits.Support.ActualReferenceInitializationTerminalBoundary

end
