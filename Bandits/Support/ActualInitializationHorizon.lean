/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationRun

import Lean.Elab.Tactic.Omega

/-!
# Actual initialization through the first launch boundary

This module repeatedly executes the accepted actual clipped-block fold and
its combined boundary handoff, starting from the source initialization state.
The finite records are concatenated in chronological order.  It stops at the
actual launch boundary or after all physical rounds through `T`.

The source algorithm is `sources/zip4/manuscript/07_public_setup.tex:63-113,
123-164` and the local physical order is
`sources/zip4/manuscript/06_interruptions.tex:235-296`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActiveFollowerDownAcceptance

namespace Bandits.Support.ActualInitializationHorizon

abbrev Parameters := ConstructorDimensions.Parameters

/-- A zero-based finite sequence of natural round numbers. -/
def consecutiveNat (start count : ℕ) : List ℕ :=
  match count with
  | 0 => []
  | n + 1 => start :: consecutiveNat (start + 1) n

theorem consecutiveNat_length (start count : ℕ) :
    (consecutiveNat start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [consecutiveNat, ih]

theorem consecutiveNat_append (start left right : ℕ) :
    consecutiveNat start (left + right) =
      consecutiveNat start left ++ consecutiveNat (start + left) right := by
  induction left generalizing start with
  | zero => simp [consecutiveNat]
  | succ left ih =>
      simp only [Nat.succ_add, consecutiveNat]
      rw [ih (start + 1)]
      congr 1
      simp [Nat.add_assoc, Nat.add_comm left 1]

theorem consecutiveNat_mem_iff (start count value : ℕ) :
    value ∈ consecutiveNat start count ↔ start ≤ value ∧ value < start + count := by
  induction count generalizing start value with
  | zero => simp [consecutiveNat]
  | succ count ih =>
      simp only [consecutiveNat, List.mem_cons, ih]
      omega

/-- The accepted within-block calendar list has the literal absolute round
numbers in its values. -/
theorem blockTimes_values (p : Parameters) (block : Fin (n_boot p))
    (cursor fuel : ℕ)
    (hlength : cursor + fuel = BootstrapObservedFollower.blockLength p block) :
    (ActualInitializationRun.blockTimes p block cursor fuel hlength).map Fin.val =
      consecutiveNat (BootstrapObservedFollower.blockStart p block + cursor) fuel := by
  induction fuel generalizing cursor with
  | zero => simp [ActualInitializationRun.blockTimes, consecutiveNat]
  | succ fuel ih =>
      simp only [ActualInitializationRun.blockTimes, List.map_cons, consecutiveNat]
      have htail :
          (ActualInitializationRun.blockTimes p block (cursor + 1) fuel (by omega)).map
              Fin.val = consecutiveNat
                (BootstrapObservedFollower.blockStart p block + (cursor + 1)) fuel :=
        ih (cursor + 1) (by omega)
      rw [htail]
      simp [ActualInitializationRun.blockTime, Nat.add_assoc]

/-- The actual records of a full accepted block enumerate that entire clipped
calendar interval exactly once and in increasing order. -/
theorem blockFold_time_values {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0) :
    (ActualInitializationRun.PhysicalRoundRecord.times folded.records).map Fin.val =
      consecutiveNat (BootstrapObservedFollower.blockStart p block)
        (BootstrapObservedFollower.blockLength p block) := by
  have hcount : folded.records.length = BootstrapObservedFollower.blockLength p block := by
    have h := folded.record_count
    rw [folded.consumed_eq_blockLength] at h
    omega
  have hbudget : 0 + folded.records.length =
      BootstrapObservedFollower.blockLength p block := by omega
  calc
    (ActualInitializationRun.PhysicalRoundRecord.times folded.records).map Fin.val =
        (ActualInitializationRun.blockTimes p block 0 folded.records.length hbudget).map
          Fin.val := congrArg (fun times => times.map Fin.val) folded.chronological
    _ = consecutiveNat (BootstrapObservedFollower.blockStart p block) folded.records.length :=
      blockTimes_values p block 0 folded.records.length hbudget
    _ = consecutiveNat (BootstrapObservedFollower.blockStart p block)
        (BootstrapObservedFollower.blockLength p block) := by rw [hcount]

/-- Every follower boundary entry in a completed block is the existing
successful boundary operation on that fold's actual final follower state. -/
theorem combinedBoundaryHandoff_follower_step {p : Parameters} {rate : RateInput p}
    {block : Fin (n_boot p)} {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0) (i : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.boundaryFollowers rate block folded.followers i =
      .ok ((ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        C_star C_h folded).followers i) := by
  have houtputs :
      (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        C_star C_h folded).followers i =
        ActualInitializationRun.blockBoundaryFollowers p rate block source rewards folded i := by
    dsimp [ActualInitializationRun.combinedBoundaryHandoff, id]
  rw [houtputs]
  exact ActualInitializationRun.blockBoundaryFollowers_step p rate block source rewards folded i

/-- An actual handoff can continue only to the original successor block; its
coordinator, monitor, constants, and follower carries are exactly those
computed from this block's actual final fold. -/
theorem combinedBoundaryHandoff_continueNext_facts {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (next : Fin (n_boot p)) (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (h : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .continueNext next nextCarry) :
    next.val = block.val + 1 ∧
      nextCarry.C_star = C_star ∧ nextCarry.C_h = C_h ∧
      ∃ live : BootstrapCoordinatorLocalRound.PrelaunchBlock p,
        folded.phase = .prelaunch live ∧
        nextCarry.coordinator = live.data.coordinator ∧
        nextCarry.monitor = live.monitor ∧
        ∀ i, nextCarry.followers i =
          ActualInitializationRun.followerCarryAtBlockBoundary p rate block
            (folded.followers i) := by
  cases folded with
  | mk consumed phase followers records invariant consumed_eq_blockLength record_count chronological =>
      cases phase with
      | launched launch =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
          cases h
      | prelaunch live =>
          by_cases hlast : block.val + 1 = n_boot p
          · dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
            rw [dite_eq_left hlast] at h
            cases h
          · have hnext : block.val + 1 < n_boot p := by omega
            dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
            rw [dite_eq_right hlast] at h
            let nextOf : ActualInitializationRun.BoundaryDisposition p rate block →
                Fin (n_boot p) := fun disposition =>
              match disposition with
              | .continueNext next _ => next
              | .launched _ _ => next
              | .exhausted _ => next
            let starOf : ActualInitializationRun.BoundaryDisposition p rate block → ℝ :=
              fun disposition => match disposition with
              | .continueNext _ carry => carry.C_star
              | .launched _ _ => nextCarry.C_star
              | .exhausted _ => nextCarry.C_star
            let chOf : ActualInitializationRun.BoundaryDisposition p rate block → ℝ :=
              fun disposition => match disposition with
              | .continueNext _ carry => carry.C_h
              | .launched _ _ => nextCarry.C_h
              | .exhausted _ => nextCarry.C_h
            let coordinatorOf :
                ActualInitializationRun.BoundaryDisposition p rate block →
                  BootstrapPhysicalBlock.State p := fun disposition =>
              match disposition with
              | .continueNext _ carry => carry.coordinator
              | .launched _ _ => nextCarry.coordinator
              | .exhausted _ => nextCarry.coordinator
            let monitorOf :
                ActualInitializationRun.BoundaryDisposition p rate block →
                  BootstrapCoordinatorLocalRound.UnlaunchedMonitor p :=
              fun disposition => match disposition with
              | .continueNext _ carry => carry.monitor
              | .launched _ _ => nextCarry.monitor
              | .exhausted _ => nextCarry.monitor
            let followersOf (i : Fin (p.m - 1)) :
                ActualInitializationRun.BoundaryDisposition p rate block →
                  ActualInitializationRun.FollowerCarry p rate := fun disposition =>
              match disposition with
              | .continueNext _ carry => carry.followers i
              | .launched _ _ => nextCarry.followers i
              | .exhausted _ => nextCarry.followers i
            have hnextVal : next.val = block.val + 1 := by
              have hproj := congrArg nextOf h
              simpa [nextOf, ActualInitializationRun.successorBlock] using
                congrArg Fin.val hproj.symm
            have hstar : nextCarry.C_star = C_star := by
              have hproj := congrArg starOf h
              simpa [starOf] using hproj.symm
            have hch : nextCarry.C_h = C_h := by
              have hproj := congrArg chOf h
              simpa [chOf] using hproj.symm
            have hcoordinator : nextCarry.coordinator = live.data.coordinator := by
              have hproj := congrArg coordinatorOf h
              simpa [coordinatorOf] using hproj.symm
            have hmonitor : nextCarry.monitor = live.monitor := by
              have hproj := congrArg monitorOf h
              simpa [monitorOf] using hproj.symm
            refine ⟨hnextVal, hstar, hch, live, rfl, hcoordinator, hmonitor, ?_⟩
            intro i
            have hproj := congrArg (followersOf i) h
            simpa [followersOf] using hproj.symm

/-- The next-block decrease is the actual remaining calendar-block measure
used by `runFrom`. -/
theorem combinedBoundaryHandoff_remaining_decreases {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (next : Fin (n_boot p)) (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (h : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .continueNext next nextCarry) :
    n_boot p - next.val < n_boot p - block.val := by
  have hnext := combinedBoundaryHandoff_continueNext_facts folded next nextCarry h
  omega

/-- After an actual bootstrap boundary, the follower either keeps the exact
updated bootstrap numerators or installs the pending first declaration in its
original row and ordinary initial configuration. -/
theorem followerCarryAtBlockBoundary_bootstrap_eq {p : Parameters}
    {rate : RateInput p} (block : Fin (n_boot p))
    (state : BootstrapObservedFollower.StartupState p block) :
    ActualInitializationRun.followerCarryAtBlockBoundary p rate block
        (.bootstrap state) =
      match BootstrapObservedFollower.pendingDeclaration state.blockCase with
      | none => .bootstrap (BootstrapObservedFollower.updatedNumerators p block state)
          (BootstrapObservedFollower.updatedNumerators_lower_bound p block state)
      | some row => .declared row (BootstrapObservedFollower.nextActivationRound p block)
          (.ordinary (ReferencePrelaunchFollower.initial p rate.eta)
            (ActiveFollowerLifecycle.initialMemory p)) := by
  cases hpending : BootstrapObservedFollower.pendingDeclaration state.blockCase <;>
    simp [ActualInitializationRun.followerCarryAtBlockBoundary,
      ActualInitializationRun.followerCarryOfBoundaryOutput,
      ActualInitializationRun.boundaryOutputFromFollower, hpending]

/-- An already declared follower's whole local configuration, row, and
activation are copied through the actual block boundary unchanged. -/
theorem followerCarryAtBlockBoundary_declared_eq {p : Parameters}
    {rate : RateInput p} (block : Fin (n_boot p)) (row : Fin (M p))
    (activation : ReferencePrelaunchFollower.Activation p)
    (configuration : DeclaredFollowerLocalRound.LocalConfiguration p rate) :
    ActualInitializationRun.followerCarryAtBlockBoundary p rate block
      (.declared row activation configuration) = .declared row activation configuration := rfl

/-- A pending first declaration is represented by the next block's original
activation boundary. -/
theorem nextActivationRound_eq_successor_start {p : Parameters}
    (block next : Fin (n_boot p)) (hnext : next.val = block.val + 1) :
    (BootstrapObservedFollower.nextActivationRound p block).val =
      BootstrapObservedFollower.blockStart p next + 1 := by
  have hnonlast : block.val + 1 < n_boot p := by omega
  simpa [BootstrapObservedFollower.blockStart, hnext] using
    BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block hnonlast

/-- Exhaustion is the actual no-launch handoff at the clipped final block. -/
theorem combinedBoundaryHandoff_exhausted_last {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (h : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .exhausted live) :
    block.val + 1 = n_boot p := by
  cases folded with
  | mk consumed phase followers records invariant consumed_eq_blockLength record_count chronological =>
      cases phase with
      | launched launch =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
          cases h
      | prelaunch current =>
          by_cases hlast : block.val + 1 = n_boot p
          · dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
            rw [dite_eq_left hlast] at h
            cases h
            exact hlast
          · dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
            rw [dite_eq_right hlast] at h
            cases h

/-- A launched handoff retains the block of its actual launched coordinator
continuation. -/
theorem combinedBoundaryHandoff_launched_block_eq {p : Parameters}
    {rate : RateInput p} {block : Fin (n_boot p)}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards
      C_star C_h 0)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (h : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      C_star C_h folded).disposition = .launched launch learnerSeed) :
    launch.data.block = block := by
  cases folded with
  | mk consumed phase followers records invariant consumed_eq_blockLength record_count chronological =>
      cases phase with
      | prelaunch live =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
          by_cases hlast : block.val + 1 = n_boot p
          · simp [hlast] at h
          · simp [hlast] at h
      | launched actual =>
          dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at h
          let blockOf : ActualInitializationRun.BoundaryDisposition p rate block →
              Fin (n_boot p) := fun disposition =>
            match disposition with
            | .continueNext _ _ => block
            | .launched active _ => active.data.block
            | .exhausted _ => block
          have hblocks := congrArg blockOf h
          have hactual : actual.data.block = block := by
            simpa [ActualInitializationRun.continuationAligned,
              ActualInitializationRun.continuationData] using invariant.1.1
          simpa [blockOf] using hblocks.symm.trans hactual

/-- One suffix of the deterministic actual initialization recursion.  Its
terminal fold and handoff are retained as produced; `records` is the sole
chronological concatenation of its actual physical round records. -/
structure ContinuedBlockExecution (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p) where
  block : Fin (n_boot p)
  carry : ActualInitializationRun.BlockCarry p rate block
  next : Fin (n_boot p)
  nextCarry : ActualInitializationRun.BlockCarry p rate next
  branch_eq :
    (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
      carry.C_star carry.C_h
      (ActualInitializationRun.foldBlock p rate block source rewards carry)).disposition =
        .continueNext next nextCarry

/-- One suffix of the deterministic actual initialization recursion.  Its
terminal fold and handoff are retained as produced; `records` is the sole
chronological concatenation of its actual physical round records. -/
structure RunSuffix (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (startBlock : Fin (n_boot p))
    (startCarry : ActualInitializationRun.BlockCarry p rate startBlock) where
  terminalBlock : Fin (n_boot p)
  terminalC_star : ℝ
  terminalC_h : ℝ
  terminalFold : ActualInitializationRun.BlockFoldOutput p rate terminalBlock source
    rewards terminalC_star terminalC_h 0
  terminalHandoff : ActualInitializationRun.CombinedBoundaryHandoff p rate
    terminalBlock source
  terminalHandoff_eq : terminalHandoff =
    ActualInitializationRun.combinedBoundaryHandoff p rate terminalBlock source rewards
      terminalC_star terminalC_h terminalFold
  terminalDisposition : ActualInitializationRun.BoundaryDisposition p rate terminalBlock
  terminalDisposition_eq : terminalDisposition = terminalHandoff.disposition
  terminal_stopped : match terminalDisposition with
    | .continueNext _ _ => False
    | .launched _ _ => True
    | .exhausted _ => True
  terminalC_star_eq : terminalC_star = startCarry.C_star
  terminalC_h_eq : terminalC_h = startCarry.C_h
  records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
  continuedBlocks : List (ContinuedBlockExecution p rate source rewards)
  continuedBlockIndex :
    (continuedBlocks.map fun execution => execution.block.val) =
      consecutiveNat startBlock.val continuedBlocks.length
  terminalBlock_index : terminalBlock.val = startBlock.val + continuedBlocks.length
  start_before_terminal : BootstrapObservedFollower.blockStart p startBlock ≤
    BootstrapObservedFollower.blockStop p terminalBlock
  chronological :
    (ActualInitializationRun.PhysicalRoundRecord.times records).map Fin.val =
      consecutiveNat (BootstrapObservedFollower.blockStart p startBlock)
        (BootstrapObservedFollower.blockStop p terminalBlock -
          BootstrapObservedFollower.blockStart p startBlock)

/-- Recurse only through the actual `continueNext` branch of the accepted
combined handoff.  The decreasing measure is the number of original blocks
from the current block through the clipped final block. -/
noncomputable def runFrom (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (block : Fin (n_boot p)) (carry : ActualInitializationRun.BlockCarry p rate block) :
    RunSuffix p rate source rewards block carry := by
  let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
  let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
    carry.C_star carry.C_h folded
  cases hdisposition : handoff.disposition with
  | continueNext next nextCarry =>
      have hfacts := combinedBoundaryHandoff_continueNext_facts folded next nextCarry
        (by simpa [handoff] using hdisposition)
      let tail := runFrom p rate source rewards next nextCarry
      have hcount : folded.records.length = BootstrapObservedFollower.blockLength p block := by
        have h := folded.record_count
        rw [folded.consumed_eq_blockLength] at h
        omega
      have hstop : BootstrapObservedFollower.blockStart p block +
          BootstrapObservedFollower.blockLength p block =
            BootstrapObservedFollower.blockStop p block :=
        ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hnextStart : BootstrapObservedFollower.blockStart p next =
          BootstrapObservedFollower.blockStop p block := by
        have hnextNonlast : block.val + 1 < n_boot p := by omega
        have hactivation :=
          BootstrapObservedFollower.nextActivationRound_nonlast_eq_nextStart p block
            hnextNonlast
        change BootstrapObservedFollower.blockStop p block + 1 =
          (block.val + 1) * B_boot p + 1 at hactivation
        have hstart : BootstrapObservedFollower.blockStart p next =
            (block.val + 1) * B_boot p := by
          simp [BootstrapObservedFollower.blockStart, hfacts.1]
        omega
      refine {
        terminalBlock := tail.terminalBlock
        terminalC_star := tail.terminalC_star
        terminalC_h := tail.terminalC_h
        terminalFold := tail.terminalFold
        terminalHandoff := tail.terminalHandoff
        terminalHandoff_eq := tail.terminalHandoff_eq
        terminalDisposition := tail.terminalDisposition
        terminalDisposition_eq := tail.terminalDisposition_eq
        terminal_stopped := tail.terminal_stopped
        terminalC_star_eq := ?_
        terminalC_h_eq := ?_
        records := folded.records ++ tail.records
        continuedBlocks := {
          block := block
          carry := carry
          next := next
          nextCarry := nextCarry
          branch_eq := by simpa [handoff, folded] using hdisposition } :: tail.continuedBlocks
        continuedBlockIndex := ?_
        terminalBlock_index := ?_
        start_before_terminal := ?_
        chronological := ?_ }
      · exact tail.terminalC_star_eq.trans hfacts.2.1
      · exact tail.terminalC_h_eq.trans hfacts.2.2.1
      · have htail := tail.continuedBlockIndex
        simp only [List.map_cons, List.length_cons, consecutiveNat]
        have htail' :
            (tail.continuedBlocks.map fun execution => execution.block.val) =
              consecutiveNat (block.val + 1) tail.continuedBlocks.length := by
          simpa [hfacts.1] using htail
        exact congrArg (List.cons block.val) htail'
      · have htail := tail.terminalBlock_index
        simp only [List.length_cons]
        omega
      · exact (le_of_lt (BootstrapObservedFollower.blockStart_lt_blockStop p block)).trans
          (by rw [← hnextStart]; exact tail.start_before_terminal)
      · have hfoldChron := blockFold_time_values folded
        have htailChron := tail.chronological
        have hterminal_ge : BootstrapObservedFollower.blockStart p next ≤
            BootstrapObservedFollower.blockStop p tail.terminalBlock :=
          tail.start_before_terminal
        have hlength : BootstrapObservedFollower.blockLength p block +
            (BootstrapObservedFollower.blockStop p tail.terminalBlock -
              BootstrapObservedFollower.blockStart p next) =
                BootstrapObservedFollower.blockStop p tail.terminalBlock -
                  BootstrapObservedFollower.blockStart p block := by
          omega
        calc
          (ActualInitializationRun.PhysicalRoundRecord.times
              (folded.records ++ tail.records)).map Fin.val =
              (ActualInitializationRun.PhysicalRoundRecord.times folded.records).map Fin.val ++
                (ActualInitializationRun.PhysicalRoundRecord.times tail.records).map Fin.val := by
                  simp [ActualInitializationRun.PhysicalRoundRecord.times,
                    List.map_append, List.map_map]
          _ = consecutiveNat (BootstrapObservedFollower.blockStart p block)
                (BootstrapObservedFollower.blockLength p block) ++
              consecutiveNat (BootstrapObservedFollower.blockStart p next)
                (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                  BootstrapObservedFollower.blockStart p next) := by
                rw [hfoldChron, htailChron]
          _ = consecutiveNat (BootstrapObservedFollower.blockStart p block)
                (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                  BootstrapObservedFollower.blockStart p block) := by
                calc
                  _ = consecutiveNat (BootstrapObservedFollower.blockStart p block)
                        (BootstrapObservedFollower.blockLength p block) ++
                      consecutiveNat
                        (BootstrapObservedFollower.blockStart p block +
                          BootstrapObservedFollower.blockLength p block)
                        (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                          BootstrapObservedFollower.blockStart p next) := by
                    rw [hnextStart, ← hstop]
                  _ = consecutiveNat (BootstrapObservedFollower.blockStart p block)
                        (BootstrapObservedFollower.blockLength p block +
                          (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                            BootstrapObservedFollower.blockStart p next)) :=
                    (consecutiveNat_append _ _ _).symm
                  _ = consecutiveNat (BootstrapObservedFollower.blockStart p block)
                        (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                          BootstrapObservedFollower.blockStart p block) := by
                    rw [hlength]
  | launched launch learnerSeed =>
      have hcount : folded.records.length = BootstrapObservedFollower.blockLength p block := by
        have h := folded.record_count
        rw [folded.consumed_eq_blockLength] at h
        omega
      have hstop : BootstrapObservedFollower.blockStart p block +
          BootstrapObservedFollower.blockLength p block =
            BootstrapObservedFollower.blockStop p block :=
        ActualInitializationRun.blockStart_add_length_eq_stop p block
      refine {
        terminalBlock := block
        terminalC_star := carry.C_star
        terminalC_h := carry.C_h
        terminalFold := folded
        terminalHandoff := handoff
        terminalHandoff_eq := rfl
        terminalDisposition := .launched launch learnerSeed
        terminalDisposition_eq := hdisposition.symm
        terminal_stopped := trivial
        terminalC_star_eq := rfl
        terminalC_h_eq := rfl
        records := folded.records
        continuedBlocks := []
        continuedBlockIndex := by simp [consecutiveNat]
        terminalBlock_index := by simp
        start_before_terminal := le_of_lt
          (BootstrapObservedFollower.blockStart_lt_blockStop p block)
        chronological := ?_ }
      have hend : BootstrapObservedFollower.blockStop p block -
          BootstrapObservedFollower.blockStart p block =
            BootstrapObservedFollower.blockLength p block := by
        omega
      rw [hend]
      exact blockFold_time_values folded
  | exhausted live =>
      have hcount : folded.records.length = BootstrapObservedFollower.blockLength p block := by
        have h := folded.record_count
        rw [folded.consumed_eq_blockLength] at h
        omega
      have hstop : BootstrapObservedFollower.blockStart p block +
          BootstrapObservedFollower.blockLength p block =
            BootstrapObservedFollower.blockStop p block :=
        ActualInitializationRun.blockStart_add_length_eq_stop p block
      refine {
        terminalBlock := block
        terminalC_star := carry.C_star
        terminalC_h := carry.C_h
        terminalFold := folded
        terminalHandoff := handoff
        terminalHandoff_eq := rfl
        terminalDisposition := .exhausted live
        terminalDisposition_eq := hdisposition.symm
        terminal_stopped := trivial
        terminalC_star_eq := rfl
        terminalC_h_eq := rfl
        records := folded.records
        continuedBlocks := []
        continuedBlockIndex := by simp [consecutiveNat]
        terminalBlock_index := by simp
        start_before_terminal := le_of_lt
          (BootstrapObservedFollower.blockStart_lt_blockStop p block)
        chronological := ?_ }
      have hend : BootstrapObservedFollower.blockStop p block -
          BootstrapObservedFollower.blockStart p block =
            BootstrapObservedFollower.blockLength p block := by
        omega
      rw [hend]
      exact blockFold_time_values folded
termination_by n_boot p - block.val
decreasing_by omega

/-- The actual source-initialized execution.  Inputs are exactly the original
published table/private coordinates and block/player-round scalar streams,
the actual rounded reward table, the original rate input, and the two shared
constants.  The recursion starts at `initialCarry`; no block history or state
sequence is accepted as an input. -/
noncomputable def sourceInitializedRun (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    RunSuffix p rate source rewards (ActualInitializationRun.firstBlock p)
      (ActualInitializationRun.initialCarry p rate C_star C_h) :=
  runFrom p rate source rewards (ActualInitializationRun.firstBlock p)
    (ActualInitializationRun.initialCarry p rate C_star C_h)

/-- The source-initialized record times are exactly the zero-based physical
rounds before its terminal boundary, with neither skipped nor repeated times. -/
theorem sourceInitializedRun_chronological (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (ActualInitializationRun.PhysicalRoundRecord.times
      (sourceInitializedRun p rate source rewards C_star C_h).records).map Fin.val =
        consecutiveNat 0
          (BootstrapObservedFollower.blockStop
            p (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock) := by
  have h := (sourceInitializedRun p rate source rewards C_star C_h).chronological
  simpa [sourceInitializedRun, ActualInitializationRun.firstBlock,
    BootstrapObservedFollower.blockStart] using h

/-- The computed continuation witnesses are exactly the original block
indices before the terminal block, in order. -/
theorem sourceInitializedRun_continued_block_indices (p : Parameters)
    (rate : RateInput p) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    ((sourceInitializedRun p rate source rewards C_star C_h).continuedBlocks.map
      fun execution => execution.block.val) =
        consecutiveNat 0
          (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock.val := by
  let result := sourceInitializedRun p rate source rewards C_star C_h
  have hindices := result.continuedBlockIndex
  have hterminal : result.terminalBlock.val = result.continuedBlocks.length := by
    simpa [ActualInitializationRun.firstBlock] using result.terminalBlock_index
  have hindices' :
      (result.continuedBlocks.map fun execution => execution.block.val) =
        consecutiveNat 0 result.continuedBlocks.length := by
    simpa [ActualInitializationRun.firstBlock] using hindices
  rw [hterminal.symm] at hindices'
  exact hindices'

/-- Every earlier block appears in the computed continuation chain and
consumed an actual `continueNext` handoff, so none of those blocks launched. -/
theorem sourceInitializedRun_prior_blocks_continue (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (execution : ContinuedBlockExecution p rate source rewards)
    (hmembership : execution ∈
      (sourceInitializedRun p rate source rewards C_star C_h).continuedBlocks)
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p) :
    execution.block.val <
        (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock.val ∧
      (ActualInitializationRun.combinedBoundaryHandoff p rate execution.block source rewards
        execution.carry.C_star execution.carry.C_h
        (ActualInitializationRun.foldBlock p rate execution.block source rewards execution.carry)
        ).disposition = .continueNext execution.next execution.nextCarry ∧
      (ActualInitializationRun.combinedBoundaryHandoff p rate execution.block source rewards
        execution.carry.C_star execution.carry.C_h
        (ActualInitializationRun.foldBlock p rate execution.block source rewards execution.carry)
        ).disposition ≠ .launched launch learnerSeed := by
  let result := sourceInitializedRun p rate source rewards C_star C_h
  have hterminal : result.terminalBlock.val = result.continuedBlocks.length := by
    simpa [ActualInitializationRun.firstBlock] using result.terminalBlock_index
  have hindices : (result.continuedBlocks.map fun item => item.block.val) =
      consecutiveNat 0 result.terminalBlock.val := by
    simpa [ActualInitializationRun.firstBlock, hterminal] using result.continuedBlockIndex
  have hmap : execution.block.val ∈
      result.continuedBlocks.map fun item => item.block.val :=
    List.mem_map.mpr ⟨execution, hmembership, rfl⟩
  rw [hindices] at hmap
  have hlt := (consecutiveNat_mem_iff 0 result.terminalBlock.val execution.block.val).mp hmap
  refine ⟨by simpa using hlt.2, execution.branch_eq, ?_⟩
  rw [execution.branch_eq]
  intro hlaunch
  cases hlaunch

/-- On exhaustion the actual handoff remains unlaunched at the final clipped
boundary, whose preceding physical records are all `T` rounds. -/
theorem sourceInitializedRun_exhaustion_reaches_horizon (p : Parameters)
    (rate : RateInput p) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (h : (sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
      .exhausted live) :
    BootstrapObservedFollower.blockStop p
        (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock = p.T ∧
      live.monitor.1.crossingBlock = none ∧ live.monitor.1.launchPosition = p.T := by
  let result := sourceInitializedRun p rate source rewards C_star C_h
  have hhandoff : result.terminalHandoff.disposition = .exhausted live :=
    result.terminalDisposition_eq.symm.trans h
  rw [result.terminalHandoff_eq] at hhandoff
  have hlast := combinedBoundaryHandoff_exhausted_last result.terminalFold live hhandoff
  exact ⟨BootstrapObservedFollower.finalBlock_endpoint_eq_T p result.terminalBlock hlast,
    live.monitor.property.1, live.monitor.property.2⟩

/-- A terminal launch carries the strict source threshold witness from the
actual coordinator handoff. -/
theorem launchedBlock_launchPosition_eq_blockStop {p : Parameters}
    (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p) :
    launch.monitor.launchPosition =
      BootstrapObservedFollower.blockStop p launch.data.block := by
  have hindex : BootstrapDimensions.roundBlockIndex p launch.triggerRound =
      launch.data.block := by
    apply Fin.ext
    exact ((BootstrapDimensions.mem_calendarBlock_iff_quotient p launch.data.block
      launch.triggerRound).1 launch.triggerInBlock).symm
  have hend := launch.triggerAtBlockEnd
  unfold BootstrapLaunchMonitor.calendarBlockEnd at hend
  rw [hindex] at hend
  calc
    launch.monitor.launchPosition =
        BootstrapDimensions.manuscriptRound p launch.triggerRound := launch.launchPosition
    _ = BootstrapObservedFollower.blockStop p launch.data.block := by
      simpa [BootstrapObservedFollower.blockStop] using hend

theorem sourceInitializedRun_terminal_launch_strict (p : Parameters)
    (rate : RateInput p) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (h : (sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
      .launched launch learnerSeed) :
    (sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.disposition =
        .launched launch learnerSeed ∧
      launch.monitor.crossingBlock =
        some (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock ∧
      BootstrapLaunchMonitor.monitorValue p launch.monitor.counters >
        4 * BootstrapStartupCostScale.Q launch.data.C_star launch.data.C_h p ∧
      launch.monitor.launchPosition = BootstrapObservedFollower.blockStop p
        (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock := by
  let result := sourceInitializedRun p rate source rewards C_star C_h
  have hsource := result.terminalDisposition_eq.symm.trans h
  have hhandoff := hsource
  rw [result.terminalHandoff_eq] at hhandoff
  have hblock := combinedBoundaryHandoff_launched_block_eq result.terminalFold launch
    learnerSeed hhandoff
  have hcross : launch.monitor.crossingBlock = some result.terminalBlock := by
    rw [← hblock]
    exact launch.crossing
  have hposition : launch.monitor.launchPosition =
      BootstrapObservedFollower.blockStop p result.terminalBlock := by
    rw [launchedBlock_launchPosition_eq_blockStop launch, hblock]
  exact ⟨hsource, hcross, launch.strictThreshold, hposition⟩

/-- A launch on the clipped final block starts at the distinct source round
`T+1`; the chronological record list itself still ends after physical round `T`. -/
theorem sourceInitializedRun_final_launch_round (p : Parameters)
    (rate : RateInput p) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlast : (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock.val + 1 =
      n_boot p)
    (h : (sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
      .launched launch learnerSeed) :
    (sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.disposition =
        .launched launch learnerSeed ∧ launch.monitor.launchPosition + 1 = p.T + 1 := by
  let result := sourceInitializedRun p rate source rewards C_star C_h
  have hhandoff : result.terminalHandoff.disposition = .launched launch learnerSeed :=
    result.terminalDisposition_eq.symm.trans h
  rw [result.terminalHandoff_eq] at hhandoff
  have hlaunchBlock := combinedBoundaryHandoff_launched_block_eq result.terminalFold launch
    learnerSeed hhandoff
  have hlastLaunch : launch.data.block.val + 1 = n_boot p := by rw [hlaunchBlock]; exact hlast
  exact ⟨result.terminalDisposition_eq.symm.trans h,
    ActualInitializationRun.launchedAtFinalBlock_sourceRound p launch hlastLaunch⟩

/-- Both action and rounded-feedback projections contain one entry for each
actual physical record, hence exactly the rounds through the terminal boundary. -/
theorem sourceInitializedRun_history_lengths (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (ActualInitializationRun.PhysicalRoundRecord.actions
        (sourceInitializedRun p rate source rewards C_star C_h).records).length =
      BootstrapObservedFollower.blockStop p
        (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock ∧
    (ActualInitializationRun.PhysicalRoundRecord.feedback
        (sourceInitializedRun p rate source rewards C_star C_h).records).length =
      BootstrapObservedFollower.blockStop p
        (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock := by
  have hchron := sourceInitializedRun_chronological p rate source rewards C_star C_h
  have hlen := congrArg List.length hchron
  simp only [List.length_map, consecutiveNat_length] at hlen
  have hrecords : (sourceInitializedRun p rate source rewards C_star C_h).records.length =
      BootstrapObservedFollower.blockStop p
        (sourceInitializedRun p rate source rewards C_star C_h).terminalBlock := by
    simpa [ActualInitializationRun.PhysicalRoundRecord.times] using hlen
  constructor
  · simpa only [ActualInitializationRun.PhysicalRoundRecord.actions,
      List.length_map] using hrecords
  · simpa only [ActualInitializationRun.PhysicalRoundRecord.feedback,
      List.length_map] using hrecords

/-- Horizon exhaustion preserves the distinct no-crossing sentinel and has
both actual physical histories of full length `T`. -/
theorem sourceInitializedRun_exhaustion_history_lengths (p : Parameters)
    (rate : RateInput p) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
    (h : (sourceInitializedRun p rate source rewards C_star C_h).terminalDisposition =
      .exhausted live) :
    (ActualInitializationRun.PhysicalRoundRecord.actions
      (sourceInitializedRun p rate source rewards C_star C_h).records).length = p.T ∧
    (ActualInitializationRun.PhysicalRoundRecord.feedback
      (sourceInitializedRun p rate source rewards C_star C_h).records).length = p.T ∧
    (sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.disposition =
      .exhausted live ∧ live.monitor.1.crossingBlock = none ∧
        live.monitor.1.launchPosition = p.T := by
  let result := sourceInitializedRun p rate source rewards C_star C_h
  have hterminal := result.terminalDisposition_eq.symm.trans h
  have hh := hterminal
  rw [result.terminalHandoff_eq] at hh
  have hlast := combinedBoundaryHandoff_exhausted_last result.terminalFold live hh
  have hstop := BootstrapObservedFollower.finalBlock_endpoint_eq_T p result.terminalBlock hlast
  have hlength := sourceInitializedRun_history_lengths p rate source rewards C_star C_h
  rw [hstop] at hlength
  exact ⟨hlength.1, hlength.2, hterminal, live.monitor.property.1, live.monitor.property.2⟩

/-- Each record in the source-initialized output retains a successful actual
simultaneous physical step at its literal time, coordinator state, follower
states, original source, and rounded reward table. -/
theorem physicalRoundRecord_actual {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    ActualInitializationPhysicalStep.step rate record.block record.time
        record.coordinatorBefore record.followersBefore source rewards = .ok record.result ∧
      record.result.prepared.source = source ∧ record.result.prepared.rewards = rewards ∧
      record.result.actions = ActualInitializationPhysicalStep.actionProfile
        record.result.prepared ∧
      record.result.feedback = ActualInitializationPhysicalStep.physicalFeedback
        record.result.prepared := by
  have hready := (ActualInitializationPhysicalStep.step_succeeds_iff_ready rate
    record.block record.time record.coordinatorBefore record.followersBefore source rewards).mp
      ⟨record.result, record.executed⟩
  obtain ⟨prepared, hprepare⟩ :=
    (ActualInitializationPhysicalStep.prepare_eq_ok_iff_ready rate record.block record.time
      record.coordinatorBefore record.followersBefore source rewards).mpr hready
  have hstep : ActualInitializationPhysicalStep.observePrepared prepared = .ok record.result := by
    simpa [ActualInitializationPhysicalStep.step, hprepare] using record.executed
  have hresult : record.result.prepared = prepared := by
    have hround : record.result =
        ⟨prepared, (ActualInitializationPhysicalStep.observeFollowers prepared).val,
          (ActualInitializationPhysicalStep.observeFollowers prepared).property⟩ := by
      simpa [ActualInitializationPhysicalStep.observePrepared] using hstep.symm
    rw [hround]
  have hprepareInputs : prepared.source = source ∧ prepared.rewards = rewards := by
    have h := hprepare
    simp [ActualInitializationPhysicalStep.prepare, hready] at h
    cases h
    exact ⟨rfl, rfl⟩
  refine ⟨record.executed, ?_, ?_, rfl, rfl⟩
  · rw [hresult]
    exact hprepareInputs.1
  · rw [hresult]
    exact hprepareInputs.2

/-- The source-initialized output preserves its initial shared constants at
the actual terminal fold. -/
theorem sourceInitializedRun_shared_constants (p : Parameters) (rate : RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    (sourceInitializedRun p rate source rewards C_star C_h).terminalC_star = C_star ∧
      (sourceInitializedRun p rate source rewards C_star C_h).terminalC_h = C_h := by
  exact ⟨(sourceInitializedRun p rate source rewards C_star C_h).terminalC_star_eq,
    (sourceInitializedRun p rate source rewards C_star C_h).terminalC_h_eq⟩

end Bandits.Support.ActualInitializationHorizon

end
