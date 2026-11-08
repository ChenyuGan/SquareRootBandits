/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualPostlaunchPhysicalStep

/-!
# Actual complete physical history

This module joins the source-initialized actual prefix to the deterministic
actual mixed postlaunch steps, retaining the original private source and
rounded reward table throughout.

Mathematical evidence: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`, and
`sources/zip4/manuscript/08_main_theorem.tex:67-75`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualPostlaunchPhysicalStep

namespace Bandits.Support.ActualCompletePhysicalHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActualPostlaunchPhysicalStep.RateInput
abbrev SourceInput (p : Parameters) := ActualPostlaunchPhysicalStep.SourceInput p
abbrev GridRewardTable (p : Parameters) := ActualPostlaunchPhysicalStep.GridRewardTable p

variable {p : Parameters} {rate : RateInput p}

/-- A retained actual postlaunch round and its exact mixed-step input/result. -/
structure MixedRoundRecord (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) where
  block : Fin (n_boot p)
  cursor : Nat
  input : ActualPostlaunchPhysicalStep.PhysicalInput
    (p := p) (rate := rate) block cursor
  input_source : input.source = source
  input_rewards : input.rewards = rewards
  result : ActualPostlaunchPhysicalStep.RoundResult input
  result_eq : result = ActualPostlaunchPhysicalStep.step input

def MixedRoundRecord.time {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    (record : MixedRoundRecord p rate source rewards) : Fin p.T := record.input.time

def MixedRoundRecord.actions {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    (record : MixedRoundRecord p rate source rewards) :
      FiniteBanditModel.ActionProfile p.m p.K :=
  ActualPostlaunchPhysicalStep.actionProfile record.result.prepared

def MixedRoundRecord.feedback {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    (record : MixedRoundRecord p rate source rewards) : Fin p.m → Fin (D p + 1) :=
  ActualPostlaunchPhysicalStep.physicalFeedback record.result.prepared

/-- Each successor trace starts at the preceding result's full `nextState`. -/
inductive MixedBlockTrace (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p)) :
    (cursor : Nat) → ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor → (stop : Nat) → Type
  | done {cursor : Nat}
      (state : ActualPostlaunchPhysicalStep.PostlaunchState
        (p := p) (rate := rate) block cursor) :
      MixedBlockTrace p rate source rewards block cursor state cursor
  | step {cursor stop : Nat}
      (state : ActualPostlaunchPhysicalStep.PostlaunchState
        (p := p) (rate := rate) block cursor)
      (input : ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) block cursor)
      (input_state : input.state = state)
      (input_source : input.source = source)
      (input_rewards : input.rewards = rewards)
      (result : ActualPostlaunchPhysicalStep.RoundResult input)
      (result_eq : result = ActualPostlaunchPhysicalStep.step input)
      (tail : MixedBlockTrace p rate source rewards block
        (cursor + 1) result.nextState stop)
      (cursor_lt_stop : cursor < stop) :
      MixedBlockTrace p rate source rewards block cursor state stop

def MixedBlockTrace.records {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)} {cursor : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor} {stop : Nat}
    (trace : MixedBlockTrace p rate source rewards block cursor state stop) :
      List (MixedRoundRecord p rate source rewards) :=
  match trace with
  | .done _ => []
  | .step _ input _ hsource hrewards result result_eq tail _ =>
      ⟨block, cursor, input, hsource, hrewards, result, result_eq⟩ :: tail.records

def MixedBlockTrace.finalState {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)} {cursor : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor} {stop : Nat}
    (trace : MixedBlockTrace p rate source rewards block cursor state stop) :
      ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block stop :=
  match trace with
  | .done state => state
  | .step _ _ _ _ _ _ _ tail _ => tail.finalState

/-- Fold the actual step through the end of this original clipped block. -/
noncomputable def foldMixedBlockAux (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p)) (cursor : Nat)
    (state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor)
    (hcursor : cursor ≤ BootstrapObservedFollower.blockLength p block) :
    MixedBlockTrace p rate source rewards block cursor state
      (BootstrapObservedFollower.blockLength p block) := by
  by_cases hdone : cursor = BootstrapObservedFollower.blockLength p block
  · subst cursor
    exact .done state
  · have hlt : cursor < BootstrapObservedFollower.blockLength p block := by omega
    let input : ActualPostlaunchPhysicalStep.PhysicalInput
        (p := p) (rate := rate) block cursor := ⟨source, rewards, state, hlt⟩
    let result := ActualPostlaunchPhysicalStep.step input
    have hnext : cursor + 1 ≤ BootstrapObservedFollower.blockLength p block := by omega
    exact .step state input rfl rfl rfl result rfl
      (foldMixedBlockAux p rate source rewards block (cursor + 1) result.nextState hnext) hlt
termination_by BootstrapObservedFollower.blockLength p block - cursor
decreasing_by omega

noncomputable def foldMixedBlock (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block 0) :
    MixedBlockTrace p rate source rewards block 0 state
      (BootstrapObservedFollower.blockLength p block) :=
  foldMixedBlockAux p rate source rewards block 0 state (Nat.zero_le _)

/-- Fold from an already constructed cursor-zero input without rebuilding it.
This is used for the launch adapter's exact first physical input. -/
noncomputable def foldMixedBlockFromInput (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block 0)
    (input_source : input.source = source) (input_rewards : input.rewards = rewards) :
    MixedBlockTrace p rate source rewards block 0 input.state
      (BootstrapObservedFollower.blockLength p block) := by
  let result := ActualPostlaunchPhysicalStep.step input
  have hnext : 0 + 1 ≤ BootstrapObservedFollower.blockLength p block := by
    have hpositive := input.cursor_lt
    omega
  exact .step input.state input rfl input_source input_rewards result rfl
    (foldMixedBlockAux p rate source rewards block (0 + 1) result.nextState hnext)
    input.cursor_lt

def MixedBlockTrace.times {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)} {cursor : Nat}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor} {stop : Nat}
    (trace : MixedBlockTrace p rate source rewards block cursor state stop) :
      List (Fin p.T) := trace.records.map MixedRoundRecord.time

theorem MixedBlockTrace.times_values (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p)) (cursor stop : Nat)
    (state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block cursor)
    (trace : MixedBlockTrace p rate source rewards block cursor state stop) :
    trace.times.map Fin.val = ActualInitializationHorizon.consecutiveNat
      (BootstrapObservedFollower.blockStart p block + cursor) (stop - cursor) := by
  induction trace with
  | done state =>
      simp [MixedBlockTrace.times, MixedBlockTrace.records,
        ActualInitializationHorizon.consecutiveNat]
  | @step cursor stop state input hstate hsource hrewards result result_eq tail hlt ih =>
      have htime : input.time.val = BootstrapObservedFollower.blockStart p block + cursor := by
        simp [ActualPostlaunchPhysicalStep.PhysicalInput.time,
          ActualInitializationRun.blockTime]
      have hcount : stop - cursor = (stop - (cursor + 1)) + 1 := by omega
      have hstart : BootstrapObservedFollower.blockStart p block + (cursor + 1) =
          BootstrapObservedFollower.blockStart p block + cursor + 1 := by omega
      simp only [MixedBlockTrace.times, MixedBlockTrace.records, List.map_cons,
        List.map_map, MixedRoundRecord.time]
      rw [htime, hcount, ActualInitializationHorizon.consecutiveNat]
      simpa [hstart, MixedBlockTrace.times] using ih

/-- All actual follower outputs at the completed mixed block boundary. -/
structure PostlaunchBoundaryRecord (p : Parameters) (rate : RateInput p) where
  block : Fin (n_boot p)
  state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate)
    block (BootstrapObservedFollower.blockLength p block)
  outputs : Fin (p.m - 1) → ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate
  outputs_eq : ∀ i, outputs i = ActualPostlaunchPhysicalStep.boundaryOutput state i
  accepted : ∀ i,
    ActualInitializationPhysicalStep.boundaryFollower rate block (state.followers i) =
      .ok (outputs i)

/-- The exact actual mixed-step adapter at a nonfinal postlaunch block
boundary, including its complete successor state. -/
structure PostlaunchCrossBoundaryRecord (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) where
  block : Fin (n_boot p)
  state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate)
    block (BootstrapObservedFollower.blockLength p block)
  hasNext : block.val + 1 < n_boot p
  next : Fin (n_boot p)
  next_eq : next = ActualInitializationRun.successorBlock p block hasNext
  successorState : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate)
    next 0
  crossSuccessorBoundary_eq : successorState =
    ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source state

def postlaunchCrossBoundaryRecord {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block 0}
    (trace : MixedBlockTrace p rate source rewards block 0 state
      (BootstrapObservedFollower.blockLength p block))
    (hasNext : block.val + 1 < n_boot p) (next : Fin (n_boot p))
    (next_eq : next = ActualInitializationRun.successorBlock p block hasNext) :
    PostlaunchCrossBoundaryRecord p rate source := by
  let terminal := trace.finalState
  exact ⟨block, terminal, hasNext, next, next_eq,
    ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source terminal, rfl⟩

def postlaunchBoundaryRecord {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)} {state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block 0}
    (trace : MixedBlockTrace p rate source rewards block 0 state
      (BootstrapObservedFollower.blockLength p block)) : PostlaunchBoundaryRecord p rate := by
  let terminal : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block (BootstrapObservedFollower.blockLength p block) :=
    trace.finalState
  exact ⟨block, terminal, ActualPostlaunchPhysicalStep.boundaryOutput terminal,
    fun _ => rfl, ActualPostlaunchPhysicalStep.boundaryOutput_accepted terminal⟩

/-- A suffix is indexed by its exact current block and cursor-zero state. A
successor block begins from the existing follower-only cross-boundary adapter;
the final clipped block retains its actual boundary outputs without a successor.
-/
inductive PostlaunchSuffix (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) :
    (block : Fin (n_boot p)) →
    ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0 → Type
  | final {block : Fin (n_boot p)}
      {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
      (trace : MixedBlockTrace p rate source rewards block 0 state
        (BootstrapObservedFollower.blockLength p block))
      (last : block.val + 1 = n_boot p) :
      PostlaunchSuffix p rate source rewards block state
  | successor {block : Fin (n_boot p)}
      {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
      (trace : MixedBlockTrace p rate source rewards block 0 state
        (BootstrapObservedFollower.blockLength p block))
      (hasNext : block.val + 1 < n_boot p)
      (next : Fin (n_boot p))
      (next_eq : next = ActualInitializationRun.successorBlock p block hasNext)
      (tail : PostlaunchSuffix p rate source rewards next
        (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source
          trace.finalState)) :
      PostlaunchSuffix p rate source rewards block state

private theorem successorBlock_measure_decreases (p : Parameters)
    (block : Fin (n_boot p)) (hnext : block.val + 1 < n_boot p) :
    n_boot p - (ActualInitializationRun.successorBlock p block hnext).val <
      n_boot p - block.val := by
  have hval : (ActualInitializationRun.successorBlock p block hnext).val = block.val + 1 := rfl
  rw [hval]
  omega

noncomputable def runPostlaunchSuffixFromTrace (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block 0)
    (trace : MixedBlockTrace p rate source rewards block 0 state
      (BootstrapObservedFollower.blockLength p block)) :
    PostlaunchSuffix p rate source rewards block state := by
  by_cases hlast : block.val + 1 = n_boot p
  · exact .final trace hlast
  · have hnext : block.val + 1 < n_boot p := by omega
    let next := ActualInitializationRun.successorBlock p block hnext
    exact .successor trace hnext next rfl
      (runPostlaunchSuffixFromTrace p rate source rewards next
        (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext rfl source
          trace.finalState)
        (foldMixedBlock p rate source rewards next
          (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hnext rfl source
            trace.finalState)))
termination_by n_boot p - block.val
decreasing_by
  exact successorBlock_measure_decreases p block hnext

noncomputable def runPostlaunchSuffix (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState
      (p := p) (rate := rate) block 0) :
    PostlaunchSuffix p rate source rewards block state :=
  runPostlaunchSuffixFromTrace p rate source rewards block state
    (foldMixedBlock p rate source rewards block state)

def PostlaunchSuffix.records {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state) :
      List (MixedRoundRecord p rate source rewards) :=
  match suffix with
  | .final trace _ => trace.records
  | .successor trace _ _ _ tail => trace.records ++ tail.records

def PostlaunchSuffix.terminalBlock {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state) : Fin (n_boot p) :=
  match suffix with
  | .final _ _ => block
  | .successor _ _ _ _ tail => tail.terminalBlock

def PostlaunchSuffix.boundaries {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state) :
      List (PostlaunchBoundaryRecord p rate) :=
  match suffix with
  | .final trace _ => [postlaunchBoundaryRecord trace]
  | .successor trace _ _ _ tail => postlaunchBoundaryRecord trace :: tail.boundaries

/-- Each completed nonfinal mixed block exposes the actual follower-only
adapter equation that starts its successor. -/
def PostlaunchSuffix.crossBoundaryRecords {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state) :
    List (PostlaunchCrossBoundaryRecord p rate source) :=
  match suffix with
  | .final _ _ => []
  | .successor trace hasNext next next_eq tail =>
      postlaunchCrossBoundaryRecord trace hasNext next next_eq :: tail.crossBoundaryRecords

theorem PostlaunchSuffix.terminalBlock_last (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0) :
    (suffix : PostlaunchSuffix p rate source rewards block state) →
      suffix.terminalBlock.val + 1 = n_boot p
  | .final _trace last => last
  | .successor trace hasNext next next_eq tail =>
      PostlaunchSuffix.terminalBlock_last p rate source rewards next
        (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source
          trace.finalState) tail

theorem PostlaunchSuffix.boundaries_accepted (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0) :
    (suffix : PostlaunchSuffix p rate source rewards block state) →
    ∀ boundary ∈ suffix.boundaries, ∀ i,
      ActualInitializationPhysicalStep.boundaryFollower rate boundary.block
        (boundary.state.followers i) = .ok (boundary.outputs i)
  | .final trace last => by
      intro boundary hboundary i
      simp [PostlaunchSuffix.boundaries] at hboundary
      subst boundary
      exact (postlaunchBoundaryRecord trace).accepted i
  | .successor trace hasNext next next_eq tail => by
      intro boundary hboundary i
      simp only [PostlaunchSuffix.boundaries, List.mem_cons] at hboundary
      rcases hboundary with hboundary | hboundary
      · subst boundary
        exact (postlaunchBoundaryRecord trace).accepted i
      · exact PostlaunchSuffix.boundaries_accepted p rate source rewards next
          (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source
            trace.finalState) tail boundary hboundary i

theorem PostlaunchSuffix.times_values (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0) :
    (suffix : PostlaunchSuffix p rate source rewards block state) →
    (suffix.records.map MixedRoundRecord.time).map Fin.val =
      ActualInitializationHorizon.consecutiveNat
        (BootstrapObservedFollower.blockStart p block)
        (BootstrapObservedFollower.blockStop p suffix.terminalBlock -
          BootstrapObservedFollower.blockStart p block)
  | .final trace last => by
      have hstop := BootstrapObservedFollower.finalBlock_endpoint_eq_T p block last
      have hlength := ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hdiff : BootstrapObservedFollower.blockStop p block -
          BootstrapObservedFollower.blockStart p block =
            BootstrapObservedFollower.blockLength p block := by omega
      have htimes := MixedBlockTrace.times_values p rate source rewards block 0
        (BootstrapObservedFollower.blockLength p block) state trace
      simpa [PostlaunchSuffix.records, PostlaunchSuffix.terminalBlock,
        MixedBlockTrace.times, hdiff, Nat.zero_add] using htimes
  | .successor trace hasNext next next_eq tail => by
      have hnextVal : next.val = block.val + 1 := by
        simp [next_eq, ActualInitializationRun.successorBlock]
      have hnextStart : BootstrapObservedFollower.blockStart p next =
          BootstrapObservedFollower.blockStop p block := by
        have hactivation := ActualInitializationHorizon.nextActivationRound_eq_successor_start
          (p := p) block next hnextVal
        change BootstrapObservedFollower.blockStop p block + 1 =
          BootstrapObservedFollower.blockStart p next + 1 at hactivation
        omega
      have hlength := ActualInitializationRun.blockStart_add_length_eq_stop p block
      have hfold := MixedBlockTrace.times_values p rate source rewards block 0
        (BootstrapObservedFollower.blockLength p block) state trace
      have hterminal : BootstrapObservedFollower.blockStart p next ≤
          BootstrapObservedFollower.blockStop p tail.terminalBlock := by
        have hstart := BootstrapObservedFollower.blockStart_lt_blockStop p next
        have hstop : BootstrapObservedFollower.blockStop p next ≤ p.T := by
          simp [BootstrapObservedFollower.blockStop]
        have hfinal := BootstrapObservedFollower.finalBlock_endpoint_eq_T p tail.terminalBlock
          (PostlaunchSuffix.terminalBlock_last p rate source rewards next
            (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source
              trace.finalState) tail)
        omega
      have hcount : BootstrapObservedFollower.blockLength p block +
          (BootstrapObservedFollower.blockStop p tail.terminalBlock -
            BootstrapObservedFollower.blockStart p next) =
          BootstrapObservedFollower.blockStop p tail.terminalBlock -
            BootstrapObservedFollower.blockStart p block := by omega
      calc
        ((trace.records ++ tail.records).map MixedRoundRecord.time).map Fin.val =
            (trace.times.map Fin.val) ++ ((tail.records.map MixedRoundRecord.time).map Fin.val) := by
              simp [MixedBlockTrace.times, List.map_append, List.map_map, Function.comp_def]
        _ = ActualInitializationHorizon.consecutiveNat
              (BootstrapObservedFollower.blockStart p block)
              (BootstrapObservedFollower.blockLength p block) ++
            ActualInitializationHorizon.consecutiveNat
              (BootstrapObservedFollower.blockStart p next)
              (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                BootstrapObservedFollower.blockStart p next) := by
              rw [hfold, PostlaunchSuffix.times_values p rate source rewards next
                (ActualPostlaunchPhysicalStep.crossSuccessorBoundary hasNext next_eq source
                  trace.finalState) tail]
              simp
        _ = ActualInitializationHorizon.consecutiveNat
              (BootstrapObservedFollower.blockStart p block)
              (BootstrapObservedFollower.blockLength p block +
                (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                  BootstrapObservedFollower.blockStart p next)) := by
              rw [hnextStart, ← hlength]
              exact (ActualInitializationHorizon.consecutiveNat_append _ _ _).symm
        _ = ActualInitializationHorizon.consecutiveNat
              (BootstrapObservedFollower.blockStart p block)
              (BootstrapObservedFollower.blockStop p tail.terminalBlock -
                BootstrapObservedFollower.blockStart p block) := by rw [hcount]

theorem PostlaunchSuffix.record_count (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (block : Fin (n_boot p))
    (state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0)
    (suffix : PostlaunchSuffix p rate source rewards block state) :
    suffix.records.length = p.T - BootstrapObservedFollower.blockStart p block := by
  have hchron := suffix.times_values p rate source rewards block state
  have hlen := congrArg List.length hchron
  have hterminal := BootstrapObservedFollower.finalBlock_endpoint_eq_T p suffix.terminalBlock
    (suffix.terminalBlock_last p rate source rewards block state)
  simpa [List.length_map, ActualInitializationHorizon.consecutiveNat_length, hterminal] using hlen

/-- The complete construction has exactly the computed terminal cases. -/
inductive CompleteHistory (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) where
  | launchedBefore (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
      (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
      (launched : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalDisposition = .launched launch learnerSeed)
      (before : launch.monitor.launchPosition < p.T)
      (postlaunch : PostlaunchSuffix p rate source rewards
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
          rewards C_star C_h launch learnerSeed launched before)
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
          rewards C_star C_h launch learnerSeed launched before).state)
  | launchedAtHorizon (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
      (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
      (launched : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalDisposition = .launched launch learnerSeed)
      (atHorizon : launch.monitor.launchPosition = p.T)
  | exhausted (live : BootstrapCoordinatorLocalRound.PrelaunchBlock p)
      (exhausted : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
        C_star C_h).terminalDisposition = .exhausted live)

theorem sourceRun_not_continueNext (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (run : ActualInitializationHorizon.RunSuffix p rate source rewards
      (ActualInitializationRun.firstBlock p)
      (ActualInitializationRun.initialCarry p rate C_star C_h))
    (next : Fin (n_boot p))
    (nextCarry : ActualInitializationRun.BlockCarry p rate next)
    (h : run.terminalDisposition = .continueNext next nextCarry) : False := by
  cases run with
  | mk terminalBlock terminalC_star terminalC_h terminalFold terminalHandoff
      terminalHandoff_eq terminalDisposition terminalDisposition_eq terminal_stopped
      terminalC_star_eq terminalC_h_eq records continuedBlocks continuedBlockIndex
      terminalBlock_index start_before_terminal chronological =>
        cases terminalDisposition with
        | continueNext next' nextCarry' => exact terminal_stopped
        | launched launch learnerSeed => cases h
        | exhausted live => cases h

/-- Construct the deterministic actual history from only the original source,
reward table, rate, and shared constants. The initialization run computes its
initial carry internally. -/
noncomputable def sourceInitializedActualCompleteHistory (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) : CompleteHistory p rate source rewards C_star C_h := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  cases hterminal : run.terminalDisposition with
  | launched launch learnerSeed =>
      have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
        p rate source rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal)
      have hstop_le : BootstrapObservedFollower.blockStop p run.terminalBlock ≤ p.T := by
        simp [BootstrapObservedFollower.blockStop]
      have hposition_le : launch.monitor.launchPosition ≤ p.T := by
        rw [hstrict.2.2.2]
        exact hstop_le
      by_cases hbefore : launch.monitor.launchPosition < p.T
      · exact .launchedBefore launch learnerSeed (by simpa [run] using hterminal) hbefore
          (runPostlaunchSuffixFromTrace p rate source rewards
            (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
              rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal) hbefore)
            (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
              rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal) hbefore).state
            (foldMixedBlockFromInput p rate source rewards
              (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
                rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal) hbefore)
              (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
                rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal) hbefore)
              (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_source p rate source
                rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal) hbefore)
              (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_rewards p rate source
                rewards C_star C_h launch learnerSeed (by simpa [run] using hterminal) hbefore)))
      · have hat : launch.monitor.launchPosition = p.T := by omega
        exact .launchedAtHorizon launch learnerSeed (by simpa [run] using hterminal) hat
  | exhausted live => exact .exhausted live (by simpa [run] using hterminal)
  | continueNext next nextCarry =>
      exact False.elim (sourceRun_not_continueNext p rate source rewards C_star C_h
        run next nextCarry hterminal)

/-- Typed disjoint records for the source initialization and the actual mixed
postlaunch suffix. -/
inductive PhysicalHistoryRecord (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) where
  | initialization (record : ActualInitializationRun.PhysicalRoundRecord
      p rate source rewards)
  | postlaunch (record : MixedRoundRecord p rate source rewards)

def PhysicalHistoryRecord.time {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} :
    PhysicalHistoryRecord p rate source rewards → Fin p.T
  | .initialization record => record.time
  | .postlaunch record => record.time

def PhysicalHistoryRecord.actions {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} :
    PhysicalHistoryRecord p rate source rewards →
      FiniteBanditModel.ActionProfile p.m p.K
  | .initialization record => record.result.actions
  | .postlaunch record => record.actions

def PhysicalHistoryRecord.feedback {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} :
    PhysicalHistoryRecord p rate source rewards → Fin p.m → Fin (D p + 1)
  | .initialization record => record.result.feedback
  | .postlaunch record => record.feedback

def initializationRecords {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (_history : CompleteHistory p rate source rewards C_star C_h) :=
  (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records

def postlaunchRecords {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ} :
    CompleteHistory p rate source rewards C_star C_h →
      List (MixedRoundRecord p rate source rewards)
  | .launchedBefore _ _ _ _ suffix => suffix.records
  | .launchedAtHorizon _ _ _ _ => []
  | .exhausted _ _ => []

/-- The initialization prefix length is the launch round before the horizon;
final launch and exhaustion both retain all `T` ordinary physical rounds. -/
def CompleteHistory.prefixRoundCount {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ} :
    CompleteHistory p rate source rewards C_star C_h → Nat
  | .launchedBefore launch _ _ _ _ => launch.monitor.launchPosition
  | .launchedAtHorizon _ _ _ _ => p.T
  | .exhausted _ _ => p.T

/-- The actual H record list ends at its computed terminal block boundary. -/
theorem initializationRun_record_count (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.length =
      BootstrapObservedFollower.blockStop p
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalBlock := by
  have hchron := ActualInitializationHorizon.sourceInitializedRun_chronological
    p rate source rewards C_star C_h
  have hlength := congrArg List.length hchron
  simpa [ActualInitializationRun.PhysicalRoundRecord.times,
    ActualInitializationHorizon.consecutiveNat_length] using hlength

/-- The source initialization and actual mixed suffix have the exact split
counts: `s` prefix records and `T-s` suffix records in each terminal case. -/
theorem sourceInitializedActualCompleteHistory_component_counts (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h) :
    (initializationRecords history).length = CompleteHistory.prefixRoundCount history ∧
      (postlaunchRecords history).length = p.T - CompleteHistory.prefixRoundCount history := by
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
        p rate source rewards C_star C_h launch learnerSeed hlaunch
      have hprefix := initializationRun_record_count p rate source rewards C_star C_h
      have hstart : BootstrapObservedFollower.blockStart p
          (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
            rewards C_star C_h launch learnerSeed hlaunch hbefore) =
            launch.monitor.launchPosition := by
        have htime := ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_time_val
          p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore
        simpa [ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput,
          ActualPostlaunchPhysicalStep.PhysicalInput.time,
          ActualInitializationRun.blockTime] using htime
      have hsuffix := suffix.record_count p rate source rewards
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
          rewards C_star C_h launch learnerSeed hlaunch hbefore)
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
          rewards C_star C_h launch learnerSeed hlaunch hbefore).state
      constructor
      · simpa [initializationRecords, CompleteHistory.prefixRoundCount,
          ← hstrict.2.2.2] using hprefix
      · simpa [postlaunchRecords, CompleteHistory.prefixRoundCount, hstart] using hsuffix
  | launchedAtHorizon launch learnerSeed hlaunch hat =>
      have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
        p rate source rewards C_star C_h launch learnerSeed hlaunch
      have hprefix := initializationRun_record_count p rate source rewards C_star C_h
      constructor
      · simpa [initializationRecords, CompleteHistory.prefixRoundCount,
          ← hstrict.2.2.2, hat] using hprefix
      · simp [postlaunchRecords, CompleteHistory.prefixRoundCount]
  | exhausted live hexhausted =>
      have hexhaust := ActualInitializationHorizon.sourceInitializedRun_exhaustion_reaches_horizon
        p rate source rewards C_star C_h live hexhausted
      have hprefix := initializationRun_record_count p rate source rewards C_star C_h
      constructor
      · simpa [initializationRecords, CompleteHistory.prefixRoundCount,
          hexhaust.1] using hprefix
      · simp [postlaunchRecords, CompleteHistory.prefixRoundCount]

def physicalHistoryRecords {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h) :
      List (PhysicalHistoryRecord p rate source rewards) :=
  (initializationRecords history).map .initialization ++
    (postlaunchRecords history).map .postlaunch

def times {p : Parameters} {rate : RateInput p} {source : SourceInput p}
    {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h) :
      List (Fin p.T) := (physicalHistoryRecords history).map PhysicalHistoryRecord.time

def actionHistory {p : Parameters} {rate : RateInput p} {source : SourceInput p}
    {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h) :
      List (FiniteBanditModel.ActionProfile p.m p.K) :=
  (physicalHistoryRecords history).map PhysicalHistoryRecord.actions

def feedbackHistory {p : Parameters} {rate : RateInput p} {source : SourceInput p}
    {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h) :
      List (Fin p.m → Fin (D p + 1)) :=
  (physicalHistoryRecords history).map PhysicalHistoryRecord.feedback

def postlaunchBoundaryRecords {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ} :
    CompleteHistory p rate source rewards C_star C_h →
      List (PostlaunchBoundaryRecord p rate)
  | .launchedBefore _ _ _ _ suffix => suffix.boundaries
  | .launchedAtHorizon _ _ _ _ => []
  | .exhausted _ _ => []

/-- The exact terminal boundary outputs from H are retained in every case,
including final launch and exhaustion with their distinct dispositions. -/
def initializationTerminalBoundaryOutputs (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) :
    Fin (p.m - 1) → ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers

theorem initializationTerminalBoundaryOutputs_eq_handoff (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) :
    initializationTerminalBoundaryOutputs p rate source rewards C_star C_h =
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers := rfl

/-- The launch adapter's initial follower family is exactly its per-player
projection from H's actual terminal handoff. -/
theorem sourceInitializedLaunchSuccessorInput_followers (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) (launch : BootstrapCoordinatorLocalRound.LaunchedBlock p)
    (learnerSeed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hlaunch : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards
      C_star C_h).terminalDisposition = .launched launch learnerSeed)
    (hbefore : launch.monitor.launchPosition < p.T) :
    ∀ i, (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
      rewards C_star C_h launch learnerSeed hlaunch hbefore).state.followers i =
        ActualPostlaunchPhysicalStep.sourceInitializedLaunchedFollower p rate source rewards
          C_star C_h launch learnerSeed hlaunch hbefore i := by
  intro i
  rfl

theorem times_projection (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h) :
    times history =
      ActualInitializationRun.PhysicalRoundRecord.times
        (initializationRecords history) ++
      (postlaunchRecords history).map MixedRoundRecord.time := by
  simp [times, physicalHistoryRecords, PhysicalHistoryRecord.time,
    ActualInitializationRun.PhysicalRoundRecord.times, List.map_append,
    List.map_map, Function.comp_def]

theorem actionHistory_projection (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h) :
    actionHistory history =
      ActualInitializationRun.PhysicalRoundRecord.actions
        (initializationRecords history) ++
      (postlaunchRecords history).map MixedRoundRecord.actions := by
  simp [actionHistory, physicalHistoryRecords, PhysicalHistoryRecord.actions,
    ActualInitializationRun.PhysicalRoundRecord.actions, List.map_append,
    List.map_map, Function.comp_def]

theorem feedbackHistory_projection (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h) :
    feedbackHistory history =
      ActualInitializationRun.PhysicalRoundRecord.feedback
        (initializationRecords history) ++
      (postlaunchRecords history).map MixedRoundRecord.feedback := by
  simp [feedbackHistory, physicalHistoryRecords, PhysicalHistoryRecord.feedback,
    ActualInitializationRun.PhysicalRoundRecord.feedback, List.map_append,
    List.map_map, Function.comp_def]

/-- Every actual player's chosen arm at each retained round. -/
def playerArmHistory {p : Parameters} {rate : RateInput p} {source : SourceInput p}
    {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) : List (Fin p.K) :=
  (actionHistory history).map fun profile => profile player

/-- Every actual player's collision-filtered integer grid observation. -/
def playerGridFeedbackHistory {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) : List (Fin (D p + 1)) :=
  (feedbackHistory history).map fun feedback => feedback player

/-- The exact quantized reward entries `y / D` read from this player's actual
feedback history. -/
def playerQuantizedObservationHistory {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) : List ℝ :=
  (playerGridFeedbackHistory history player).map fun y => (y.val : ℝ) / (D p : ℝ)

/-- If a scalar reward projection is wanted, it is exactly the sum of the
actual per-round `y / D` entries above. -/
def totalObservedReward {p : Parameters} {rate : RateInput p}
    {source : SourceInput p} {rewards : GridRewardTable p} {C_star C_h : ℝ}
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) : ℝ :=
  (playerQuantizedObservationHistory history player).sum

theorem playerArmHistory_projection (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) :
    playerArmHistory history player =
      (ActualInitializationRun.PhysicalRoundRecord.actions
        (initializationRecords history)).map (fun profile => profile player) ++
      ((postlaunchRecords history).map MixedRoundRecord.actions).map
        (fun profile => profile player) := by
  rw [playerArmHistory, actionHistory_projection p rate source rewards C_star C_h history]
  simp [List.map_append, List.map_map, Function.comp_def]

theorem playerGridFeedbackHistory_projection (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) :
    playerGridFeedbackHistory history player =
      (ActualInitializationRun.PhysicalRoundRecord.feedback
        (initializationRecords history)).map (fun feedback => feedback player) ++
      ((postlaunchRecords history).map MixedRoundRecord.feedback).map
        (fun feedback => feedback player) := by
  rw [playerGridFeedbackHistory, feedbackHistory_projection p rate source rewards C_star C_h history]
  simp [List.map_append, List.map_map, Function.comp_def]

theorem playerQuantizedObservationHistory_projection (p : Parameters) (rate : RateInput p)
    (source : SourceInput p) (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (history : CompleteHistory p rate source rewards C_star C_h)
    (player : Fin p.m) :
    playerQuantizedObservationHistory history player =
      (ActualInitializationRun.PhysicalRoundRecord.feedback
        (initializationRecords history)).map
          (fun feedback => ((feedback player).val : ℝ) / (D p : ℝ)) ++
        ((postlaunchRecords history).map MixedRoundRecord.feedback).map
          (fun feedback => ((feedback player).val : ℝ) / (D p : ℝ)) := by
  rw [playerQuantizedObservationHistory, playerGridFeedbackHistory_projection]
  simp [List.map_append, List.map_map, Function.comp_def]

/-- Exact zero-based chronology through all `T` physical rounds. -/
theorem sourceInitializedActualCompleteHistory_times_values (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) :
    ((times (sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)).map
      Fin.val) = ActualInitializationHorizon.consecutiveNat 0 p.T := by
  let history := sourceInitializedActualCompleteHistory p rate source rewards C_star C_h
  change ((times history).map Fin.val) = ActualInitializationHorizon.consecutiveNat 0 p.T
  cases history with
  | launchedBefore launch learnerSeed hlaunch hbefore suffix =>
      have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
        p rate source rewards C_star C_h launch learnerSeed hlaunch
      let prefixTimes := ActualInitializationRun.PhysicalRoundRecord.times
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records
      have hprefixChron := ActualInitializationHorizon.sourceInitializedRun_chronological
        p rate source rewards C_star C_h
      have hprefix : prefixTimes.map Fin.val =
          ActualInitializationHorizon.consecutiveNat 0 launch.monitor.launchPosition := by
        simpa [prefixTimes, ← hstrict.2.2.2] using hprefixChron
      have hstart : BootstrapObservedFollower.blockStart p
          (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
            rewards C_star C_h launch learnerSeed hlaunch hbefore) =
            launch.monitor.launchPosition := by
        have htime := ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput_time_val
          p rate source rewards C_star C_h launch learnerSeed hlaunch hbefore
        simpa [ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput,
          ActualPostlaunchPhysicalStep.PhysicalInput.time,
          ActualInitializationRun.blockTime] using htime
      have hlast := suffix.terminalBlock_last p rate source rewards
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
          rewards C_star C_h launch learnerSeed hlaunch hbefore)
        (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
          rewards C_star C_h launch learnerSeed hlaunch hbefore).state
      have hfinal : BootstrapObservedFollower.blockStop p suffix.terminalBlock = p.T :=
        BootstrapObservedFollower.finalBlock_endpoint_eq_T p suffix.terminalBlock hlast
      let suffixTimes := suffix.records.map MixedRoundRecord.time
      have htail : suffixTimes.map Fin.val =
          ActualInitializationHorizon.consecutiveNat launch.monitor.launchPosition
            (p.T - launch.monitor.launchPosition) := by
        have htail' := suffix.times_values p rate source rewards
          (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorBlock p rate source
            rewards C_star C_h launch learnerSeed hlaunch hbefore)
          (ActualPostlaunchPhysicalStep.sourceInitializedLaunchSuccessorInput p rate source
            rewards C_star C_h launch learnerSeed hlaunch hbefore).state
        simpa [suffixTimes, hfinal, hstart] using htail'
      have hprojection := times_projection p rate source rewards C_star C_h
        (.launchedBefore launch learnerSeed hlaunch hbefore suffix)
      have hcombined : (times (.launchedBefore launch learnerSeed hlaunch hbefore suffix)).map Fin.val =
          prefixTimes.map Fin.val ++ suffixTimes.map Fin.val := by
        rw [hprojection]
        simp [prefixTimes, suffixTimes, initializationRecords, postlaunchRecords,
          ActualInitializationRun.PhysicalRoundRecord.times, List.map_append,
          List.map_map, Function.comp_def]
      rw [hcombined, hprefix, htail]
      have hsplit : launch.monitor.launchPosition +
          (p.T - launch.monitor.launchPosition) = p.T := by omega
      calc
        ActualInitializationHorizon.consecutiveNat 0 launch.monitor.launchPosition ++
            ActualInitializationHorizon.consecutiveNat launch.monitor.launchPosition
              (p.T - launch.monitor.launchPosition) =
            ActualInitializationHorizon.consecutiveNat 0
              (launch.monitor.launchPosition + (p.T - launch.monitor.launchPosition)) := by
                simpa [Nat.zero_add] using
                  (ActualInitializationHorizon.consecutiveNat_append 0
                    launch.monitor.launchPosition
                    (p.T - launch.monitor.launchPosition)).symm
        _ = ActualInitializationHorizon.consecutiveNat 0 p.T := by rw [hsplit]
  | launchedAtHorizon launch learnerSeed hlaunch hat =>
      have hstrict := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict
        p rate source rewards C_star C_h launch learnerSeed hlaunch
      have hprefix := ActualInitializationHorizon.sourceInitializedRun_chronological
        p rate source rewards C_star C_h
      rw [← hstrict.2.2.2, hat] at hprefix
      have hprojection := times_projection p rate source rewards C_star C_h
        (.launchedAtHorizon launch learnerSeed hlaunch hat)
      rw [hprojection]
      simpa [initializationRecords, postlaunchRecords, ActualInitializationRun.PhysicalRoundRecord.times,
        List.map_append, List.map_map, Function.comp_def] using hprefix
  | exhausted live hexhausted =>
      have hexhaust := ActualInitializationHorizon.sourceInitializedRun_exhaustion_reaches_horizon
        p rate source rewards C_star C_h live hexhausted
      have hprefix := ActualInitializationHorizon.sourceInitializedRun_chronological
        p rate source rewards C_star C_h
      rw [hexhaust.1] at hprefix
      have hprojection := times_projection p rate source rewards C_star C_h
        (.exhausted live hexhausted)
      rw [hprojection]
      simpa [initializationRecords, postlaunchRecords, ActualInitializationRun.PhysicalRoundRecord.times,
        List.map_append, List.map_map, Function.comp_def] using hprefix

/-- The exported constructor retains exactly `T` time, action and feedback
entries, with the same complete record spine. -/
theorem sourceInitializedActualCompleteHistory_lengths (p : Parameters)
    (rate : RateInput p) (source : SourceInput p) (rewards : GridRewardTable p)
    (C_star C_h : ℝ) :
    let history := sourceInitializedActualCompleteHistory p rate source rewards C_star C_h;
      (physicalHistoryRecords history).length = p.T ∧
      (actionHistory history).length = p.T ∧ (feedbackHistory history).length = p.T := by
  let history := sourceInitializedActualCompleteHistory p rate source rewards C_star C_h
  have hchron := sourceInitializedActualCompleteHistory_times_values p rate source rewards
    C_star C_h
  have hlength := congrArg List.length hchron
  have hrecords : (times history).length = p.T := by
    simpa [ActualInitializationHorizon.consecutiveNat_length] using hlength
  refine ⟨?_, ?_, ?_⟩
  · simpa [times] using hrecords
  · have hActionsLength : (actionHistory history).length = (times history).length := by
      rw [actionHistory_projection p rate source rewards C_star C_h history,
        times_projection p rate source rewards C_star C_h history]
      simp [ActualInitializationRun.PhysicalRoundRecord.actions,
        ActualInitializationRun.PhysicalRoundRecord.times]
    exact hActionsLength.trans hrecords
  · have hFeedbackLength : (feedbackHistory history).length = (times history).length := by
      rw [feedbackHistory_projection p rate source rewards C_star C_h history,
        times_projection p rate source rewards C_star C_h history]
      simp [ActualInitializationRun.PhysicalRoundRecord.feedback,
        ActualInitializationRun.PhysicalRoundRecord.times]
    exact hFeedbackLength.trans hrecords

end Bandits.Support.ActualCompletePhysicalHistory

end
