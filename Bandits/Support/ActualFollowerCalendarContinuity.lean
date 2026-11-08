/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockFollowerLocality
public import Bandits.Support.ActualPostlaunchBlockFollowerLocality

import Lean.Elab.Tactic.Omega

/-!
# Actual follower storage on the complete physical calendar

This module projects one follower's complete retained state and outcome from
the actual source-initialized history. Its continuity proofs follow the real
initialization fold, launch handoff, and mixed postlaunch suffix.

Mathematical evidence: `sources/zip4/manuscript/01_introduction.tex:20-36`,
`sources/zip4/manuscript/07_public_setup.tex:28-38,55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131`,
`sources/zip4/manuscript/06_interruptions.tex:240-296`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.PublicDiscreteDraws
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationHorizon
open Bandits.Support.ActualPostlaunchPhysicalStep
open Bandits.Support.ActualPostlaunchFollowerMeasurability
open Bandits.Support.ActualPostlaunchStepMeasurability
open Bandits.Support.ActualPostlaunchPreparationMeasurability
open Bandits.Support.ActualCompletePhysicalHistory

namespace Bandits.Support.ActualFollowerCalendarContinuity

abbrev Parameters := ActualInitializationBlockFollowerLocality.Parameters
abbrev RateInput := ActualInitializationBlockFollowerLocality.RateInput

variable {p : Parameters} (rate : RateInput p)
  (source : BootstrapPrivateRoundStreams.SourceInput p)
  (rewards : ActualCompletePhysicalHistory.GridRewardTable p)
  (C_star C_h : ℝ) (i : Fin (p.m - 1))

private theorem consecutiveNat_getElem (start count idx : ℕ) (hidx : idx < count) :
    (ActualInitializationHorizon.consecutiveNat start count)[idx]'(by
      rw [ActualInitializationHorizon.consecutiveNat_length]
      exact hidx) = start + idx := by
  induction idx generalizing start count with
  | zero =>
      cases count with
      | zero => omega
      | succ count => simp [ActualInitializationHorizon.consecutiveNat]
  | succ idx ih =>
      cases count with
      | zero => omega
      | succ count =>
          simp only [ActualInitializationHorizon.consecutiveNat,
            List.getElem_cons_succ]
          have htail : idx < count := by omega
          have h := ih (start + 1) count htail
          omega

private theorem blockLength_pos {block : Fin (n_boot p)} :
    0 < BootstrapObservedFollower.blockLength p block := by
  have hstart := BootstrapObservedFollower.blockStart_lt_blockStop p block
  simp [BootstrapObservedFollower.blockLength]
  omega

include rate source rewards C_star C_h i

/-- Adjacent initialization records from one clipped-block fold retain the
same block and the literal next follower storage. -/
def initializationSameBlockFollowerStep
    {recordSource : BootstrapPrivateRoundStreams.SourceInput p}
    {recordRewards : ActualInitializationPhysicalStep.GridRewardTable p}
    (left right : ActualInitializationRun.PhysicalRoundRecord p rate
      recordSource recordRewards) : Prop :=
  left.block = right.block ∧
    left.time.val + 1 = right.time.val ∧
      HEq (right.followersBefore i) ((left.result.followers i).next)

omit source rewards in
/-- The physical records in the actual cursor fold are adjacent by the
recursive input's own `next` follower field. -/
theorem foldBlockAux_follower_chain
    {block : Fin (n_boot p)} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (input : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (blockRewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let folded := ActualInitializationRun.foldBlockAux p rate block input.1.1
      blockRewards C_star C_h cursor fuel hbudget input.1.2.1 input.1.2.2 input.2
    List.IsChain (initializationSameBlockFollowerStep rate i)
      folded.records := by
  change List.IsChain (initializationSameBlockFollowerStep rate i)
    (ActualInitializationRun.foldBlockAux p rate block input.1.1 blockRewards C_star C_h
      cursor fuel hbudget input.1.2.1 input.1.2.2 input.2).records
  induction fuel generalizing cursor with
  | zero =>
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
        hbudget blockRewards input
      have hrecords := congrArg (fun data => data.2.2) hd
      dsimp only at hrecords ⊢
      simp [hrecords]
  | succ fuel ih =>
      have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
        hbudget hc blockRewards input
      have hrecords := congrArg (fun data => data.2.2) hd
      dsimp only at hrecords
      let next := ActualInitializationCursorMeasurability.cursorSuccessorInput hc
        blockRewards input
      let tail := ActualInitializationRun.foldBlockAux p rate block next.1.1
        blockRewards C_star C_h (cursor + 1) fuel (by omega)
        next.1.2.1 next.1.2.2 next.2
      have htail := ih (by omega) next
      cases fuel with
      | zero =>
          have hzero := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
            (by omega) blockRewards
            (ActualInitializationCursorMeasurability.cursorSuccessorInput hc
              blockRewards input)
          have htailRecords := congrArg (fun data => data.2.2) hzero
          dsimp only at htailRecords
          change List.IsChain (initializationSameBlockFollowerStep rate i)
            (ActualInitializationRun.foldBlockAux p rate block input.1.1 blockRewards
              C_star C_h cursor 1 hbudget input.1.2.1 input.1.2.2 input.2).records
          rw [hrecords, htailRecords]
          exact List.IsChain.singleton _
      | succ fuel =>
          have hcNext : cursor + 1 < BootstrapObservedFollower.blockLength p block := by omega
          let nextInput := ActualInitializationCursorMeasurability.cursorSuccessorInput hc
            blockRewards input
          let first := ActualInitializationBlockFoldExact.cursorRecord hc blockRewards input
          let second := ActualInitializationBlockFoldExact.cursorRecord hcNext blockRewards
            nextInput
          have hbudgetTail : (cursor + 1) + (fuel + 1) =
              BootstrapObservedFollower.blockLength p block := by omega
          have htailData := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
            hbudgetTail hcNext blockRewards nextInput
          have htailRecordsEq := congrArg (fun data => data.2.2) htailData
          dsimp only at htailRecordsEq
          have hstep : initializationSameBlockFollowerStep rate i
              first second := by
            refine ⟨rfl, ?_, ?_⟩
            · simp [first, second, ActualInitializationBlockFoldExact.cursorRecord,
                ActualInitializationRun.blockTime]
              omega
            · dsimp [first, second, initializationSameBlockFollowerStep,
                ActualInitializationBlockFoldExact.cursorRecord, nextInput,
                ActualInitializationCursorMeasurability.cursorSuccessorInput]
              exact HEq.rfl
          have hchainTail : List.IsChain
              (initializationSameBlockFollowerStep rate i)
              (ActualInitializationBlockFoldExact.cursorRecord hcNext blockRewards nextInput ::
                (ActualInitializationRun.foldBlockAux p rate block
                  (ActualInitializationCursorMeasurability.cursorSuccessorInput hcNext
                    blockRewards nextInput).1.1 blockRewards C_star C_h
                  (cursor + 1 + 1) fuel (by omega)
                  (ActualInitializationCursorMeasurability.cursorSuccessorInput hcNext
                    blockRewards nextInput).1.2.1
                  (ActualInitializationCursorMeasurability.cursorSuccessorInput hcNext
                    blockRewards nextInput).1.2.2
                  (ActualInitializationCursorMeasurability.cursorSuccessorInput hcNext
                    blockRewards nextInput).2).records) := by
            rw [← htailRecordsEq]
            simpa [next, nextInput] using htail
          change List.IsChain (initializationSameBlockFollowerStep rate i)
            (ActualInitializationRun.foldBlockAux p rate block input.1.1 blockRewards
              C_star C_h cursor (fuel + 2) hbudget input.1.2.1 input.1.2.2 input.2).records
          rw [hrecords, htailRecordsEq]
          exact List.IsChain.cons_cons hstep hchainTail

omit source rewards i in
/-- The actual recursive cursor fold begins with its accepted cursor record. -/
lemma foldBlockAux_follower_head
    {block : Fin (n_boot p)} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (input : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (blockRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (hfuel : 0 < fuel) :
    (ActualInitializationRun.foldBlockAux p rate block input.1.1
      blockRewards C_star C_h cursor fuel hbudget input.1.2.1 input.1.2.2 input.2).records.head? =
      some (ActualInitializationBlockFoldExact.cursorRecord hcursor blockRewards input) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
        hbudget hcursor blockRewards input
      have hrecords := congrArg (fun data => data.2.2) hd
      dsimp only at hrecords
      rw [hrecords]
      rfl

omit source rewards C_star C_h in
private theorem foldBlock_follower_head
    {block : Fin (n_boot p)}
    (blockSource : BootstrapPrivateRoundStreams.SourceInput p)
    (blockRewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (carry : ActualInitializationRun.BlockCarry p rate block) :
    (ActualInitializationRun.foldBlock p rate block blockSource blockRewards carry).records.head? =
        some (ActualInitializationBlockFoldExact.cursorRecord
          (blockLength_pos (p := p) (block := block)) blockRewards
          (ActualInitializationBlockFoldMeasurability.actualCursorZeroInput
            (⟨blockSource, carry, rfl, rfl⟩ :
              ActualInitializationBlockMeasurability.BlockInput
                p rate block carry.C_star carry.C_h))) ∧
      (ActualInitializationBlockFoldExact.cursorRecord
          (blockLength_pos (p := p) (block := block)) blockRewards
          (ActualInitializationBlockFoldMeasurability.actualCursorZeroInput
            (⟨blockSource, carry, rfl, rfl⟩ :
              ActualInitializationBlockMeasurability.BlockInput
                p rate block carry.C_star carry.C_h))).followersBefore i =
        ActualInitializationRun.beginFollowerBlock p rate block blockSource i
          (carry.followers i) := by
  let input : ActualInitializationBlockMeasurability.BlockInput
      p rate block carry.C_star carry.C_h := ⟨blockSource, carry, rfl, rfl⟩
  let x := ActualInitializationBlockFoldMeasurability.actualCursorZeroInput input
  have hdata := ActualInitializationBlockFoldExact.foldBlock_zero_input_data blockRewards input
  have hrecords := congrArg (fun data => data.2.2) hdata
  dsimp only at hrecords
  have hcursor : 0 < BootstrapObservedFollower.blockLength p block := blockLength_pos
  have hhead := foldBlockAux_follower_head (rate := rate)
    (C_star := carry.C_star) (C_h := carry.C_h)
    (block := block) (cursor := 0) (fuel := BootstrapObservedFollower.blockLength p block)
    (hbudget := by simp) (input := x) (blockRewards := blockRewards)
    (hcursor := hcursor) (hfuel := by omega)
  refine ⟨?_, ?_⟩
  · rw [hrecords]
    exact hhead
  · simp [ActualInitializationBlockFoldExact.cursorRecord,
      ActualInitializationBlockFoldMeasurability.actualCursorZeroInput,
      ActualInitializationRun.beginBlock,
      ActualInitializationRun.beginFollowerBlock]

omit source rewards in
/-- The last actual cursor record stores precisely the final folded follower. -/
theorem foldBlockAux_follower_last
    {block : Fin (n_boot p)} {cursor fuel : ℕ}
    (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (input : ActualInitializationCursorMeasurability.CursorInput
      p rate block C_star C_h cursor)
    (blockRewards : ActualInitializationPhysicalStep.GridRewardTable p) :
    let folded := ActualInitializationRun.foldBlockAux p rate block input.1.1
      blockRewards C_star C_h cursor fuel hbudget input.1.2.1 input.1.2.2 input.2
    ∀ r ∈ folded.records.getLast?, r.block = block ∧
      HEq ((r.result.followers i).next) (folded.followers i) := by
  dsimp only
  induction fuel generalizing cursor with
  | zero =>
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
        hbudget blockRewards input
      have hr := congrArg (fun d => d.2.2) hd
      dsimp only at hr
      rw [hr]
      simp only [List.getLast?_nil, Option.not_mem_none, false_implies, implies_true]
  | succ fuel ih =>
      have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
      have hd := ActualInitializationBlockFoldExact.foldBlockAux_succ_data
        hbudget hc blockRewards input
      have hr := congrArg (fun d => d.2.2) hd
      have hf := congrArg (fun d => d.2.1) hd
      dsimp only at hr hf
      rw [hr, hf]
      cases fuel with
      | zero =>
          have hz := ActualInitializationBlockFoldExact.foldBlockAux_zero_data
            (by omega) blockRewards
            (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input)
          have hzr := congrArg (fun d => d.2.2) hz
          have hzf := congrArg (fun d => d.2.1) hz
          dsimp only at hzr hzf
          rw [hzr, hzf]
          intro r h
          change some (ActualInitializationBlockFoldExact.cursorRecord hc blockRewards input) = some r at h
          have he := (Option.some.inj h).symm
          subst r
          exact ⟨rfl, HEq.rfl⟩
      | succ fuel =>
          have hn : cursor + 1 < BootstrapObservedFollower.blockLength p block := by omega
          have ht := ActualInitializationBlockFoldExact.foldBlockAux_succ_data (fuel := fuel)
            (by omega) hn blockRewards
            (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input)
          have htr := congrArg (fun d => d.2.2) ht
          dsimp only at htr
          have hi := ih (by omega)
            (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input)
          intro r h
          apply hi r
          have hnonempty : (ActualInitializationRun.foldBlockAux p rate block
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input).1.1
              blockRewards C_star C_h (cursor + 1) (fuel + 1) (by omega)
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input).1.2.1
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input).1.2.2
              (ActualInitializationCursorMeasurability.cursorSuccessorInput hc blockRewards input).2).records ≠ [] := by
            rw [htr]
            exact List.cons_ne_nil _ _
          rw [List.getLast?_cons_of_ne_nil
            (x := ActualInitializationBlockFoldExact.cursorRecord hc blockRewards input) hnonempty] at h
          exact h

/-- The original complete history, bound once for the projections below. -/
def actualHistory : ActualCompletePhysicalHistory.CompleteHistory p rate source rewards C_star C_h :=
  ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h

/-- The sole retained record at a calendar position. The bound follows from
the actual complete-history length theorem; no default record is introduced. -/
def calendarRecord (t : Fin p.T) :
    ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards := by
  let h := actualHistory rate source rewards C_star C_h
  have hlength : (ActualCompletePhysicalHistory.physicalHistoryRecords h).length = p.T := by
    simpa [h, actualHistory] using
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards
        C_star C_h).1
  exact (ActualCompletePhysicalHistory.physicalHistoryRecords h)[t.val]'(by omega)

/-- The original block tag stored by either constructor of an actual history
record. -/
def recordBlock
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards) : Fin (n_boot p) :=
  match record with
  | .initialization r => r.block
  | .postlaunch r => r.block

/-- The actual pre-round follower state retained by either record constructor. -/
def recordFollowerBefore
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards)
    (follower : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.FollowerState p rate
      (recordBlock rate source rewards record) :=
  match record with
  | .initialization r => r.followersBefore follower
  | .postlaunch r => r.input.state.followers follower

/-- The actual post-observation follower outcome retained by either record
constructor, including its prepared arm and full next storage. -/
def recordFollowerOutcome
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards)
    (follower : Fin (p.m - 1)) :
    ActualInitializationPhysicalStep.FollowerOutcome p rate
      (recordBlock rate source rewards record) :=
  match record with
  | .initialization r => r.result.followers follower
  | .postlaunch r => r.result.followers follower

/-- The block index assigned to calendar time by the original source calendar. -/
def calendarBlockIndex (t : Fin p.T) : Fin (n_boot p) :=
  BootstrapDimensions.roundBlockIndex p t

/-- The actual boundary output at the last postlaunch block of the retained
suffix. -/
def terminalBoundaryRecord
    {p : Parameters} {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p}
    {rewards : ActualCompletePhysicalHistory.GridRewardTable p}
    {block : Fin (n_boot p)} {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0} :
    (suffix : ActualCompletePhysicalHistory.PostlaunchSuffix p rate source rewards block state) →
      ActualCompletePhysicalHistory.PostlaunchBoundaryRecord p rate
  | .final trace _ => ActualCompletePhysicalHistory.postlaunchBoundaryRecord trace
  | .successor _ _ _ _ tail => terminalBoundaryRecord tail

/-- The accepted terminal follower output retained by the actual history.
There is no physical successor after the horizon. -/
def terminalFollowerOutput : ActualInitializationPhysicalStep.BoundaryFollowerOutput p rate :=
  match actualHistory rate source rewards C_star C_h with
  | .launchedBefore _ _ _ _ suffix => (terminalBoundaryRecord suffix).outputs i
  | .launchedAtHorizon _ _ _ _ =>
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i
  | .exhausted _ _ =>
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i

include rate source rewards C_star C_h i

omit i in
/-- Every projected record has the queried calendar time. -/
theorem calendarRecord_time (t : Fin p.T) :
    (calendarRecord rate source rewards C_star C_h t).time = t := by
  let h := actualHistory rate source rewards C_star C_h
  let rs := ActualCompletePhysicalHistory.physicalHistoryRecords h
  have hlen : rs.length = p.T := by
    simpa [h, rs, actualHistory] using
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards
        C_star C_h).1
  have hchron := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_times_values p rate source
    rewards C_star C_h
  have hchron' :
      ((rs.map ActualCompletePhysicalHistory.PhysicalHistoryRecord.time).map Fin.val) =
        ActualInitializationHorizon.consecutiveNat 0 p.T := by
    simpa [rs, h, actualHistory, ActualCompletePhysicalHistory.times] using hchron
  have hvalid : t.val <
      ((rs.map ActualCompletePhysicalHistory.PhysicalHistoryRecord.time).map Fin.val).length := by
    simp only [List.length_map]
    rw [hlen]
    exact t.isLt
  have hpoint := getElem_congr hchron' (i := t.val) (j := t.val) rfl hvalid
  have hstandard := consecutiveNat_getElem 0 p.T t.val t.isLt
  have htimeValue : (calendarRecord rate source rewards C_star C_h t).time.val = t.val := by
    simpa [calendarRecord, actualHistory, h, rs, ActualCompletePhysicalHistory.times] using
      hpoint.trans hstandard
  exact Fin.ext htimeValue

omit i in
/-- The stored block is exactly the quotient-calendar block. -/
theorem calendarRecord_block (t : Fin p.T) :
    recordBlock rate source rewards (calendarRecord rate source rewards C_star C_h t) =
      calendarBlockIndex t := by
  let record := calendarRecord rate source rewards C_star C_h t
  have htime := calendarRecord_time rate source rewards C_star C_h t
  have hrecordMem : record.time ∈ BootstrapDimensions.calendarBlock p
      (recordBlock rate source rewards record) := by
    cases record with
    | initialization r =>
        exact (ActualInitializationPhysicalStep.step_succeeds_iff_ready rate r.block r.time r.coordinatorBefore
          r.followersBefore source rewards).mp ⟨r.result, r.executed⟩ |>.2.1
    | postlaunch r =>
        have hmem := ActualInitializationRun.blockTime_mem p r.block r.cursor r.input.cursor_lt
        change ActualInitializationRun.blockTime p r.block r.cursor r.input.cursor_lt ∈
          BootstrapDimensions.calendarBlock p r.block
        exact hmem
  have hmem : t ∈ BootstrapDimensions.calendarBlock p
      (recordBlock rate source rewards record) := by
    rw [← htime]
    exact hrecordMem
  apply Fin.ext
  have hquot := (BootstrapDimensions.mem_calendarBlock_iff_quotient p
    (recordBlock rate source rewards record) t).mp hmem
  exact hquot

/-- The player's feedback entry is read from the same indexed actual record. -/
theorem calendarRecord_playerFeedback (t : Fin p.T) :
    (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (actualHistory rate source rewards C_star C_h)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
        have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
          p rate source rewards C_star C_h
        have hlen : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
            (actualHistory rate source rewards C_star C_h)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
          simpa [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
            ActualCompletePhysicalHistory.feedbackHistory, actualHistory] using h.1
        rw [hlen]
        exact t.isLt) =
      (calendarRecord rate source rewards C_star C_h t).feedback
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  simp [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
    ActualCompletePhysicalHistory.feedbackHistory,
    actualHistory, calendarRecord, List.getElem_map]

/-- The player's arm entry is read from the same indexed actual record. -/
theorem calendarRecord_playerArm (t : Fin p.T) :
    (ActualCompletePhysicalHistory.playerArmHistory
      (actualHistory rate source rewards C_star C_h)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
        have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
          p rate source rewards C_star C_h
        have hlen : (ActualCompletePhysicalHistory.playerArmHistory
            (actualHistory rate source rewards C_star C_h)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
          simpa [ActualCompletePhysicalHistory.playerArmHistory,
            ActualCompletePhysicalHistory.actionHistory, actualHistory] using h.1
        rw [hlen]
        exact t.isLt) =
      (ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions
        (calendarRecord rate source rewards C_star C_h t))
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
  simp [ActualCompletePhysicalHistory.playerArmHistory,
    ActualCompletePhysicalHistory.actionHistory,
    actualHistory, calendarRecord, List.getElem_map]

omit rewards C_star C_h in
private theorem preparedCodeArm_eq_of_localCode_decode
    {block : Fin (n_boot p)} (time : Fin p.T)
    (code : ActualPostlaunchFollowerMeasurability.LocalCode (rate := rate) block)
    (outcome : ActualInitializationPhysicalStep.FollowerOutcome p rate block)
    (hdecode : ActualPostlaunchFollowerMeasurability.decodeLocalCode
      source time i code = some outcome) :
    ActualInitializationPreparationMeasurability.preparedFollowerCodeArm code.1 =
      outcome.prepared.arm := by
  cases hprepared : ActualInitializationPreparationMeasurability.decodePreparedFollowerCode
      (rate := rate) (block := block) i source time code.1 with
  | none =>
      simp [ActualPostlaunchFollowerMeasurability.decodeLocalCode, hprepared] at hdecode
  | some prepared =>
      have houtcome : ⟨prepared,
          ActualInitializationRoundMeasurability.followerStateOfCode p rate block code.2.2⟩ =
            outcome := by
        simpa [ActualPostlaunchFollowerMeasurability.decodeLocalCode, hprepared] using hdecode
      have harm := ActualPostlaunchPreparationMeasurability.preparedFollowerCodeArm_eq_of_decode
        (rate := rate) (block := block) i source time code.1 prepared hprepared
      cases houtcome
      exact harm

omit rewards C_star C_h in
private theorem postlaunchLocalCode_decode_of_cursor_eq
    {block : Fin (n_boot p)} {cursor actualCursor : Nat}
    (input : ActualPostlaunchPhysicalStep.PhysicalInput
      (p := p) (rate := rate) block actualCursor)
    (hcursorEq : cursor = actualCursor)
    (hsource : input.source = source)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor
      (input.state.followers i))
    (ownY : Fin (D p + 1))
    (hfeedback : ownY = ActualPostlaunchPhysicalStep.physicalFeedback
      (ActualPostlaunchPhysicalStep.prepare input)
      (PublicDiscreteDraws.followerPlayer p.two_le_m i)) :
    ActualPostlaunchFollowerMeasurability.decodeLocalCode source input.time i
      (ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
          (input.state.followers i) hstate ownY)) =
      some ((ActualPostlaunchPhysicalStep.step input).followers i) := by
  cases hcursorEq
  have hcode : ActualPostlaunchFollowerMeasurability.localCodeOnCursor
      (rate := rate) hcursor i
      (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
        (input.state.followers i) hstate ownY) =
      ActualPostlaunchStepMeasurability.followerLocalCode i input := by
    simp [ActualPostlaunchStepMeasurability.followerLocalCode,
      ActualPostlaunchStepMeasurability.followerInput,
      ActualPostlaunchPreparationMeasurability.cursorFollower,
      ActualPostlaunchFollowerMeasurability.localInputOfComponents,
      hsource, hfeedback]
  rw [← hsource] at hcode
  rw [← hsource, hcode]
  exact ActualPostlaunchStepMeasurability.decode_followerLocalCode input i

omit source rewards C_star C_h i in
private theorem followerAtCursor_cast
    {block block' : Fin (n_boot p)} {cursor cursor' : Nat}
    (eblock : block = block') (ecursor : cursor = cursor')
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower) :
    ActualInitializationRun.followerAtCursor p rate block' cursor'
      (cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) eblock)
        follower) := by
  cases eblock
  cases ecursor
  exact hstate

omit rewards C_star C_h in
private theorem decodeLocalCode_cast
    {block block' : Fin (n_boot p)} {cursor cursor' : Nat}
    (eblock : block = block') (ecursor : cursor = cursor')
    (time : Fin p.T)
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (hcursor' : cursor' < BootstrapObservedFollower.blockLength p block')
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (feedback : Fin (D p + 1))
    (outcome : ActualInitializationPhysicalStep.FollowerOutcome p rate block)
    (hdecode : ActualPostlaunchFollowerMeasurability.decodeLocalCode source time i
      (ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents source follower hstate feedback)) =
      some outcome) :
    ActualPostlaunchFollowerMeasurability.decodeLocalCode source time i
      (ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursor' i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
          (cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) eblock)
            follower)
          (followerAtCursor_cast (rate := rate) eblock ecursor follower hstate)
          feedback)) =
      some (cast (congrArg (ActualInitializationPhysicalStep.FollowerOutcome p rate) eblock)
        outcome) := by
  cases eblock
  cases ecursor
  exact hdecode

omit rewards C_star C_h in
private theorem decodeLocalCode_congr_time
    {block : Fin (n_boot p)} {time time' : Fin p.T}
    (etime : time = time')
    (code : ActualPostlaunchFollowerMeasurability.LocalCode (rate := rate) block)
    (outcome : ActualInitializationPhysicalStep.FollowerOutcome p rate block)
    (hdecode : ActualPostlaunchFollowerMeasurability.decodeLocalCode source time i code =
      some outcome) :
    ActualPostlaunchFollowerMeasurability.decodeLocalCode source time' i code =
      some outcome := by
  cases etime
  exact hdecode

omit rewards C_star C_h in
private theorem preparedCodeArm_cast
    {block block' : Fin (n_boot p)} {cursor cursor' : Nat}
    (eblock : block = block') (ecursor : cursor = cursor')
    (hcursor : cursor < BootstrapObservedFollower.blockLength p block)
    (hcursor' : cursor' < BootstrapObservedFollower.blockLength p block')
    (follower : ActualInitializationPhysicalStep.FollowerState p rate block)
    (hstate : ActualInitializationRun.followerAtCursor p rate block cursor follower)
    (feedback : Fin (D p + 1)) :
    ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
      (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hcursor' i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
          (cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) eblock)
            follower)
          (followerAtCursor_cast (rate := rate) eblock ecursor follower hstate)
          feedback)) =
    ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
      (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hcursor i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents source follower hstate feedback)) := by
  cases eblock
  cases ecursor
  rfl

omit C_star C_h in
/-- Each record's retained own feedback and incoming storage feed the same
cursor-local code that the accepted initialization or mixed step used. -/
private theorem physicalHistoryRecord_followerLocalCode
    (record : ActualCompletePhysicalHistory.PhysicalHistoryRecord p rate source rewards) :
    ∃ hcursor : record.time.val - BootstrapObservedFollower.blockStart p
        (recordBlock rate source rewards record) < BootstrapObservedFollower.blockLength p
          (recordBlock rate source rewards record),
    ∃ hstate : ActualInitializationRun.followerAtCursor p rate
        (recordBlock rate source rewards record)
        (record.time.val - BootstrapObservedFollower.blockStart p
          (recordBlock rate source rewards record))
        (recordFollowerBefore rate source rewards record i),
      ActualPostlaunchFollowerMeasurability.localTime (recordBlock rate source rewards record)
        (record.time.val - BootstrapObservedFollower.blockStart p
          (recordBlock rate source rewards record)) hcursor = record.time ∧
      ActualPostlaunchFollowerMeasurability.decodeLocalCode source record.time i
        (ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursor i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
            (recordFollowerBefore rate source rewards record i) hstate
            (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))) =
        some (recordFollowerOutcome rate source rewards record i) ∧
      ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions record
        (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
      ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
        (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hcursor i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
            (recordFollowerBefore rate source rewards record i) hstate
            (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))) := by
  cases record with
  | initialization initRecord =>
      dsimp only [recordBlock, recordFollowerBefore, recordFollowerOutcome,
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.time,
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.feedback,
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions]
      obtain ⟨hcursor, hstate, htime, hdecode⟩ :=
        ActualInitializationBlockFollowerLocality.initialization_record_localCode initRecord i
      refine ⟨hcursor, hstate, htime, hdecode, ?_⟩
      have hcodeArm := preparedCodeArm_eq_of_localCode_decode
        (rate := rate) (source := source) (i := i)
        (time := initRecord.time)
        (code := ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursor i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
            (initRecord.followersBefore i) hstate
            (initRecord.result.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))))
        (outcome := initRecord.result.followers i) hdecode
      have hprepared := ActualInitializationPhysicalStep.roundResult_follower_arm_preserved
        initRecord.result i
      calc
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions
            (.initialization initRecord) (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
            initRecord.result.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) := rfl
        _ = (initRecord.result.prepared.followers i).arm :=
          ActualInitializationPhysicalStep.actionProfile_follower initRecord.result.prepared i
        _ = (initRecord.result.followers i).prepared.arm := hprepared.symm
        _ = ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
            (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hcursor i
              (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
                (initRecord.followersBefore i) hstate
                (initRecord.result.feedback
                  (PublicDiscreteDraws.followerPlayer p.two_le_m i)))) := hcodeArm.symm
  | postlaunch mixedRecord =>
      set cursor : Nat := mixedRecord.time.val -
        BootstrapObservedFollower.blockStart p mixedRecord.block with hcursorDef
      have hcursorValue : cursor = mixedRecord.cursor := by
        rw [hcursorDef]
        dsimp [ActualCompletePhysicalHistory.MixedRoundRecord.time,
          ActualPostlaunchPhysicalStep.PhysicalInput.time, ActualInitializationRun.blockTime]
        omega
      subst cursor
      have hcursor : mixedRecord.cursor < BootstrapObservedFollower.blockLength p mixedRecord.block :=
        mixedRecord.input.cursor_lt
      have hstate : ActualInitializationRun.followerAtCursor p rate mixedRecord.block mixedRecord.cursor
          (mixedRecord.input.state.followers i) := mixedRecord.input.state.followers_at_cursor i
      have htime : ActualPostlaunchFollowerMeasurability.localTime mixedRecord.block mixedRecord.cursor
          hcursor = mixedRecord.time := rfl
      have hfeedback : mixedRecord.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
          ActualPostlaunchPhysicalStep.physicalFeedback
            (ActualPostlaunchPhysicalStep.prepare mixedRecord.input)
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
        change ActualPostlaunchPhysicalStep.physicalFeedback mixedRecord.result.prepared
            (PublicDiscreteDraws.followerPlayer p.two_le_m i) = _
        rw [mixedRecord.result_eq]
        rfl
      have hcursorOut : mixedRecord.time.val -
          BootstrapObservedFollower.blockStart p mixedRecord.block <
            BootstrapObservedFollower.blockLength p mixedRecord.block := by
        rw [hcursorValue]
        exact hcursor
      have hstateOut : ActualInitializationRun.followerAtCursor p rate mixedRecord.block
          (mixedRecord.time.val - BootstrapObservedFollower.blockStart p mixedRecord.block)
          (mixedRecord.input.state.followers i) := by
        rw [hcursorValue]
        exact hstate
      have htimeOut : ActualPostlaunchFollowerMeasurability.localTime mixedRecord.block
          (mixedRecord.time.val - BootstrapObservedFollower.blockStart p mixedRecord.block)
          hcursorOut = mixedRecord.time := by
        apply Fin.ext
        simp [ActualPostlaunchFollowerMeasurability.localTime,
          ActualInitializationRun.blockTime,
          ActualCompletePhysicalHistory.MixedRoundRecord.time,
          ActualPostlaunchPhysicalStep.PhysicalInput.time]
      let codeOut := ActualPostlaunchFollowerMeasurability.localCodeOnCursor hcursorOut i
        (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
          (mixedRecord.input.state.followers i) hstateOut
          (mixedRecord.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))
      have hdecodeOut : ActualPostlaunchFollowerMeasurability.decodeLocalCode source mixedRecord.time i
          codeOut = some (mixedRecord.result.followers i) := by
        simpa [codeOut, ActualCompletePhysicalHistory.MixedRoundRecord.time,
          mixedRecord.result_eq] using
          (postlaunchLocalCode_decode_of_cursor_eq (rate := rate) (source := source)
          (i := i)
          mixedRecord.input hcursorValue mixedRecord.input_source hcursorOut hstateOut
          (mixedRecord.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)) hfeedback)
      refine ⟨hcursorOut, hstateOut, htimeOut, hdecodeOut, ?_⟩
      have hcodeArm := preparedCodeArm_eq_of_localCode_decode
        (rate := rate) (source := source) (i := i)
        (time := mixedRecord.time) (code := codeOut)
        (outcome := mixedRecord.result.followers i) hdecodeOut
      have hprepared := ActualInitializationPhysicalStep.observeFollower_preserves_prepared_arm
        rate mixedRecord.block mixedRecord.input.time mixedRecord.input.source i
        (mixedRecord.result.prepared.followers i)
        (mixedRecord.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
        (mixedRecord.result.followers i) (mixedRecord.result.followerTransition i)
      calc
        ActualCompletePhysicalHistory.PhysicalHistoryRecord.actions
            (.postlaunch mixedRecord) (PublicDiscreteDraws.followerPlayer p.two_le_m i) =
            ActualPostlaunchPhysicalStep.actionProfile mixedRecord.result.prepared
              (PublicDiscreteDraws.followerPlayer p.two_le_m i) := rfl
        _ = (mixedRecord.result.prepared.followers i).arm :=
          ActualPostlaunchPhysicalStep.actionProfile_follower mixedRecord.result.prepared i
        _ = (mixedRecord.result.followers i).prepared.arm := hprepared.symm
        _ = ActualInitializationPreparationMeasurability.preparedFollowerCodeArm codeOut.1 :=
          hcodeArm.symm

/-- The within-block cursor at this calendar time. -/
def calendarCursor (t : Fin p.T) : ℕ :=
  t.val - BootstrapObservedFollower.blockStart p (calendarBlockIndex t)

/-- The complete follower state before its actual physical choice. -/
def calendarFollowerBefore (follower : Fin (p.m - 1)) (t : Fin p.T) :
    ActualInitializationPhysicalStep.FollowerState p rate (calendarBlockIndex t) := by
  let record := calendarRecord rate source rewards C_star C_h t
  exact cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
    (calendarRecord_block rate source rewards C_star C_h t))
    (recordFollowerBefore rate source rewards record follower)

/-- The complete follower outcome after the actual physical observation. -/
def calendarFollowerOutcome (follower : Fin (p.m - 1)) (t : Fin p.T) :
    ActualInitializationPhysicalStep.FollowerOutcome p rate (calendarBlockIndex t) := by
  let record := calendarRecord rate source rewards C_star C_h t
  exact cast (congrArg (ActualInitializationPhysicalStep.FollowerOutcome p rate)
    (calendarRecord_block rate source rewards C_star C_h t))
    (recordFollowerOutcome rate source rewards record follower)

/-- The complete stored follower state after this physical round. -/
def calendarFollowerAfter (follower : Fin (p.m - 1)) (t : Fin p.T) :
    ActualInitializationPhysicalStep.FollowerState p rate (calendarBlockIndex t) :=
  (calendarFollowerOutcome rate source rewards C_star C_h follower t).next

omit rate source rewards C_star C_h i in
/-- The offset belongs to the original clipped block, including the shortened
last block. -/
lemma calendarCursor_lt_blockLength (t : Fin p.T) :
    calendarCursor t <
      BootstrapObservedFollower.blockLength p
        (calendarBlockIndex t) := by
  have hmem := BootstrapDimensions.round_mem_quotient_block p t
  have hbounds := (BootstrapDimensions.mem_calendarBlock_iff p
    (calendarBlockIndex t) t).mp hmem
  simp only [calendarBlockIndex, BootstrapDimensions.roundBlockIndex,
    Fin.val_mk] at hbounds
  simp only [calendarCursor, calendarBlockIndex,
    BootstrapObservedFollower.blockStart, BootstrapObservedFollower.blockLength,
    BootstrapObservedFollower.blockStop, BootstrapDimensions.roundBlockIndex,
    Fin.val_mk]
  omega

omit rate source rewards C_star C_h i in
/-- The source time associated with a cursor is the calendar position itself. -/
lemma calendarLocalTime_eq_time (t : Fin p.T) :
    ActualPostlaunchFollowerMeasurability.localTime (calendarBlockIndex t)
      (calendarCursor t)
      (calendarCursor_lt_blockLength t) = t := by
  apply Fin.ext
  have hmem := BootstrapDimensions.round_mem_quotient_block p t
  have hbounds := (BootstrapDimensions.mem_calendarBlock_iff p
    (calendarBlockIndex t) t).mp hmem
  simp only [calendarBlockIndex, BootstrapDimensions.roundBlockIndex,
    Fin.val_mk] at hbounds
  simp [ActualPostlaunchFollowerMeasurability.localTime,
    ActualInitializationRun.blockTime, calendarCursor, calendarBlockIndex,
    BootstrapDimensions.roundBlockIndex, BootstrapObservedFollower.blockStart] at hbounds ⊢
  omega

include rate source rewards C_star C_h i

/-- The actual record at a calendar position supplies its existing cursor
follower, own feedback, decoded outcome, and prepared arm. -/
theorem calendar_record_localCode (t : Fin p.T) :
    ∃ hs_t : ActualInitializationRun.followerAtCursor p rate
        (calendarBlockIndex t) (calendarCursor t)
        (calendarFollowerBefore rate source rewards C_star C_h i t),
      ActualPostlaunchFollowerMeasurability.localTime (calendarBlockIndex t)
        (calendarCursor t) (calendarCursor_lt_blockLength t) = t ∧
      ActualPostlaunchFollowerMeasurability.decodeLocalCode source t i
        (ActualPostlaunchFollowerMeasurability.localCodeOnCursor
          (calendarCursor_lt_blockLength t) i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
            (calendarFollowerBefore rate source rewards C_star C_h i t) hs_t
            ((ActualCompletePhysicalHistory.playerGridFeedbackHistory
              (actualHistory rate source rewards C_star C_h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
                have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
                  p rate source rewards C_star C_h
                have hlen : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
                    (actualHistory rate source rewards C_star C_h)
                    (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
                  simpa [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
                    ActualCompletePhysicalHistory.feedbackHistory, actualHistory] using h.1
                rw [hlen]
                exact t.isLt)))) =
        some (calendarFollowerOutcome rate source rewards C_star C_h i t) ∧
      (ActualCompletePhysicalHistory.playerArmHistory
        (actualHistory rate source rewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
          have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
            p rate source rewards C_star C_h
          have hlen : (ActualCompletePhysicalHistory.playerArmHistory
              (actualHistory rate source rewards C_star C_h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
            simpa [ActualCompletePhysicalHistory.playerArmHistory,
              ActualCompletePhysicalHistory.actionHistory, actualHistory] using h.1
          rw [hlen]
          exact t.isLt) =
        ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
          (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
            (calendarCursor_lt_blockLength t) i
            (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
              (calendarFollowerBefore rate source rewards C_star C_h i t) hs_t
              ((ActualCompletePhysicalHistory.playerGridFeedbackHistory
                (actualHistory rate source rewards C_star C_h)
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
                  have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
                    p rate source rewards C_star C_h
                  have hlen : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
                      (actualHistory rate source rewards C_star C_h)
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
                    simpa [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
                      ActualCompletePhysicalHistory.feedbackHistory, actualHistory] using h.1
                  rw [hlen]
                  exact t.isLt)))) := by
  let record := calendarRecord rate source rewards C_star C_h t
  have hblock := calendarRecord_block rate source rewards C_star C_h t
  have htime := calendarRecord_time rate source rewards C_star C_h t
  obtain ⟨hrecordCursor, hrecordState, hrecordTime, hrecordDecode, hrecordArm⟩ :=
    physicalHistoryRecord_followerLocalCode (rate := rate) (source := source)
      (rewards := rewards) (i := i) record
  have hcursorEq : record.time.val - BootstrapObservedFollower.blockStart p
      (recordBlock rate source rewards record) = calendarCursor t := by
    simp [calendarCursor, calendarBlockIndex, record, htime, hblock]
  have hstate : ActualInitializationRun.followerAtCursor p rate
      (calendarBlockIndex t) (calendarCursor t)
      (calendarFollowerBefore rate source rewards C_star C_h i t) := by
    exact followerAtCursor_cast (rate := rate) hblock hcursorEq
      (recordFollowerBefore rate source rewards record i) hrecordState
  refine ⟨hstate, calendarLocalTime_eq_time t, ?_, ?_⟩
  · have hfeedback := calendarRecord_playerFeedback rate source rewards C_star C_h i t
    have hdecodeAtTime : ActualPostlaunchFollowerMeasurability.decodeLocalCode source t i
        (ActualPostlaunchFollowerMeasurability.localCodeOnCursor hrecordCursor i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
            (recordFollowerBefore rate source rewards record i) hrecordState
            (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))) =
        some (recordFollowerOutcome rate source rewards record i) := by
      exact decodeLocalCode_congr_time (rate := rate) (source := source) (i := i) htime
        (ActualPostlaunchFollowerMeasurability.localCodeOnCursor hrecordCursor i
          (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
            (recordFollowerBefore rate source rewards record i) hrecordState
            (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))))
        (recordFollowerOutcome rate source rewards record i) hrecordDecode
    have hdecodeCast := decodeLocalCode_cast (rate := rate) (source := source) (i := i)
      hblock hcursorEq t hrecordCursor (calendarCursor_lt_blockLength t)
      (recordFollowerBefore rate source rewards record i) hrecordState
      (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
      (recordFollowerOutcome rate source rewards record i) hdecodeAtTime
    simpa [calendarFollowerBefore, calendarFollowerOutcome, record,
      recordFollowerBefore, recordFollowerOutcome, ← hfeedback] using hdecodeCast
  · have harm := hrecordArm
    have hfeedback := calendarRecord_playerFeedback rate source rewards C_star C_h i t
    have harmCast := preparedCodeArm_cast (rate := rate) (source := source) (i := i)
      hblock hcursorEq hrecordCursor (calendarCursor_lt_blockLength t)
      (recordFollowerBefore rate source rewards record i) hrecordState
      (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i))
    calc
      (ActualCompletePhysicalHistory.playerArmHistory
        (actualHistory rate source rewards C_star C_h)
        (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
          have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
            p rate source rewards C_star C_h
          have hlen : (ActualCompletePhysicalHistory.playerArmHistory
              (actualHistory rate source rewards C_star C_h)
              (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
            simpa [ActualCompletePhysicalHistory.playerArmHistory,
              ActualCompletePhysicalHistory.actionHistory, actualHistory] using h.1
          rw [hlen]
          exact t.isLt) =
        record.actions (PublicDiscreteDraws.followerPlayer p.two_le_m i) := by
          simpa [record] using
            calendarRecord_playerArm rate source rewards C_star C_h i t
      _ = ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
          (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor hrecordCursor i
            (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
              (recordFollowerBefore rate source rewards record i) hrecordState
              (record.feedback (PublicDiscreteDraws.followerPlayer p.two_le_m i)))) := harm
      _ = ActualInitializationPreparationMeasurability.preparedFollowerCodeArm
          (ActualPostlaunchFollowerMeasurability.preparedCodeOnCursor
            (calendarCursor_lt_blockLength t) i
            (ActualPostlaunchFollowerMeasurability.localInputOfComponents source
              (calendarFollowerBefore rate source rewards C_star C_h i t) hstate
              ((ActualCompletePhysicalHistory.playerGridFeedbackHistory
                (actualHistory rate source rewards C_star C_h)
                (PublicDiscreteDraws.followerPlayer p.two_le_m i))[t.val]'(by
                  have h := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths
                    p rate source rewards C_star C_h
                  have hlen : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
                      (actualHistory rate source rewards C_star C_h)
                      (PublicDiscreteDraws.followerPlayer p.two_le_m i)).length = p.T := by
                    simpa [ActualCompletePhysicalHistory.playerGridFeedbackHistory,
                      ActualCompletePhysicalHistory.feedbackHistory, actualHistory] using h.1
                  rw [hlen]
                  exact t.isLt)))) := by
            simpa [calendarFollowerBefore, record, recordFollowerBefore,
              ← hfeedback] using harmCast.symm

omit i in
/-- The history abbreviation is the original source-initialized complete history. -/
theorem actualHistory_eq : actualHistory rate source rewards C_star C_h =
    sourceInitializedActualCompleteHistory p rate source rewards C_star C_h := rfl

omit i in
/-- The calendar lookup is the literal bounded lookup in the actual record list. -/
theorem calendarRecord_eq_getElem (t : Fin p.T) :
    calendarRecord rate source rewards C_star C_h t =
      (physicalHistoryRecords (actualHistory rate source rewards C_star C_h))[t.val]'(by
        rw [show (physicalHistoryRecords (actualHistory rate source rewards C_star C_h)).length = p.T from
          (sourceInitializedActualCompleteHistory_lengths p rate source rewards C_star C_h).1]
        exact t.isLt) := rfl

omit C_star C_h in
/-- Initialization readout retains the original complete incoming state and outcome. -/
theorem initialization_record_storage
    (r : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    recordBlock rate source rewards (.initialization r) = r.block ∧
      recordFollowerBefore rate source rewards (.initialization r) i = r.followersBefore i ∧
      recordFollowerOutcome rate source rewards (.initialization r) i = r.result.followers i := ⟨rfl, rfl, rfl⟩

omit C_star C_h in
/-- Mixed readout retains the original complete incoming state and outcome. -/
theorem postlaunch_record_storage (r : MixedRoundRecord p rate source rewards) :
    recordBlock rate source rewards (.postlaunch r) = r.block ∧
      recordFollowerBefore rate source rewards (.postlaunch r) i = r.input.state.followers i ∧
      recordFollowerOutcome rate source rewards (.postlaunch r) i = r.result.followers i := ⟨rfl, rfl, rfl⟩

/-- The two calendar projections use only the proved original block transport. -/
theorem calendarFollower_storage_eq (t : Fin p.T) :
    calendarFollowerBefore rate source rewards C_star C_h i t =
      cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate)
        (calendarRecord_block rate source rewards C_star C_h t))
        (recordFollowerBefore rate source rewards
          (calendarRecord rate source rewards C_star C_h t) i) ∧
    calendarFollowerOutcome rate source rewards C_star C_h i t =
      cast (congrArg (ActualInitializationPhysicalStep.FollowerOutcome p rate)
        (calendarRecord_block rate source rewards C_star C_h t))
        (recordFollowerOutcome rate source rewards
          (calendarRecord rate source rewards C_star C_h t) i) := ⟨rfl, rfl⟩

/-- After-round storage is the whole next field of the actual decoded outcome. -/
theorem calendarFollowerAfter_eq (t : Fin p.T) :
    calendarFollowerAfter rate source rewards C_star C_h i t =
      (calendarFollowerOutcome rate source rewards C_star C_h i t).next := rfl

/-- Terminal readout selects the existing final suffix boundary, or the
initialization handoff when the launch has no within-horizon successor. -/
theorem terminalFollowerOutput_eq : terminalFollowerOutput rate source rewards C_star C_h i =
    match actualHistory rate source rewards C_star C_h with
    | .launchedBefore _ _ _ _ suffix => (terminalBoundaryRecord suffix).outputs i
    | .launchedAtHorizon _ _ _ _ =>
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i
    | .exhausted _ _ =>
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalHandoff.followers i := rfl

omit rate source rewards C_star C_h i in
/-- The quotient block and cursor are literal original calendar coordinates. -/
theorem calendarCoordinates_eq (t : Fin p.T) :
    calendarBlockIndex t = BootstrapDimensions.roundBlockIndex p t ∧
      calendarCursor t = t.val - BootstrapObservedFollower.blockStart p (calendarBlockIndex t) := ⟨rfl, rfl⟩

omit rate source rewards C_star C_h i in
/-- The suffix terminal projection is exactly its last retained boundary. -/
theorem terminalBoundaryRecord_eq_last {rate : RateInput p}
    {source : BootstrapPrivateRoundStreams.SourceInput p} {rewards : ActualCompletePhysicalHistory.GridRewardTable p}
    {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state) :
    suffix.boundaries.getLast? = some (terminalBoundaryRecord suffix) := by
  induction suffix with
  | final => rfl
  | successor trace hasNext next next_eq tail ih =>
      change (postlaunchBoundaryRecord trace :: tail.boundaries).getLast? = _
      rw [List.getLast?_cons_of_ne_nil (by cases tail <;> exact List.cons_ne_nil _ _)]
      exact ih

section Continuity

local notation "rb" => recordBlock rate source rewards
local notation "rf" => recordFollowerBefore rate source rewards
local notation "ro" => recordFollowerOutcome rate source rewards
local notation "stored" => (fun r : PhysicalHistoryRecord p rate source rewards =>
  (@Sigma.mk _ (ActualInitializationPhysicalStep.FollowerState p rate) (rb r) (rf r i)))
local notation "updated" => (fun r : PhysicalHistoryRecord p rate source rewards =>
  (@Sigma.mk _ (ActualInitializationPhysicalStep.FollowerState p rate) (rb r) (FollowerOutcome.next (ro r i))))
local notation "Next" => (fun a b : PhysicalHistoryRecord p rate source rewards =>
  stored b = updated a ∨
    Fin.val (rb a) + 1 = Fin.val (rb b) ∧
      rf b i = beginFollowerBlock p rate (rb b) source i
        (followerCarryAtBlockBoundary p rate (rb a) (FollowerOutcome.next (ro a i))))

omit C_star C_h in
private theorem initialization_block_data (block : Fin (n_boot p))
    (carry : ActualInitializationRun.BlockCarry p rate block) :
    let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
    let rs := folded.records.map PhysicalHistoryRecord.initialization
    rs ≠ [] ∧
      (∀ r ∈ rs.head?, stored r =
        ⟨block, beginFollowerBlock p rate block source i (carry.followers i)⟩) ∧
      (∀ r ∈ rs.getLast?, updated r = ⟨block, folded.followers i⟩) ∧
      List.IsChain Next rs := by
  dsimp only
  let input : ActualInitializationBlockMeasurability.BlockInput
      p rate block carry.C_star carry.C_h := ⟨source, carry, rfl, rfl⟩
  let x := ActualInitializationBlockFoldMeasurability.actualCursorZeroInput input
  have hd := ActualInitializationBlockFoldExact.foldBlock_zero_input_data rewards input
  have hr := congrArg (fun d => d.2.2) hd
  have hf := congrArg (fun d => d.2.1) hd
  dsimp only at hr hf
  have hh := foldBlock_follower_head (rate := rate) (i := i) source rewards carry
  have hn : (ActualInitializationRun.foldBlock p rate block source rewards carry).records ≠ [] := by
    intro he
    rw [he] at hh
    cases hh.1
  refine ⟨fun h => hn (List.map_eq_nil_iff.mp h), ?_, ?_, ?_⟩
  · intro r h
    rw [List.head?_map, hh.1] at h
    change some (PhysicalHistoryRecord.initialization
      (ActualInitializationBlockFoldExact.cursorRecord
        (blockLength_pos (p := p) (block := block)) rewards x)) = some r at h
    have he := (Option.some.inj h).symm
    subst r
    apply Sigma.ext rfl
    exact heq_of_eq hh.2
  · intro r h
    rw [List.getLast?_map] at h
    obtain ⟨a, ha, he⟩ := Option.mem_map.mp h
    subst r
    rw [hr] at ha
    have hl := foldBlockAux_follower_last (rate := rate) (i := i)
      (C_star := carry.C_star) (C_h := carry.C_h)
      (fuel := BootstrapObservedFollower.blockLength p block) (by simp) x rewards a ha
    apply Sigma.ext hl.1
    rw [hf]
    exact hl.2
  · apply (List.isChain_map _).mpr
    have hc := foldBlockAux_follower_chain (rate := rate) (i := i)
      (C_star := carry.C_star) (C_h := carry.C_h)
      (fuel := BootstrapObservedFollower.blockLength p block) (by simp) x rewards
    rw [hr]
    apply hc.imp
    intro a b hab
    left
    exact Sigma.ext hab.1.symm hab.2.2

omit C_star C_h in
private theorem mixed_trace_data {block : Fin (n_boot p)} {cursor stop : ℕ}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block cursor}
    (trace : MixedBlockTrace p rate source rewards block cursor state stop) :
    let rs := trace.records.map PhysicalHistoryRecord.postlaunch
    (∀ r ∈ rs.head?, stored r = ⟨block, state.followers i⟩) ∧
      (∀ r ∈ rs.getLast?, updated r = ⟨block, trace.finalState.followers i⟩) ∧
      List.IsChain Next rs := by
  induction trace with
  | done state =>
      simp only [MixedBlockTrace.records, List.map_nil, List.head?_nil,
        List.getLast?_nil, Option.not_mem_none, false_implies, implies_true,
        List.isChain_nil, and_self]
  | @step cursor stop state input hstate hsource hrewards result hresult tail hlt ih =>
      simp only [MixedBlockTrace.records, List.map_cons]
      refine ⟨?_, ?_, ?_⟩
      · intro r h
        have he : r = .postlaunch ⟨block, cursor, input, hsource, hrewards, result, hresult⟩ := by
          change some (.postlaunch ⟨block, cursor, input, hsource, hrewards, result, hresult⟩) = some r at h
          exact (Option.some.inj h).symm
        subst r
        exact congrArg (fun s => (⟨block, s.followers i⟩ : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b)) hstate
      · intro r h
        by_cases he : tail.records = []
        · have hf : (⟨block, tail.finalState.followers i⟩ :
              Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) =
              ⟨block, result.nextState.followers i⟩ := by
            cases tail with
            | done => rfl
            | step => simp only [MixedBlockTrace.records, List.cons_ne_nil] at he
          change r ∈ (PhysicalHistoryRecord.postlaunch
            ⟨block, cursor, input, hsource, hrewards, result, hresult⟩ ::
              tail.records.map PhysicalHistoryRecord.postlaunch).getLast? at h
          rw [he] at h
          change some (.postlaunch ⟨block, cursor, input, hsource, hrewards, result, hresult⟩) = some r at h
          have heq := (Option.some.inj h).symm
          subst r
          exact hf.symm
        · rw [List.getLast?_cons_of_ne_nil (fun h => he (List.map_eq_nil_iff.mp h))] at h
          exact ih.2.1 r h
      · apply ih.2.2.cons
        intro r h
        left
        exact (ih.1 r h).trans (by rfl)

omit C_star C_h in
private theorem boundary_join {block next : Fin (n_boot p)}
    (after : ActualInitializationPhysicalStep.FollowerState p rate block)
    (a b : PhysicalHistoryRecord p rate source rewards)
    (ha : updated a = ⟨block, after⟩)
    (hb : stored b = ⟨next, beginFollowerBlock p rate next source i
      (followerCarryAtBlockBoundary p rate block after)⟩)
    (hnext : block.val + 1 = next.val) : Next a b := by
  obtain ⟨ea, heqa⟩ := Sigma.mk.inj ha
  obtain ⟨eb, heqb⟩ := Sigma.mk.inj hb
  subst block
  subst next
  have hafter := eq_of_heq heqa
  have hbefore := eq_of_heq heqb
  right
  exact ⟨hnext, by rw [hbefore, hafter]⟩

omit C_star C_h in
private theorem initialization_run_data (fuel : ℕ) :
    ∀ (block : Fin (n_boot p)) (carry : ActualInitializationRun.BlockCarry p rate block),
    n_boot p - block.val = fuel →
    let run := ActualInitializationHorizon.runFrom p rate source rewards block carry
    let rs := run.records.map PhysicalHistoryRecord.initialization
    rs ≠ [] ∧
      (∀ r ∈ rs.head?, stored r =
        ⟨block, beginFollowerBlock p rate block source i (carry.followers i)⟩) ∧
      (∀ r ∈ rs.getLast?, updated r = ⟨run.terminalBlock, run.terminalFold.followers i⟩) ∧
      List.IsChain Next rs := by
  classical
  induction fuel with
  | zero =>
      intro block carry hmeasure
      have := block.isLt
      omega
  | succ fuel ih =>
      intro block carry hmeasure
      dsimp only
      let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
      let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        carry.C_star carry.C_h folded
      have hd := initialization_block_data rate source rewards i block carry
      by_cases hs : ∃ next nextCarry, handoff.disposition = .continueNext next nextCarry
      · obtain ⟨next, nextCarry, hnext⟩ := hs
        have hfacts := ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts
          folded next nextCarry hnext
        have ht := ih next nextCarry (by have := next.isLt; omega)
        have he := ActualInitializationHorizonObservation.runData_continue carry next nextCarry hnext
        have hr := congrArg (fun d => d.2.1.map PhysicalHistoryRecord.initialization) he
        have hf := congrArg (fun d =>
          (⟨d.1.1, d.1.2.2.2.1.followers i⟩ : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b)) he
        simp only [ActualInitializationHorizonObservation.runData,
          ActualInitializationHorizonObservation.terminalData, List.map_append] at hr hf
        rw [hr]
        refine ⟨List.append_ne_nil_of_left_ne_nil hd.1 _, ?_, ?_, ?_⟩
        · rw [List.head?_append_of_ne_nil _ hd.1]
          exact hd.2.1
        · rw [List.getLast?_append_of_ne_nil _ ht.1]
          intro r h
          exact (ht.2.2.1 r h).trans hf.symm
        · apply hd.2.2.2.append ht.2.2.2
          intro a ha b hb
          have hcarry := hfacts.2.2.2.choose_spec.2.2.2 i
          have hb' := ht.2.1 b hb
          rw [hcarry] at hb'
          exact boundary_join rate source rewards i (folded.followers i) a b
            (hd.2.2.1 a ha) hb' hfacts.1.symm
      · have hstop : ∀ next nextCarry, handoff.disposition ≠ .continueNext next nextCarry := by
          intro next nextCarry h
          exact hs ⟨next, nextCarry, h⟩
        have he := ActualInitializationHorizonObservation.runData_stop carry hstop
        have hr := congrArg (fun d => d.2.1.map PhysicalHistoryRecord.initialization) he
        have hf := congrArg (fun d =>
          (⟨d.1.1, d.1.2.2.2.1.followers i⟩ : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b)) he
        dsimp only [ActualInitializationHorizonObservation.runData,
          ActualInitializationHorizonObservation.terminalData] at hr hf
        rw [hr]
        exact ⟨hd.1, hd.2.1, fun r h => (hd.2.2.1 r h).trans hf.symm, hd.2.2.2⟩

omit C_star C_h i in
private theorem mixed_block_nonempty {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (trace : MixedBlockTrace p rate source rewards block 0 state
      (BootstrapObservedFollower.blockLength p block)) : trace.records ≠ [] := by
  have ht := congrArg List.length
    (MixedBlockTrace.times_values p rate source rewards block 0 _ state trace)
  simp only [MixedBlockTrace.times, List.length_map,
    ActualInitializationHorizon.consecutiveNat_length, Nat.sub_zero] at ht
  intro he
  rw [he] at ht
  have hp := blockLength_pos (p := p) (block := block)
  simp only [List.length_nil] at ht
  omega

omit C_star C_h in
private theorem postlaunch_suffix_data {block : Fin (n_boot p)}
    {state : ActualPostlaunchPhysicalStep.PostlaunchState (p := p) (rate := rate) block 0}
    (suffix : PostlaunchSuffix p rate source rewards block state) :
    let rs := suffix.records.map PhysicalHistoryRecord.postlaunch
    rs ≠ [] ∧
      (∀ r ∈ rs.head?, stored r = ⟨block, state.followers i⟩) ∧
      (∀ r ∈ rs.getLast?, boundaryOutputFromFollower p rate (rb r) (ro r i).next =
        (terminalBoundaryRecord suffix).outputs i) ∧ List.IsChain Next rs := by
  induction suffix with
  | final trace last =>
      have hd := mixed_trace_data rate source rewards i trace
      have hn := mixed_block_nonempty rate source rewards trace
      refine ⟨fun h => hn (List.map_eq_nil_iff.mp h), hd.1, ?_, hd.2.2⟩
      intro r h
      exact congrArg (fun s : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b =>
        boundaryOutputFromFollower p rate s.1 s.2) (hd.2.1 r h)
  | @successor block state trace hasNext next next_eq tail ih =>
      have hd := mixed_trace_data rate source rewards i trace
      have hn : trace.records.map PhysicalHistoryRecord.postlaunch ≠ [] :=
        fun h => mixed_block_nonempty rate source rewards trace (List.map_eq_nil_iff.mp h)
      simp only [PostlaunchSuffix.records, List.map_append]
      refine ⟨List.append_ne_nil_of_left_ne_nil hn _, ?_, ?_, ?_⟩
      · rw [List.head?_append_of_ne_nil _ hn]
        exact hd.1
      · rw [List.getLast?_append_of_ne_nil _ ih.1]
        exact ih.2.2.1
      · apply hd.2.2.append ih.2.2.2
        intro a ha b hb
        subst next
        apply boundary_join rate source rewards i
          (next := ActualInitializationRun.successorBlock p block hasNext)
          (trace.finalState.followers i) a b
          (hd.2.1 a ha) _ rfl
        simpa only [ActualPostlaunchPhysicalStep.crossSuccessorBoundary,
          ActualPostlaunchPhysicalStep.beginSuccessorFollower,
          ActualPostlaunchPhysicalStep.boundaryCarry_eq_actual_boundary] using ih.2.1 b hb

private theorem initialization_terminal_output :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    run.terminalHandoff.followers i = boundaryOutputFromFollower p rate run.terminalBlock
      (run.terminalFold.followers i) := by
  dsimp only
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have hc : followerAtCursor p rate run.terminalBlock
      (BootstrapObservedFollower.blockLength p run.terminalBlock)
      (run.terminalFold.followers i) := by
    have h := run.terminalFold.invariant.2.2.1 i
    simpa only [run.terminalFold.consumed_eq_blockLength] using h
  have hh := ActualInitializationHorizon.combinedBoundaryHandoff_follower_step run.terminalFold i
  rw [← run.terminalHandoff_eq] at hh
  have hb := boundaryOutputAtCursor_step p rate run.terminalBlock (run.terminalFold.followers i) hc
  exact Except.ok.inj (hh.symm.trans hb)

private theorem actual_history_data :
    let rs := physicalHistoryRecords (actualHistory rate source rewards C_star C_h)
    rs ≠ [] ∧
      (∀ r ∈ rs.head?, stored r = ⟨ActualInitializationRun.firstBlock p,
        beginFollowerBlock p rate (ActualInitializationRun.firstBlock p) source i
          ((initialCarry p rate C_star C_h).followers i)⟩) ∧
      (∀ r ∈ rs.getLast?, boundaryOutputFromFollower p rate (rb r) (ro r i).next =
        terminalFollowerOutput rate source rewards C_star C_h i) ∧ List.IsChain Next rs := by
  have hi := initialization_run_data rate source rewards i
    (n_boot p - (ActualInitializationRun.firstBlock p).val)
    (ActualInitializationRun.firstBlock p) (initialCarry p rate C_star C_h) rfl
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  change let rs := run.records.map PhysicalHistoryRecord.initialization;
    rs ≠ [] ∧ (∀ r ∈ rs.head?, stored r = ⟨ActualInitializationRun.firstBlock p,
      beginFollowerBlock p rate (ActualInitializationRun.firstBlock p) source i
        ((initialCarry p rate C_star C_h).followers i)⟩) ∧
      (∀ r ∈ rs.getLast?, updated r = ⟨run.terminalBlock, run.terminalFold.followers i⟩) ∧
      List.IsChain Next rs at hi
  have ho := initialization_terminal_output rate source rewards C_star C_h i
  dsimp only
  cases he : actualHistory rate source rewards C_star C_h with
  | launchedBefore launch seed launched before suffix =>
      have hp := postlaunch_suffix_data rate source rewards i suffix
      simp only [physicalHistoryRecords, initializationRecords, postlaunchRecords]
      refine ⟨List.append_ne_nil_of_left_ne_nil hi.1 _, ?_, ?_, ?_⟩
      · rw [List.head?_append_of_ne_nil _ hi.1]
        exact hi.2.1
      · rw [List.getLast?_append_of_ne_nil _ hp.1]
        simpa only [terminalFollowerOutput, he] using hp.2.2.1
      · apply hi.2.2.2.append hp.2.2.2
        intro a ha b hb
        have hb' := hp.2.1 b hb
        rw [sourceInitializedLaunchSuccessorInput_followers p rate source rewards C_star C_h
          launch seed launched before i] at hb'
        dsimp only [ActualPostlaunchPhysicalStep.sourceInitializedLaunchedFollower] at hb'
        rw [ho] at hb'
        exact boundary_join rate source rewards i
          ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalFold.followers i)
          a b (hi.2.2.1 a ha) hb' rfl
  | launchedAtHorizon launch seed launched atHorizon =>
      simp only [physicalHistoryRecords, initializationRecords, postlaunchRecords,
        List.map_nil, List.append_nil]
      refine ⟨hi.1, hi.2.1, ?_, hi.2.2.2⟩
      intro r hr
      have h := congrArg (fun s : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b =>
        boundaryOutputFromFollower p rate s.1 s.2) (hi.2.2.1 r hr)
      exact h.trans (by simpa only [terminalFollowerOutput, he] using ho.symm)
  | exhausted live exhausted =>
      simp only [physicalHistoryRecords, initializationRecords, postlaunchRecords,
        List.map_nil, List.append_nil]
      refine ⟨hi.1, hi.2.1, ?_, hi.2.2.2⟩
      intro r hr
      have h := congrArg (fun s : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b =>
        boundaryOutputFromFollower p rate s.1 s.2) (hi.2.2.1 r hr)
      exact h.trans (by simpa only [terminalFollowerOutput, he] using ho.symm)

private theorem calendar_storage (t : Fin p.T) :
    (⟨calendarBlockIndex t, calendarFollowerBefore rate source rewards C_star C_h i t⟩ :
      Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) =
        stored (calendarRecord rate source rewards C_star C_h t) ∧
    (⟨calendarBlockIndex t, calendarFollowerAfter rate source rewards C_star C_h i t⟩ :
      Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) =
        updated (calendarRecord rate source rewards C_star C_h t) := by
  have hb := calendarRecord_block rate source rewards C_star C_h t
  have transport (b b' : Fin (n_boot p)) (e : b = b')
      (x : ActualInitializationPhysicalStep.FollowerState p rate b)
      (o : ActualInitializationPhysicalStep.FollowerOutcome p rate b) :
      (⟨b', cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) e) x⟩ :
        Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) = ⟨b, x⟩ ∧
      (⟨b', (cast (congrArg (ActualInitializationPhysicalStep.FollowerOutcome p rate) e) o).next⟩ :
        Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) = ⟨b, o.next⟩ := by
    cases e
    exact ⟨rfl, rfl⟩
  exact transport _ _ hb _ _

omit source rewards C_star C_h i in
private theorem state_eq_cast {b b' : Fin (n_boot p)} (e : b = b')
    {x : ActualInitializationPhysicalStep.FollowerState p rate b}
    {y : ActualInitializationPhysicalStep.FollowerState p rate b'}
    (h : (⟨b', y⟩ : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) = ⟨b, x⟩) :
    y = cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) e) x := by
  cases e
  exact eq_of_heq (Sigma.mk.inj h).2

/-- The actual zero-time record starts from the original initial carry and
first block's original private triple. -/
theorem calendar_follower_initial :
    let z : Fin p.T := ⟨0, by have := p.one_le_T; omega⟩
    let e : ActualInitializationRun.firstBlock p = calendarBlockIndex z := by
      apply Fin.ext
      change 0 = 0 / B_boot p
      exact (Nat.zero_div _).symm
    calendarFollowerBefore rate source rewards C_star C_h i z =
      cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) e)
        (beginFollowerBlock p rate (ActualInitializationRun.firstBlock p) source i
          ((initialCarry p rate C_star C_h).followers i)) := by
  dsimp only
  apply state_eq_cast (rate := rate)
    (b := ActualInitializationRun.firstBlock p) (b' := calendarBlockIndex ⟨0, _⟩)
    (by apply Fin.ext; exact (Nat.zero_div _).symm)
  have hd := actual_history_data rate source rewards C_star C_h i
  apply (calendar_storage rate source rewards C_star C_h i _).1.trans
  apply hd.2.1
  change (physicalHistoryRecords (actualHistory rate source rewards C_star C_h)).head? =
    some (calendarRecord rate source rewards C_star C_h ⟨0, _⟩)
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem]
  rfl

/-- Genuine adjacent calendar rounds copy the entire own storage inside a
block and apply the original boundary carry and next private triple across
blocks. The unequal case also proves the actual block and endpoint facts. -/
theorem calendar_follower_successor (t : Fin p.T) (ht : t.val + 1 < p.T) :
    let u : Fin p.T := ⟨t.val + 1, ht⟩
    if e : calendarBlockIndex t = calendarBlockIndex u then
      calendarFollowerBefore rate source rewards C_star C_h i u =
        cast (congrArg (ActualInitializationPhysicalStep.FollowerState p rate) e)
          (calendarFollowerAfter rate source rewards C_star C_h i t)
    else
      (calendarBlockIndex t).val + 1 = (calendarBlockIndex u).val ∧
      t.val + 1 = BootstrapObservedFollower.blockStop p (calendarBlockIndex t) ∧
      u.val = BootstrapObservedFollower.blockStart p (calendarBlockIndex u) ∧
      calendarFollowerBefore rate source rewards C_star C_h i u =
        beginFollowerBlock p rate (calendarBlockIndex u) source i
          (followerCarryAtBlockBoundary p rate (calendarBlockIndex t)
            (calendarFollowerAfter rate source rewards C_star C_h i t)) := by
  let u : Fin p.T := ⟨t.val + 1, ht⟩
  have hlen : (physicalHistoryRecords (actualHistory rate source rewards C_star C_h)).length = p.T :=
    (sourceInitializedActualCompleteHistory_lengths p rate source rewards C_star C_h).1
  have hrel := (actual_history_data rate source rewards C_star C_h i).2.2.2.getElem t.val
    (by rw [hlen]; exact ht)
  change Next (calendarRecord rate source rewards C_star C_h t)
    (calendarRecord rate source rewards C_star C_h u) at hrel
  have hs := (calendar_storage rate source rewards C_star C_h i u).1
  have ha := (calendar_storage rate source rewards C_star C_h i t).2
  dsimp only
  split_ifs with e
  · rcases hrel with hsame | ⟨hnext, _⟩
    · exact state_eq_cast (rate := rate) e (hs.trans (hsame.trans ha.symm))
    · rw [calendarRecord_block, calendarRecord_block, ← e] at hnext
      omega
  · obtain ⟨hnext, hbefore⟩ := hrel.resolve_left (by
      intro hsame
      exact e (congrArg Sigma.fst (hs.trans (hsame.trans ha.symm))).symm)
    have hnext' := hnext
    rw [calendarRecord_block, calendarRecord_block] at hnext'
    have hstart := ActualInitializationHorizon.nextActivationRound_eq_successor_start
      (calendarBlockIndex t) (calendarBlockIndex u) hnext'.symm
    change BootstrapObservedFollower.blockStop p (calendarBlockIndex t) + 1 =
      BootstrapObservedFollower.blockStart p (calendarBlockIndex u) + 1 at hstart
    have hb := (BootstrapDimensions.mem_calendarBlock_iff p (calendarBlockIndex t) t).mp
      (BootstrapDimensions.round_mem_quotient_block p t)
    have hu := (BootstrapDimensions.mem_calendarBlock_iff p (calendarBlockIndex u) u).mp
      (BootstrapDimensions.round_mem_quotient_block p u)
    change _ ≤ t.val ∧ t.val < BootstrapObservedFollower.blockStop p (calendarBlockIndex t) at hb
    change BootstrapObservedFollower.blockStart p (calendarBlockIndex u) ≤ t.val + 1 ∧ _ at hu
    have hend : t.val + 1 = BootstrapObservedFollower.blockStop p (calendarBlockIndex t) := by omega
    have hbegin : u.val = BootstrapObservedFollower.blockStart p (calendarBlockIndex u) := by
      change t.val + 1 = BootstrapObservedFollower.blockStart p (calendarBlockIndex u)
      omega
    refine ⟨hnext', hend, hbegin, ?_⟩
    apply eq_of_heq
    apply (Sigma.mk.inj (show
      (⟨calendarBlockIndex u, calendarFollowerBefore rate source rewards C_star C_h i u⟩ :
        Σ b, ActualInitializationPhysicalStep.FollowerState p rate b) =
      ⟨calendarBlockIndex u, beginFollowerBlock p rate (calendarBlockIndex u) source i
        (followerCarryAtBlockBoundary p rate (calendarBlockIndex t)
          (calendarFollowerAfter rate source rewards C_star C_h i t))⟩ from ?_)).2
    calc
      _ = stored (calendarRecord rate source rewards C_star C_h u) := hs
      _ = ⟨rb (calendarRecord rate source rewards C_star C_h u),
          beginFollowerBlock p rate (rb (calendarRecord rate source rewards C_star C_h u)) source i
            (followerCarryAtBlockBoundary p rate (rb (calendarRecord rate source rewards C_star C_h t))
              (ro (calendarRecord rate source rewards C_star C_h t) i).next)⟩ :=
        congrArg (Sigma.mk _) hbefore
      _ = _ := by
        rw [calendarRecord_block]
        exact congrArg (fun s : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b =>
          (⟨calendarBlockIndex u, beginFollowerBlock p rate (calendarBlockIndex u) source i
            (followerCarryAtBlockBoundary p rate s.1 s.2)⟩ :
              Σ b, ActualInitializationPhysicalStep.FollowerState p rate b)) ha.symm

/-- At the actual last round, the retained terminal output is exactly its
boundary conversion. There is no extra physical round after the horizon. -/
theorem calendar_follower_terminal :
    let l : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
    terminalFollowerOutput rate source rewards C_star C_h i =
      boundaryOutputFromFollower p rate (calendarBlockIndex l)
        (calendarFollowerAfter rate source rewards C_star C_h i l) := by
  dsimp only
  let l : Fin p.T := ⟨p.T - 1, by have := p.one_le_T; omega⟩
  have hd := actual_history_data rate source rewards C_star C_h i
  have hlen := (sourceInitializedActualCompleteHistory_lengths p rate source rewards C_star C_h).1
  have hm : calendarRecord rate source rewards C_star C_h l ∈
      (physicalHistoryRecords (actualHistory rate source rewards C_star C_h)).getLast? := by
    change (physicalHistoryRecords (actualHistory rate source rewards C_star C_h)).getLast? = some _
    rw [List.getLast?_eq_getElem?, show (physicalHistoryRecords
      (actualHistory rate source rewards C_star C_h)).length = p.T from hlen,
      List.getElem?_eq_getElem]
    rfl
  have hr := hd.2.2.1 _ hm
  have hs := congrArg (fun s : Σ b, ActualInitializationPhysicalStep.FollowerState p rate b =>
    boundaryOutputFromFollower p rate s.1 s.2)
    (calendar_storage rate source rewards C_star C_h i l).2
  exact (hs.trans hr).symm

end Continuity

end Bandits.Support.ActualFollowerCalendarContinuity

end
