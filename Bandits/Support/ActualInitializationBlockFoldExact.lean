/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualInitializationBlockFoldMeasurability

/-!
# Physical identification of the actual initialization block code

The original cursor invariant, original source (including the private array
and selected-row coordinate), and entire grid reward table are retained.
This is an internal correspondence for the existing physical recursion.

`CursorInput` has exactly `R.BlockInvariant`: continuation data have the given
block, original IDs and whole selected row, original block target, and fixed
`C_star`/`C_h`; cursor is at most the clipped length; each bootstrap follower
has processed exactly cursor rounds, while each declared follower retains its
activation bound at this time; a launched continuation is allowed only at the
clipped endpoint. Readiness and the next invariant are produced, not inputs.
`BlockInput` retains the full incoming coordinator, unlaunched monitor, and
every bootstrap or declared ordinary/dagger carry, with its original activation.

The decoder consumes the accepted stored-round decoder and reconstructs proof
fields by checks. It does not obtain numerical output by running `step` or
`foldBlockAux`. Its output is the existing `R.BlockFoldOutput`. The physical
map uses the existing `B.BlockFoldCode` and F's existing measurable structure.
No runFrom/horizon, boundary next-carry, locality, probability, manuscript
totality, or regret assertion is established here.

Sources: `sources/zip4/manuscript/07_public_setup.tex:55-114`,
`sources/zip4/manuscript/appendix_b_communication.tex:94-131,160-165`, and
`sources/zip4/manuscript/06_interruptions.tex:235-297`.
-/

@[expose] public section

noncomputable section

open scoped Classical

open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapObservedFollower
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.ActualInitializationRun
open Bandits.Support.ActualInitializationBlockMeasurability
open Bandits.Support.ActualInitializationCursorMeasurability
open Bandits.Support.ActualInitializationBlockFoldMeasurability

namespace Bandits.Support.ActualInitializationBlockFoldExact

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput

variable {p : Parameters} {rate : RateInput p} {block : Fin (n_boot p)}
  {C_star C_h : ℝ} {cursor : ℕ}

private theorem record_mk_congr {source : SourceInput p} {rewards : GridRewardTable p}
    (time : Fin p.T) (coordinator : PrelaunchBlock p)
    (followers : Fin (p.m - 1) → FollowerState p rate block)
    (left right : RoundResult p rate block) (heq : left = right)
    (hl : step rate block time coordinator followers source rewards = .ok left)
    (hr : step rate block time coordinator followers source rewards = .ok right)
    (htl : left.prepared.time = time) (htr : right.prepared.time = time) :
    (⟨block, time, coordinator, followers, left, hl, htl⟩ :
      PhysicalRoundRecord p rate source rewards) =
      ⟨block, time, coordinator, followers, right, hr, htr⟩ := by
  cases heq
  rfl

/-- The first physical record on the genuine cursor domain. The result is the
accepted cursor result and its execution certificate uses the same source,
incoming local states, and rewards. -/
def cursorRecord (hcursor : cursor < blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    PhysicalRoundRecord p rate input.1.1 rewards :=
  ⟨block, blockTime p block cursor hcursor, prelaunchAtCursor hcursor input,
    input.1.2.2, actualCursorResult hcursor rewards input,
    actualCursorResult_step hcursor rewards input, rfl⟩

/-- The cursor adapter keeps the actual source time. -/
theorem actualCursorResult_time (hcursor : cursor < blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    (actualCursorResult hcursor rewards input).prepared.time =
      blockTime p block cursor hcursor := rfl

/-- Zero fuel keeps all physical data, including a launch at the clipped
endpoint. It creates no action at the exclusive horizon endpoint. -/
theorem foldBlockAux_zero_data
    (hbudget : cursor + 0 = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    let whole := foldBlockAux p rate block input.1.1 rewards C_star C_h cursor 0
      hbudget input.1.2.1 input.1.2.2 input.2
    (whole.phase, whole.followers, whole.records) =
      (input.1.2.1, input.1.2.2, []) := by
  unfold foldBlockAux
  dsimp only [Nat.casesAuxOn]
  rfl

/-- Successor data equation for the original physical fold. Both the head
and the recursive input are identified with the accepted cursor adapter;
no step law or successful trace is supplied by the caller. -/
theorem foldBlockAux_succ_data {fuel : ℕ}
    (hbudget : cursor + (fuel + 1) = blockLength p block)
    (hcursor : cursor < blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    let nextInput := cursorSuccessorInput hcursor rewards input
    let tail := foldBlockAux p rate block nextInput.1.1 rewards C_star C_h
      (cursor + 1) fuel (by omega) nextInput.1.2.1 nextInput.1.2.2 nextInput.2
    let whole := foldBlockAux p rate block input.1.1 rewards C_star C_h cursor (fuel + 1)
      hbudget input.1.2.1 input.1.2.2 input.2
    (whole.phase, whole.followers, whole.records) =
      (tail.phase, tail.followers, cursorRecord hcursor rewards input :: tail.records) := by
  rcases input with ⟨⟨source, phase, followers⟩, hi⟩
  cases phase with
  | launched launch =>
      have hdone := hi.2.2.2
      exact False.elim (Nat.ne_of_lt hcursor hdone)
  | prelaunch coordinator =>
      dsimp only
      conv_lhs => unfold foldBlockAux
      dsimp (config := { zeta := false }) only [Nat.casesAuxOn, Nat.add]
      extract_lets +underBinder hc ht ready hct cp prep hp obs res hs fs inv rec tail
      have hpre : prelaunchAtCursor hcursor
          (⟨(source, (.prelaunch coordinator, followers)), hi⟩ :
            CursorInput p rate block C_star C_h cursor) = coordinator := rfl
      have hres : actualCursorResult hcursor rewards
          (⟨(source, (.prelaunch coordinator, followers)), hi⟩ :
            CursorInput p rate block C_star C_h cursor) = res := by
        apply actualCursorResult_eq_of_step
        rw [hpre]
        exact hs
      have hrec : rec = cursorRecord hcursor rewards
          (⟨(source, (.prelaunch coordinator, followers)), hi⟩ :
            CursorInput p rate block C_star C_h cursor) := by
        apply record_mk_congr
        exact hres.symm
      change (tail.phase, tail.followers, rec :: tail.records) = _
      rw [hrec]
      simp only [cursorSuccessorInput, hres]
      rfl

/-- The final continuation and every heterogeneous follower code are exactly
the encodings of the final physical states on this same input. -/
theorem actualBlockFoldCodeAux_final_states {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    let code := actualBlockFoldCodeAux cursor fuel hbudget rewards input
    let folded := foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel
      hbudget input.1.2.1 input.1.2.2 input.2
    code.phase = continuationCodeOf folded.phase ∧
      ∀ i, code.followers i = ActualInitializationRoundMeasurability.followerCodeOfState
        p rate block (folded.followers i) := by
  induction fuel generalizing cursor with
  | zero =>
      have hd := foldBlockAux_zero_data hbudget rewards input
      have hp := congrArg Prod.fst hd
      have hf := congrArg (fun data => data.2.1) hd
      dsimp only at hp hf
      dsimp only
      rw [actualBlockFoldCodeAux.eq_def]
      change continuationCodeOf input.1.2.1 = _ ∧ _
      rw [hp, hf]
      exact ⟨rfl, fun _ => rfl⟩
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      have hd := foldBlockAux_succ_data hbudget hc rewards input
      have hp := congrArg Prod.fst hd
      have hf := congrArg (fun data => data.2.1) hd
      dsimp only at hp hf
      have ht := ih (by omega) (cursorSuccessorInput hc rewards input)
      dsimp only
      rw [actualBlockFoldCodeAux.eq_def]
      change (actualBlockFoldCodeAux (cursor + 1) fuel (by omega) rewards
        (cursorSuccessorInput hc rewards input)).phase = _ ∧ _
      rw [hp, hf]
      exact ht

/-- Each player's chronological own-entry codes are exactly its own action
and collision-filtered grid observation from the same physical records. All
tags are retained; the equality rules out a missing or error-tagged ready
round without filtering the list. -/
theorem actualBlockFoldCodeAux_own_entries {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) (player : Fin p.m) :
    (actualBlockFoldCodeAux cursor fuel hbudget rewards input).rounds.map
        (fun code => ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput
          rate block code player) =
      (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
        input.1.2.1 input.1.2.2 input.2).records.map
          (fun record => Sum.inr (record.result.actions player, record.result.feedback player)) := by
  induction fuel generalizing cursor with
  | zero =>
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_zero_data hbudget rewards input)
      dsimp only at hr
      rw [actualBlockFoldCodeAux.eq_def, hr]
      rfl
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_succ_data hbudget hc rewards input)
      dsimp only at hr
      rw [actualBlockFoldCodeAux.eq_def, hr]
      simp only [List.map_cons]
      exact congrArg₂ List.cons (actualCursorOutputCode_own_entry hc rewards input player)
        (ih (by omega) (cursorSuccessorInput hc rewards input))

/-- The full simultaneous physical pair stored at one ready cursor. -/
theorem actualCursorOutputCode_joint
    (hcursor : cursor < blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    roundJointCode (actualCursorOutputCode hcursor rewards input).1 =
      Sum.inr ((actualCursorResult hcursor rewards input).actions,
        (actualCursorResult hcursor rewards input).feedback) := by
  cases hcode : (actualCursorOutputCode hcursor rewards input).1 with
  | inl failure =>
      have he := actualCursorOutputCode_own_entry hcursor rewards input
        (ActiveRoundActions.coordinator p.two_le_m)
      simp only [hcode, ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput,
        Sum.elim_inl] at he
      cases he
  | inr successful =>
      change Sum.inr successful.2.1 = _
      apply congrArg Sum.inr
      apply Prod.ext
      · funext player
        have he := actualCursorOutputCode_own_entry hcursor rewards input player
        simp only [hcode,
          ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput,
          Sum.elim_inr] at he
        exact congrArg Prod.fst (Sum.inr.inj he)
      · funext player
        have he := actualCursorOutputCode_own_entry hcursor rewards input player
        simp only [hcode,
          ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput,
          Sum.elim_inr] at he
        exact congrArg Prod.snd (Sum.inr.inj he)

/-- Full chronological simultaneous action/feedback pairs correspond to the
same physical record list, in order. -/
theorem actualBlockFoldCodeAux_joint_history {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    (actualBlockFoldCodeAux cursor fuel hbudget rewards input).rounds.map roundJointCode =
      (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
        input.1.2.1 input.1.2.2 input.2).records.map
          (fun record => Sum.inr (record.result.actions, record.result.feedback)) := by
  induction fuel generalizing cursor with
  | zero =>
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_zero_data hbudget rewards input)
      dsimp only at hr
      rw [actualBlockFoldCodeAux.eq_def, hr]
      rfl
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_succ_data hbudget hc rewards input)
      dsimp only at hr
      rw [actualBlockFoldCodeAux.eq_def, hr]
      simp only [List.map_cons]
      exact congrArg₂ List.cons (actualCursorOutputCode_joint hc rewards input)
        (ih (by omega) (cursorSuccessorInput hc rewards input))

private theorem blockFoldOutput_eq_of_data {source : SourceInput p}
    {rewards : GridRewardTable p}
    (left right : BlockFoldOutput p rate block source rewards C_star C_h cursor)
    (hdata : (left.phase, left.followers, left.records) =
      (right.phase, right.followers, right.records)) : left = right := by
  rcases left with ⟨lc, lp, lf, lr, li, hl, ln, lt⟩
  rcases right with ⟨rc, rp, rf, rr, ri, hr, rn, rt⟩
  obtain ⟨rfl, hrest⟩ := Prod.mk.inj hdata
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hrest
  have hc : lc = rc := hl.trans hr.symm
  cases hc
  rfl

private theorem blockFoldCode_eta (code : BlockFoldCode p rate block C_star C_h) :
    (⟨code.phase, code.followers, code.rounds⟩ : BlockFoldCode p rate block C_star C_h) =
      code := by
  cases code
  rfl

/-- Empty physical output, assembled from the terminal input without running
either the physical step or the fold. -/
def emptyCursorOutput (hbudget : cursor + 0 = blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    BlockFoldOutput p rate block input.1.1 rewards C_star C_h cursor where
  consumed := cursor
  phase := input.1.2.1
  followers := input.1.2.2
  records := []
  invariant := input.2
  consumed_eq_blockLength := by omega
  record_count := by simp only [List.length_nil, Nat.zero_add]
  chronological := by
    simp only [PhysicalRoundRecord.times, List.map_nil, List.length_nil, blockTimes]

/-- Prepend a decoded, certified round to an existing physical suffix. All
numerical fields come from the decoded result and tail. -/
def prependCursorOutput (hcursor : cursor < blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor)
    (result : RoundResult p rate block)
    (hstep : step rate block (blockTime p block cursor hcursor)
      (prelaunchAtCursor hcursor input) input.1.2.2 input.1.1 rewards = .ok result)
    (htime : result.prepared.time = blockTime p block cursor hcursor)
    (tail : BlockFoldOutput p rate block input.1.1 rewards C_star C_h (cursor + 1)) :
    BlockFoldOutput p rate block input.1.1 rewards C_star C_h cursor where
  consumed := tail.consumed
  phase := tail.phase
  followers := tail.followers
  records := ⟨block, blockTime p block cursor hcursor, prelaunchAtCursor hcursor input,
    input.1.2.2, result, hstep, htime⟩ :: tail.records
  invariant := tail.invariant
  consumed_eq_blockLength := tail.consumed_eq_blockLength
  record_count := by
    simp only [List.length_cons]
    have hn := tail.record_count
    omega
  chronological := by
    simp only [PhysicalRoundRecord.times, List.map_cons, List.length_cons, blockTimes]
    exact congrArg (List.cons (blockTime p block cursor hcursor)) tail.chronological

/-- Relative stored-round decoder. The accepted one-round decoder supplies
the result's data. The checks reconstruct its dependent execution, time, and
successor-invariant certificates; they never replace it with a rerun result.
Malformed and error-tagged rounds return `none`. -/
def decodeCursorRound (hcursor : cursor < blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor)
    (code : ActualInitializationStepMeasurability.ActualRoundOutputCode p rate block) :
    Option {result : RoundResult p rate block //
      step rate block (blockTime p block cursor hcursor) (prelaunchAtCursor hcursor input)
          input.1.2.2 input.1.1 rewards = .ok result ∧
        result.prepared.time = blockTime p block cursor hcursor ∧
        BlockInvariant p rate block input.1.1 C_star C_h (cursor + 1)
          result.coordinator.next (fun i => (result.followers i).next)} := by
  classical
  match ActualInitializationStepMeasurability.decodeActualRoundOutputCode rate block C_star C_h
      (roundInputAtCursor hcursor rewards input) code with
  | some (.ok result) =>
      exact if hvalid :
          step rate block (blockTime p block cursor hcursor) (prelaunchAtCursor hcursor input)
              input.1.2.2 input.1.1 rewards = .ok result ∧
            result.prepared.time = blockTime p block cursor hcursor ∧
            BlockInvariant p rate block input.1.1 C_star C_h (cursor + 1)
              result.coordinator.next (fun i => (result.followers i).next)
        then some ⟨result, hvalid⟩ else none
  | _ => exact none

/-- The actual stored head passes all certificate checks and restores every
field of the original physical result. -/
theorem decodeCursorRound_actual (hcursor : cursor < blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    decodeCursorRound hcursor rewards input (actualCursorOutputCode hcursor rewards input).1 =
      some ⟨actualCursorResult hcursor rewards input,
        actualCursorResult_step hcursor rewards input, actualCursorResult_time hcursor rewards input,
        actualCursorResult_invariant hcursor rewards input⟩ := by
  classical
  unfold decodeCursorRound
  rw [actualCursorOutputCode_round_reconstructs]
  dsimp only
  rw [dite_eq_left ⟨actualCursorResult_step hcursor rewards input,
    actualCursorResult_time hcursor rewards input,
    actualCursorResult_invariant hcursor rewards input⟩]

/-- Reconstruct the existing physical output from the complete stored code,
relative to the original cursor input and whole reward grid. A nonempty
suffix must decode every head and tail. At zero fuel the final codes must
match the retained states and the stored round list must be empty. -/
def decodeBlockFoldCodeAux :
    (cursor fuel : ℕ) → cursor + fuel = blockLength p block →
      (rewards : GridRewardTable p) →
      (input : CursorInput p rate block C_star C_h cursor) →
      BlockFoldCode p rate block C_star C_h →
      Option (BlockFoldOutput p rate block input.1.1 rewards C_star C_h cursor)
  | cursor, 0, hbudget, rewards, input, code => by
      classical
      exact if code.rounds = [] ∧ code.phase = continuationCodeOf input.1.2.1 ∧
          code.followers = (fun i => ActualInitializationRoundMeasurability.followerCodeOfState
            p rate block (input.1.2.2 i))
        then some (emptyCursorOutput hbudget rewards input) else none
  | cursor, fuel + 1, hbudget, rewards, input, code => by
      have hc : cursor < blockLength p block := by omega
      match code.rounds with
      | [] => exact none
      | head :: rounds =>
          match decodeCursorRound hc rewards input head with
          | none => exact none
          | some result =>
              let nextInput : CursorInput p rate block C_star C_h (cursor + 1) :=
                ⟨(input.1.1, (result.1.coordinator.next,
                  fun i => (result.1.followers i).next)), result.2.2.2⟩
              match decodeBlockFoldCodeAux (cursor + 1) fuel (by omega) rewards nextInput
                  ⟨code.phase, code.followers, rounds⟩ with
              | none => exact none
              | some tail =>
                  exact some (prependCursorOutput hc rewards input result.1
                    result.2.1 result.2.2.1 tail)
termination_by cursor fuel _ _ _ _ => fuel
decreasing_by omega

/-- Complete same-output restoration: final continuation, all heterogeneous
followers, and the exact ordered physical record list, with all certificates.
This is equality in the original `BlockFoldOutput`, not a projection or a
second execution schema. -/
theorem decodeBlockFoldCodeAux_actual {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    decodeBlockFoldCodeAux cursor fuel hbudget rewards input
        (actualBlockFoldCodeAux cursor fuel hbudget rewards input) =
      some (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
        input.1.2.1 input.1.2.2 input.2) := by
  induction fuel generalizing cursor with
  | zero =>
      rw [decodeBlockFoldCodeAux.eq_def, actualBlockFoldCodeAux.eq_def]
      simp only [and_self, ite_true]
      apply congrArg some
      apply blockFoldOutput_eq_of_data
      exact (foldBlockAux_zero_data hbudget rewards input).symm
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      rw [decodeBlockFoldCodeAux.eq_def, actualBlockFoldCodeAux.eq_def]
      dsimp only
      rw [decodeCursorRound_actual]
      dsimp only
      rw [blockFoldCode_eta]
      have ht := ih (by omega) (cursorSuccessorInput hc rewards input)
      dsimp only [cursorSuccessorInput] at ht ⊢
      rw [ht]
      apply congrArg some
      apply blockFoldOutput_eq_of_data
      exact (foldBlockAux_succ_data hbudget hc rewards input).symm

/-- Every record in the original block suffix belongs to this very block. -/
theorem foldBlockAux_records_block {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ∀ record ∈ (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
      input.1.2.1 input.1.2.2 input.2).records, record.block = block := by
  induction fuel generalizing cursor with
  | zero =>
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_zero_data hbudget rewards input)
      dsimp only at hr
      rw [hr]
      intro record hrecord
      cases hrecord
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_succ_data hbudget hc rewards input)
      dsimp only at hr
      rw [hr]
      intro record hrecord
      rcases List.mem_cons.mp hrecord with heq | htail
      · subst record
        rfl
      · exact ih (by omega) (cursorSuccessorInput hc rewards input) record htail

/-- Code one recorded round using its stored original pre-round states and
time, the full original source, and the fixed reward grid. This uses the
accepted one-round encoder and defines no further execution recursion. -/
def physicalRoundCode {source : SourceInput p} {rewards : GridRewardTable p}
    (C_star C_h : ℝ) (record : PhysicalRoundRecord p rate source rewards) :
    ActualInitializationStepMeasurability.ActualRoundOutputCode p rate record.block :=
  ActualInitializationStepMeasurability.actualRoundOutputCode rate record.block C_star C_h
    { time := record.time
      coordinatorRow := source.1.2 (selectedRowIndex p source)
      coordinatorIDs := source.1.1
      coordinator := (BootstrapCoordinatorRoundMeasurability.prelaunchCoordinates
        p record.coordinatorBefore).2
      followers := fun i => ActualInitializationRoundMeasurability.followerCodeOfState
        p rate record.block (record.followersBefore i)
      source := source
      rewards := rewards }

/-- Ordered record encoding. The proved block identities only transport the
dependent code types; no round, scalar, or failure tag is filtered. -/
def physicalRoundCodes {source : SourceInput p} {rewards : GridRewardTable p}
    (C_star C_h : ℝ) (records : List (PhysicalRoundRecord p rate source rewards))
    (hblocks : ∀ record ∈ records, record.block = block) :
    List (ActualInitializationStepMeasurability.ActualRoundOutputCode p rate block) :=
  records.pmap (P := fun record => record.block = block)
    (fun record hblock => hblock ▸ physicalRoundCode C_star C_h record) hblocks

/-- The recorded head and the cursor encoder use exactly the same input. -/
theorem physicalRoundCode_cursorRecord (hcursor : cursor < blockLength p block)
    (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    physicalRoundCode C_star C_h (cursorRecord hcursor rewards input) =
      (actualCursorOutputCode hcursor rewards input).1 := rfl

/-- The entire stored round-code list is the chronological encoding of the
same physical records, including complete preparation and observation data. -/
theorem actualBlockFoldCodeAux_rounds_eq_physicalRoundCodes {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    (actualBlockFoldCodeAux cursor fuel hbudget rewards input).rounds =
      physicalRoundCodes C_star C_h
        (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
          input.1.2.1 input.1.2.2 input.2).records
        (foldBlockAux_records_block hbudget rewards input) := by
  induction fuel generalizing cursor with
  | zero =>
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_zero_data hbudget rewards input)
      dsimp only at hr
      rw [actualBlockFoldCodeAux.eq_def]
      simp only [physicalRoundCodes, hr, List.pmap_nil]
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_succ_data hbudget hc rewards input)
      dsimp only at hr
      rw [actualBlockFoldCodeAux.eq_def]
      simp only [physicalRoundCodes, hr]
      apply congrArg₂ List.cons
      · exact (physicalRoundCode_cursorRecord hc rewards input).symm
      · exact ih (by omega) (cursorSuccessorInput hc rewards input)

/-- Encode the actual physical fold's final states and its complete record
list in the existing `BlockFoldCode` carrier. There is no new state or run. -/
def physicalBlockFoldCodeAux (cursor fuel : ℕ)
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    BlockFoldCode p rate block C_star C_h :=
  let folded := foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
    input.1.2.1 input.1.2.2 input.2
  ⟨continuationCodeOf folded.phase,
    fun i => ActualInitializationRoundMeasurability.followerCodeOfState
      p rate block (folded.followers i),
    physicalRoundCodes C_star C_h folded.records
      (foldBlockAux_records_block hbudget rewards input)⟩

/-- The actual physical map is exactly the already measurable code map,
including every final state and every chronological full round code. -/
theorem physicalBlockFoldCodeAux_eq_actualBlockFoldCodeAux {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    physicalBlockFoldCodeAux cursor fuel hbudget rewards input =
      actualBlockFoldCodeAux cursor fuel hbudget rewards input := by
  have hs := actualBlockFoldCodeAux_final_states hbudget rewards input
  have hr := actualBlockFoldCodeAux_rounds_eq_physicalRoundCodes hbudget rewards input
  rw [← blockFoldCode_eta (actualBlockFoldCodeAux cursor fuel hbudget rewards input)]
  unfold physicalBlockFoldCodeAux
  dsimp only
  congr 1
  · exact hs.1.symm
  · exact (funext hs.2).symm
  · exact hr.symm

/-- Transfer measurability through the physical map identity, using exactly
the accepted `BlockFoldCode` measurable structure and no second schema. -/
theorem measurable_physicalBlockFoldCodeAux {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p) :
    Measurable (physicalBlockFoldCodeAux (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) cursor fuel hbudget rewards) := by
  have heq : physicalBlockFoldCodeAux (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) cursor fuel hbudget rewards =
      actualBlockFoldCodeAux cursor fuel hbudget rewards :=
    funext (physicalBlockFoldCodeAux_eq_actualBlockFoldCodeAux hbudget rewards)
  rw [heq]
  exact measurable_actualBlockFoldCodeAux hbudget rewards

/-- Actions and complete grid feedback from `BlockFoldCode` are the same
chronological physical histories, with an explicit success tag at every round. -/
theorem actualBlockFoldCodeAux_actions_feedback {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    let code := actualBlockFoldCodeAux cursor fuel hbudget rewards input
    let folded := foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
      input.1.2.1 input.1.2.2 input.2
    code.actions = (PhysicalRoundRecord.actions folded.records).map Sum.inr ∧
      code.feedback = (PhysicalRoundRecord.feedback folded.records).map Sum.inr := by
  have hj := actualBlockFoldCodeAux_joint_history hbudget rewards input
  have ha := congrArg (List.map (Sum.map id Prod.fst)) hj
  have hy := congrArg (List.map (Sum.map id Prod.snd)) hj
  have hpa : ∀ code : ActualInitializationStepMeasurability.ActualRoundOutputCode p rate block,
      Sum.map id Prod.fst (roundJointCode code) =
        Sum.elim (fun _ => Sum.inl ()) (fun successful => Sum.inr successful.2.1.1) code := by
    intro code
    cases code <;> rfl
  have hpy : ∀ code : ActualInitializationStepMeasurability.ActualRoundOutputCode p rate block,
      Sum.map id Prod.snd (roundJointCode code) =
        Sum.elim (fun _ => Sum.inl ()) (fun successful => Sum.inr successful.2.1.2) code := by
    intro code
    cases code <;> rfl
  constructor
  · simpa only [BlockFoldCode.actions, PhysicalRoundRecord.actions, List.map_map,
      Function.comp_def, hpa, Sum.map_inr] using ha
  · simpa only [BlockFoldCode.feedback, PhysicalRoundRecord.feedback, List.map_map,
      Function.comp_def, hpy, Sum.map_inr] using hy

/-- The feedback in each actual record uses the original reward grid at the
recorded time and the same simultaneous action vector, with collision zeroing. -/
theorem foldBlockAux_record_feedback {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ∀ record ∈ (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
      input.1.2.1 input.1.2.2 input.2).records, ∀ player,
      record.result.feedback player =
        if FiniteBanditModel.collisionFreeFor record.result.actions player then
          rewards record.time (record.result.actions player) else 0 := by
  classical
  induction fuel generalizing cursor with
  | zero =>
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_zero_data hbudget rewards input)
      dsimp only at hr
      rw [hr]
      intro record hrecord
      cases hrecord
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      have hr := congrArg (fun data => data.2.2)
        (foldBlockAux_succ_data hbudget hc rewards input)
      dsimp only at hr
      rw [hr]
      intro record hrecord player
      rcases List.mem_cons.mp hrecord with heq | htail
      · subst record
        rfl
      · exact ih (by omega) (cursorSuccessorInput hc rewards input) record htail player

/-- Exact number of reconstructed records, transferred from the physical
fold's record-count certificate. -/
theorem decodeBlockFoldCodeAux_record_count {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    (decodeBlockFoldCodeAux cursor fuel hbudget rewards input
      (actualBlockFoldCodeAux cursor fuel hbudget rewards input)).map
        (fun folded => folded.records.length) = some fuel := by
  rw [decodeBlockFoldCodeAux_actual]
  apply congrArg some
  dsimp only
  have hn := (foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
    input.1.2.1 input.1.2.2 input.2).record_count
  rw [(foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
    input.1.2.1 input.1.2.2 input.2).consumed_eq_blockLength] at hn
  omega

/-- Exact chronological source times of the decoded stored rounds. -/
theorem decodeBlockFoldCodeAux_chronological {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    (decodeBlockFoldCodeAux cursor fuel hbudget rewards input
      (actualBlockFoldCodeAux cursor fuel hbudget rewards input)).map
        (fun folded => PhysicalRoundRecord.times folded.records) =
      some (blockTimes p block cursor fuel hbudget) := by
  rw [decodeBlockFoldCodeAux_actual]
  apply congrArg some
  let folded := foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel hbudget
    input.1.2.1 input.1.2.2 input.2
  have hn := folded.record_count
  rw [folded.consumed_eq_blockLength] at hn
  have hlength : folded.records.length = fuel := by omega
  simpa only [hlength] using folded.chronological

/-- The actual full block and the actual zero-cursor specialization have the
same physical data. Constants are the fixed constants in the incoming carry. -/
theorem foldBlock_zero_input_data (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    let folded := foldBlock p rate block input.1 rewards input.2.1
    let zero := actualCursorZeroInput input
    let localFold := foldBlockAux p rate block zero.1.1 rewards C_star C_h 0
      (blockLength p block) (by omega) zero.1.2.1 zero.1.2.2 zero.2
    (folded.phase, folded.followers, folded.records) =
      (localFold.phase, localFold.followers, localFold.records) := by
  rcases input with ⟨source, carry, hstar, hh⟩
  subst C_star
  subst C_h
  rfl

/-- All records of a full actual block have its actual block index. -/
theorem foldBlock_records_block (source : SourceInput p) (rewards : GridRewardTable p)
    (carry : BlockCarry p rate block) :
    ∀ record ∈ (foldBlock p rate block source rewards carry).records, record.block = block := by
  let input : BlockInput p rate block carry.C_star carry.C_h :=
    ⟨source, carry, rfl, rfl⟩
  exact foldBlockAux_records_block (by omega) rewards (actualCursorZeroInput input)

/-- The full physical fold encoded in the accepted carrier, jointly varying
in the entire original source and original incoming carry. -/
def physicalBlockFoldCodeOfInput (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) : BlockFoldCode p rate block C_star C_h :=
  let folded := foldBlock p rate block input.1 rewards input.2.1
  ⟨continuationCodeOf folded.phase,
    fun i => ActualInitializationRoundMeasurability.followerCodeOfState
      p rate block (folded.followers i),
    physicalRoundCodes C_star C_h folded.records
      (foldBlock_records_block input.1 rewards input.2.1)⟩

/-- Whole-block physical map identity with the accepted measurable producer. -/
theorem physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput
    (rewards : GridRewardTable p) (input : BlockInput p rate block C_star C_h) :
    physicalBlockFoldCodeOfInput rewards input = actualBlockFoldCodeOfInput rewards input := by
  rcases input with ⟨source, carry, hstar, hh⟩
  subst C_star
  subst C_h
  exact physicalBlockFoldCodeAux_eq_actualBlockFoldCodeAux (by omega) rewards
    (actualCursorZeroInput ⟨source, carry, rfl, rfl⟩)

/-- The actual full physical block code is measurable for each fixed whole
reward grid, with source and incoming carry jointly varying. -/
theorem measurable_physicalBlockFoldCodeOfInput (rewards : GridRewardTable p) :
    Measurable (physicalBlockFoldCodeOfInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards) := by
  have heq : physicalBlockFoldCodeOfInput (p := p) (rate := rate) (block := block)
      (C_star := C_star) (C_h := C_h) rewards = actualBlockFoldCodeOfInput rewards :=
    funext (physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput rewards)
  rw [heq]
  exact measurable_actualBlockFoldCodeOfInput rewards

/-- Full-block stored-code reconstruction in the original carry's constants.
The code's phantom constant indices are reindexed by keeping all fields. -/
def decodeBlockFoldCodeOfInput (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h)
    (code : BlockFoldCode p rate block C_star C_h) :
    Option (BlockFoldOutput p rate block input.1 rewards input.2.1.C_star input.2.1.C_h 0) :=
  decodeBlockFoldCodeAux 0 (blockLength p block) (by omega) rewards
    (actualCursorZeroInput (⟨input.1, input.2.1, rfl, rfl⟩ :
      BlockInput p rate block input.2.1.C_star input.2.1.C_h))
    ⟨code.phase, code.followers, code.rounds⟩

/-- Exact restoration of `R.foldBlock` on the original source and incoming
carry, including all records and all final-state proof fields. -/
theorem decodeBlockFoldCodeOfInput_actual (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    decodeBlockFoldCodeOfInput rewards input (actualBlockFoldCodeOfInput rewards input) =
      some (foldBlock p rate block input.1 rewards input.2.1) := by
  rcases input with ⟨source, carry, hstar, hh⟩
  subst C_star
  subst C_h
  unfold decodeBlockFoldCodeOfInput
  rw [blockFoldCode_eta]
  exact decodeBlockFoldCodeAux_actual (by omega) rewards
    (actualCursorZeroInput ⟨source, carry, rfl, rfl⟩)

/-- Final continuation and every heterogeneous follower of the full actual
block, without fixing the source or incoming carry to a single value. -/
theorem actualBlockFoldCodeOfInput_final_states (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    let code := actualBlockFoldCodeOfInput rewards input
    let folded := foldBlock p rate block input.1 rewards input.2.1
    code.phase = continuationCodeOf folded.phase ∧
      ∀ i, code.followers i = ActualInitializationRoundMeasurability.followerCodeOfState
        p rate block (folded.followers i) := by
  rw [← physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput]
  exact ⟨rfl, fun _ => rfl⟩

/-- Whole-block simultaneous actions and complete grid-feedback histories. -/
theorem actualBlockFoldCodeOfInput_actions_feedback (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    let code := actualBlockFoldCodeOfInput rewards input
    let folded := foldBlock p rate block input.1 rewards input.2.1
    code.actions = (PhysicalRoundRecord.actions folded.records).map Sum.inr ∧
      code.feedback = (PhysicalRoundRecord.feedback folded.records).map Sum.inr := by
  have hr := congrArg (fun data => data.2.2) (foldBlock_zero_input_data rewards input)
  dsimp only at hr
  have h := actualBlockFoldCodeAux_actions_feedback (cursor := 0)
    (fuel := blockLength p block) (by omega) rewards
    (actualCursorZeroInput input)
  dsimp only at h ⊢
  rw [← hr] at h
  exact h

/-- Every player's full-block own-entry history, with no dropped ready round. -/
theorem actualBlockFoldCodeOfInput_own_entries (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) (player : Fin p.m) :
    (actualBlockFoldCodeOfInput rewards input).rounds.map
        (fun code => ActualInitializationStepMeasurability.physicalOwnEntryFromActualRoundOutput
          rate block code player) =
      (foldBlock p rate block input.1 rewards input.2.1).records.map
        (fun record => Sum.inr (record.result.actions player, record.result.feedback player)) := by
  have hr := congrArg (fun data => data.2.2) (foldBlock_zero_input_data rewards input)
  dsimp only at hr
  have h := actualBlockFoldCodeAux_own_entries (cursor := 0)
    (fuel := blockLength p block) (by omega) rewards
    (actualCursorZeroInput input) player
  rw [← hr] at h
  exact h

/-- Whole-block full-code list identification, including all one-round
preparation and observation metadata. -/
theorem actualBlockFoldCodeOfInput_rounds_eq_physicalRoundCodes
    (rewards : GridRewardTable p) (input : BlockInput p rate block C_star C_h) :
    (actualBlockFoldCodeOfInput rewards input).rounds =
      physicalRoundCodes C_star C_h (foldBlock p rate block input.1 rewards input.2.1).records
        (foldBlock_records_block input.1 rewards input.2.1) :=
  (congrArg BlockFoldCode.rounds
    (physicalBlockFoldCodeOfInput_eq_actualBlockFoldCodeOfInput rewards input)).symm

/-- Count of decoded full-block records, inherited from `R.foldBlock`. -/
theorem decodeBlockFoldCodeOfInput_record_count (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    (decodeBlockFoldCodeOfInput rewards input (actualBlockFoldCodeOfInput rewards input)).map
        (fun folded => folded.records.length) = some (blockLength p block) := by
  rw [decodeBlockFoldCodeOfInput_actual]
  apply congrArg some
  dsimp only
  have hn := (foldBlock p rate block input.1 rewards input.2.1).record_count
  rw [(foldBlock p rate block input.1 rewards input.2.1).consumed_eq_blockLength] at hn
  omega

/-- Chronology of decoded full-block records, including the shortened final
block. No physical time is constructed after the clipped endpoint. -/
theorem decodeBlockFoldCodeOfInput_chronological (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    (decodeBlockFoldCodeOfInput rewards input (actualBlockFoldCodeOfInput rewards input)).map
        (fun folded => PhysicalRoundRecord.times folded.records) =
      some (blockTimes p block 0 (blockLength p block) (by omega)) := by
  rw [decodeBlockFoldCodeOfInput_actual]
  apply congrArg some
  let folded := foldBlock p rate block input.1 rewards input.2.1
  have hn := folded.record_count
  rw [folded.consumed_eq_blockLength] at hn
  have hlength : folded.records.length = blockLength p block := by omega
  simpa only [hlength] using folded.chronological

/-- Every stored ready round has its full success payload. This statement
keeps the whole list; it does not filter missing or error-tagged entries. -/
theorem actualBlockFoldCodeAux_rounds_success {fuel : ℕ}
    (hbudget : cursor + fuel = blockLength p block) (rewards : GridRewardTable p)
    (input : CursorInput p rate block C_star C_h cursor) :
    ∀ code ∈ (actualBlockFoldCodeAux cursor fuel hbudget rewards input).rounds,
      ∃ successful, code = Sum.inr successful := by
  induction fuel generalizing cursor with
  | zero =>
      rw [actualBlockFoldCodeAux.eq_def]
      intro code hcode
      cases hcode
  | succ fuel ih =>
      have hc : cursor < blockLength p block := by omega
      rw [actualBlockFoldCodeAux.eq_def]
      change ∀ code ∈ (actualCursorOutputCode hc rewards input).1 ::
        (actualBlockFoldCodeAux (cursor + 1) fuel (by omega) rewards
          (cursorSuccessorInput hc rewards input)).rounds, _
      intro code hcode
      rcases List.mem_cons.mp hcode with heq | htail
      · subst code
        exact ⟨_, ActualInitializationStepMeasurability.actualRoundOutputCode_eq_success_onReady
          rate block C_star C_h (readyInputAtCursor hc rewards input)⟩
      · exact ih (by omega) (cursorSuccessorInput hc rewards input) code htail

/-- Whole-block collision-filtered feedback uses the original incoming
source and the original whole reward grid. -/
theorem foldBlock_record_feedback (rewards : GridRewardTable p)
    (input : BlockInput p rate block C_star C_h) :
    ∀ record ∈ (foldBlock p rate block input.1 rewards input.2.1).records, ∀ player,
      record.result.feedback player =
        if FiniteBanditModel.collisionFreeFor record.result.actions player then
          rewards record.time (record.result.actions player) else 0 := by
  have hr := congrArg (fun data => data.2.2) (foldBlock_zero_input_data rewards input)
  dsimp only at hr
  rw [hr]
  exact foldBlockAux_record_feedback (by omega) rewards (actualCursorZeroInput input)

end Bandits.Support.ActualInitializationBlockFoldExact
