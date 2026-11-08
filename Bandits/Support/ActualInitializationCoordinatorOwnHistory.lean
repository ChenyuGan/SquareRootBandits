/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteHistoryRewardReadouts

/-!
# The actual initialization coordinator from its own history

The replay below is the existing bootstrap begin/prepare/observe composition.
It retains the original scalar selecting `J`, every own calendar arm scalar,
and every block target scalar. A launched continuation is absorbing for this
initialization readout. No arm is assigned to a launched continuation.

Sources: `sources/zip4/manuscript/01_introduction.tex:18-36`,
`07_public_setup.tex:55-114`, `appendix_b_communication.tex:94-131`,
`06_interruptions.tex:240-296`, `appendix_a_local_protocol.tex:6-14`, and
`08_main_theorem.tex:163-168`, all relative to the same manuscript directory.
These are internal finite-horizon results, not a regret or local-policy theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapDimensions
open Bandits.Support.BootstrapCoordinatorLocalRound
open Bandits.Support.BootstrapCoordinatorRoundMeasurability
open scoped Classical

namespace Bandits.Support.ActualInitializationCoordinatorOwnHistory

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ActiveFollowerDownAcceptance.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev GridRewardTable := ActualInitializationPhysicalStep.GridRewardTable

/-- Exactly the coordinator's original private coordinates, including the
scalar selecting `J`, rather than just its sampled row index. -/
abbrev OwnCoordinates (p : Parameters) :=
  PrivateSourceStreams.Scalar ×
    ((Fin p.T → PrivateSourceStreams.Scalar) ×
      (Fin (n_boot p) → PrivateSourceStreams.Scalar))

def ownCoordinates {p : Parameters} (source : SourceInput p) : OwnCoordinates p :=
  (source.2.1.2,
    ((fun t => source.2.2.1 (ActiveRoundActions.coordinator p.two_le_m, t)),
      source.2.2.2))

variable {p : Parameters}

theorem ownCoordinates_selectedRow (source : SourceInput p) :
    ActualInitializationPhysicalStep.selectedRowIndex p source =
      PrivateSourceStreams.coordinatorIndex p (ownCoordinates source).1 := rfl

theorem ownCoordinates_round (source : SourceInput p) (t : Fin p.T) :
    BootstrapPhysicalInput.playerRoundScalarAt p source.2
        (ActiveRoundActions.coordinator p.two_le_m) t =
      (ownCoordinates source).2.1 t := rfl

theorem ownCoordinates_target (source : SourceInput p) (block : Fin (n_boot p)) :
    BootstrapPhysicalInput.coordinatorTargetScalarAt p block source.2 =
      (ownCoordinates source).2.2 block := rfl

/-- Begin the next live calendar block if the previous local block has ended.
The unchanged branch consumes no target scalar. This operation is called only
at actual calendar positions; `T` has no successor preparation. -/
def atRound (own : OwnCoordinates p) (t : Fin p.T) (live : PrelaunchBlock p) :
    PrelaunchBlock p :=
  if t ∈ calendarBlock p live.data.block then live
  else beginBlock p (roundBlockIndex p t) live.data.row live.data.ids
    live.data.coordinator live.monitor live.data.C_star live.data.C_h
    (own.2.2 (roundBlockIndex p t))

theorem atRound_mem (own : OwnCoordinates p) (t : Fin p.T) (live : PrelaunchBlock p) :
    t ∈ calendarBlock p (atRound own t live).data.block := by
  unfold atRound
  split
  · assumption
  · exact round_mem_quotient_block p t

theorem atRound_eq (own : OwnCoordinates p) (t : Fin p.T) (live : PrelaunchBlock p)
    (ht : t ∈ calendarBlock p live.data.block) : atRound own t live = live := by
  simp only [atRound, ite_eq_left ht]

/-- Prepare and observe one existing bootstrap round, using separate own
arm randomness and feedback. The first launched continuation stays launched. -/
def replayStep (own : OwnCoordinates p) (t : Fin p.T)
    (phase : Continuation p) (y : Fin (D p + 1)) : Continuation p :=
  match phase with
  | .launched launch => .launched launch
  | .prelaunch live =>
      (observe (prepare p (atRound own t live) t (atRound_mem own t live)
        (own.2.1 t)) y).next

/-- The exact source initial block, zero counters and no-crossing sentinel. -/
def replayInitial (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (C_star C_h : ℝ) : Continuation p :=
  .prelaunch (beginBlock p (ActualInitializationRun.firstBlock p)
    (published.2 (PrivateSourceStreams.coordinatorIndex p own.1)) published.1
    (BootstrapPhysicalBlock.initialState p) (ActualInitializationRun.initialUnlaunchedMonitor p)
    C_star C_h (own.2.2 (ActualInitializationRun.firstBlock p)))

/-- The post-observation continuation after exactly `n` supplied own feedback
values. Each successor reads only the final value of that finite prefix. -/
def replayRaw (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (C_star C_h : ℝ) :
    (n : ℕ) → n ≤ p.T → (Fin n → Fin (D p + 1)) → Continuation p
  | 0, _, _ => replayInitial published own C_star C_h
  | n + 1, hn, feedback => replayStep own ⟨n, by omega⟩
      (replayRaw published own C_star C_h n (by omega)
        (fun j => feedback j.castSucc)) (feedback (Fin.last n))

/-- The existing continuation at the next choice, or the terminal continuation
at `T`. A live new block is begun before its first choice, once only. -/
def atPosition (own : OwnCoordinates p) (n : ℕ) (phase : Continuation p) :
    Continuation p :=
  match phase with
  | .launched launch => .launched launch
  | .prelaunch live =>
      if hn : n < p.T then .prelaunch (atRound own ⟨n, hn⟩ live)
      else .prelaunch live

def initializationReplay (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (C_star C_h : ℝ)
    (n : ℕ) (hn : n ≤ p.T) (feedback : Fin n → Fin (D p + 1)) : Continuation p :=
  atPosition own n (replayRaw published own C_star C_h n hn feedback)

/-- The existing lossless continuation code; continuous rows and constants
stay in the original published/own product carrier. -/
def initializationReplayCode (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (OwnCoordinates p × (Fin n → Fin (D p + 1)))) : ActualInitializationBlockMeasurability.ContinuationCode p :=
  ActualInitializationBlockMeasurability.continuationCodeOf (initializationReplay x.1 x.2.1 C_star C_h n hn x.2.2)

theorem replayStep_launched (own : OwnCoordinates p) (t : Fin p.T)
    (launch : LaunchedBlock p) (y : Fin (D p + 1)) :
    replayStep own t (.launched launch) y = .launched launch := rfl

theorem atPosition_horizon (own : OwnCoordinates p) (phase : Continuation p) :
    atPosition own p.T phase = phase := by
  cases phase <;> simp only [atPosition, lt_self_iff_false, ↓reduceDIte]

variable {rate : RateInput p} {source : SourceInput p} {rewards : GridRewardTable p}

private theorem record_inputs (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    record.result.prepared.coordinatorInput = record.coordinatorBefore ∧
      record.result.prepared.source = source := by
  have hr := (ActualInitializationPhysicalStep.step_succeeds_iff_ready rate record.block record.time
    record.coordinatorBefore record.followersBefore source rewards).mp
      ⟨record.result, record.executed⟩
  have he := record.executed
  simp only [ActualInitializationPhysicalStep.step, ActualInitializationPhysicalStep.prepare, dite_eq_left hr] at he
  have heq := Except.ok.inj he
  exact ⟨(congrArg (fun result => result.prepared.coordinatorInput) heq).symm,
    (congrArg (fun result => result.prepared.source) heq).symm⟩

private theorem record_mem (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    record.time ∈ calendarBlock p record.coordinatorBefore.data.block := by
  have h := record.result.prepared.readiness
  rw [← (record_inputs record).1, ← record.result_time, h.1]
  exact h.2.1

private theorem record_next (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) :
    replayStep (ownCoordinates source) record.time (.prelaunch record.coordinatorBefore)
        (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)) =
      record.result.coordinator.next := by
  rw [ActualInitializationRun.roundResult_next_eq]
  simp only [(record_inputs record).1, record.result_time, replayStep,
    atRound_eq _ _ _ (record_mem record), observe, prepare]

private def recordStep (phase : Continuation p)
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards) : Continuation p :=
  replayStep (ownCoordinates source) record.time phase
    (record.result.feedback (ActiveRoundActions.coordinator p.two_le_m))

/-- Induction predicate on the existing physical records: every next choice
has its original entire before-state. It is proved from the cursor recursion
below, never supplied by a caller of the source reconstruction. -/
private def recordsMatch (phase : Continuation p) :
    List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards) → Prop
  | [] => True
  | record :: tail =>
      atPosition (ownCoordinates source) record.time.val phase =
        .prelaunch record.coordinatorBefore ∧
      recordsMatch (recordStep phase record) tail

private theorem recordsMatch_append (phase : Continuation p)
    (left right : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards)) :
    recordsMatch phase (left ++ right) ↔
      recordsMatch phase left ∧ recordsMatch (left.foldl recordStep phase) right := by
  induction left generalizing phase with
  | nil => simp only [List.nil_append, List.foldl_nil, recordsMatch, true_and]
  | cons head tail ih =>
      simp only [List.cons_append, recordsMatch, List.foldl_cons, ih, and_assoc]

private theorem step_atPosition (own : OwnCoordinates p) (t : Fin p.T)
    (phase : Continuation p) (y : Fin (D p + 1)) :
    replayStep own t (atPosition own t.val phase) y = replayStep own t phase y := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      have hm := atRound_mem own t live
      simp only [atPosition, t.isLt, ↓reduceDIte, replayStep,
        atRound_eq own t _ hm]

private theorem recordsMatch_first_congr
    (a b : Continuation p) (head : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (tail : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (heq : atPosition (ownCoordinates source) head.time.val a =
      atPosition (ownCoordinates source) head.time.val b) :
    (recordsMatch a (head :: tail) ↔ recordsMatch b (head :: tail)) ∧
      (head :: tail).foldl recordStep a = (head :: tail).foldl recordStep b := by
  have hs : recordStep a head = recordStep b head := by
    unfold recordStep
    rw [← step_atPosition, heq, step_atPosition]
  simp only [recordsMatch, List.foldl_cons, heq, hs, iff_self, true_and]

private theorem foldBlockAux_replay {block : Fin (n_boot p)} {C_star C_h : ℝ}
    {cursor fuel : ℕ} (hbudget : cursor + fuel = BootstrapObservedFollower.blockLength p block)
    (input : ActualInitializationCursorMeasurability.CursorInput p rate block C_star C_h cursor) :
    let folded := ActualInitializationRun.foldBlockAux p rate block input.1.1 rewards C_star C_h cursor fuel
      hbudget input.1.2.1 input.1.2.2 input.2
    recordsMatch input.1.2.1 folded.records ∧
      folded.records.foldl recordStep input.1.2.1 = folded.phase := by
  induction fuel generalizing cursor with
  | zero =>
      have hdata := ActualInitializationBlockFoldExact.foldBlockAux_zero_data hbudget rewards input
      have hp := congrArg Prod.fst hdata
      have hr := congrArg (fun data => data.2.2) hdata
      dsimp only at hp hr ⊢
      rw [hp, hr]
      exact ⟨trivial, rfl⟩
  | succ fuel ih =>
      have hc : cursor < BootstrapObservedFollower.blockLength p block := by omega
      let head := ActualInitializationBlockFoldExact.cursorRecord hc rewards input
      let next := ActualInitializationCursorMeasurability.cursorSuccessorInput hc rewards input
      have hdata := ActualInitializationBlockFoldExact.foldBlockAux_succ_data hbudget hc rewards input
      have hp := congrArg Prod.fst hdata
      have hr := congrArg (fun data => data.2.2) hdata
      dsimp only at hp hr ⊢
      rw [hp, hr]
      have hm : atPosition (ownCoordinates input.1.1) head.time.val input.1.2.1 =
          .prelaunch head.coordinatorBefore := by
        rw [← ActualInitializationCursorMeasurability.prelaunchAtCursor_eq hc input]
        change atPosition _ head.time.val (.prelaunch head.coordinatorBefore) = _
        simp only [atPosition, head.time.isLt, ↓reduceDIte,
          atRound_eq _ _ _ (record_mem head)]
      have hs : recordStep input.1.2.1 head = next.1.2.1 := by
        rw [← ActualInitializationCursorMeasurability.prelaunchAtCursor_eq hc input]
        exact record_next head
      have ht := ih (by omega) next
      dsimp only [next, ActualInitializationCursorMeasurability.cursorSuccessorInput] at ht
      constructor
      · change _ ∧ recordsMatch (recordStep input.1.2.1 head) _
        refine ⟨hm, ?_⟩
        rw [hs]
        exact ht.1
      · change List.foldl recordStep (recordStep input.1.2.1 head) _ = _
        rw [hs]
        exact ht.2

private theorem foldBlock_replay (block : Fin (n_boot p))
    (carry : ActualInitializationRun.BlockCarry p rate block) :
    let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
    let started := ActualInitializationRun.beginBlock p rate block source carry
    recordsMatch (.prelaunch started.coordinator) folded.records ∧
      folded.records.foldl recordStep (.prelaunch started.coordinator) = folded.phase := by
  let input : ActualInitializationBlockMeasurability.BlockInput p rate block carry.C_star carry.C_h :=
    (source, ⟨carry, rfl, rfl⟩)
  have hdata := ActualInitializationBlockFoldExact.foldBlock_zero_input_data rewards input
  have hp := congrArg Prod.fst hdata
  have hr := congrArg (fun data => data.2.2) hdata
  dsimp only at hp hr ⊢
  rw [hp, hr]
  exact foldBlockAux_replay (by omega)
    (ActualInitializationBlockFoldMeasurability.actualCursorZeroInput input)

private theorem atPosition_idempotent (own : OwnCoordinates p) (n : ℕ)
    (phase : Continuation p) :
    atPosition own n (atPosition own n phase) = atPosition own n phase := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      by_cases hn : n < p.T
      · simp only [atPosition, hn, ↓reduceDIte,
          atRound_eq _ _ _ (atRound_mem own ⟨n, hn⟩ live)]
      · simp only [atPosition, hn, ↓reduceDIte]

private theorem first_record_time
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (start count : ℕ) (hcount : 0 < count)
    (hchron : (ActualInitializationRun.PhysicalRoundRecord.times records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat start count) :
    ∃ head tail, records = head :: tail ∧ head.time.val = start := by
  cases count with
  | zero => omega
  | succ count =>
      cases records with
      | nil =>
          simp only [ActualInitializationRun.PhysicalRoundRecord.times, List.map_nil,
            ActualInitializationHorizon.consecutiveNat] at hchron
          cases hchron
      | cons head tail =>
          refine ⟨head, tail, rfl, ?_⟩
          exact (List.cons.inj hchron).1

private theorem records_congr_start
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (start count : ℕ) (hcount : 0 < count)
    (hchron : (ActualInitializationRun.PhysicalRoundRecord.times records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat start count)
    (a b : Continuation p) (hnorm : atPosition (ownCoordinates source) start a = b) :
    (recordsMatch a records ↔ recordsMatch b records) ∧
      records.foldl recordStep a = records.foldl recordStep b := by
  obtain ⟨head, tail, rfl, htime⟩ := first_record_time records start count hcount hchron
  apply recordsMatch_first_congr
  rw [htime, ← hnorm, atPosition_idempotent]

private theorem continue_normalizes {block : Fin (n_boot p)} {C_star C_h : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards C_star C_h 0)
    (next : Fin (n_boot p)) (carry : ActualInitializationRun.BlockCarry p rate next)
    (hd : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards C_star C_h folded).disposition =
      .continueNext next carry) :
    atPosition (ownCoordinates source) (BootstrapObservedFollower.blockStart p next)
        folded.phase = .prelaunch (ActualInitializationRun.beginBlock p rate next source carry).coordinator := by
  obtain ⟨hnext, hstar, hh, live, hphase, hc, hm, _⟩ :=
    ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts folded next carry hd
  have ha := folded.invariant.1
  rw [hphase] at ha
  dsimp only [ActualInitializationRun.continuationAligned,
    ActualInitializationRun.continuationData] at ha
  have ht : BootstrapObservedFollower.blockStart p next < p.T :=
    lt_of_lt_of_le (BootstrapObservedFollower.blockStart_lt_blockStop p next)
      (Nat.min_le_left _ _)
  let t : Fin p.T := ⟨BootstrapObservedFollower.blockStart p next, ht⟩
  have hi : roundBlockIndex p t = next := by
    apply Fin.ext
    change (next.val * B_boot p) / B_boot p = next.val
    exact Nat.mul_div_cancel _ (B_boot_pos p)
  have hstop : BootstrapObservedFollower.blockStop p block = t.val := by
    change min p.T ((block.val + 1) * B_boot p) = next.val * B_boot p
    rw [← hnext]
    exact Nat.min_eq_right ht.le
  have hnot : t ∉ calendarBlock p live.data.block := by
    rw [ha.1, mem_calendarBlock_iff]
    intro h
    have hu := h.2
    change t.val < BootstrapObservedFollower.blockStop p block at hu
    omega
  rw [hphase]
  simp only [atPosition, ht, ↓reduceDIte]
  change Continuation.prelaunch
    (atRound (ownCoordinates source) t live) = _
  rw [atRound, ite_eq_right hnot, hi]
  change Continuation.prelaunch
      (beginBlock p next live.data.row live.data.ids live.data.coordinator live.monitor
        live.data.C_star live.data.C_h ((ownCoordinates source).2.2 next)) =
    .prelaunch (beginBlock p next (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) source.1.1
      carry.coordinator carry.monitor carry.C_star carry.C_h
      (BootstrapPhysicalInput.coordinatorTargetScalarAt p next source.2))
  rw [ha.2.1, ha.2.2.1, ha.2.2.2.2.1, ha.2.2.2.2.2, hc, hm, hstar, hh]
  rfl

private theorem runFrom_replay (fuel : ℕ) (block : Fin (n_boot p))
    (hmeasure : n_boot p - block.val = fuel) (carry : ActualInitializationRun.BlockCarry p rate block) :
    let run := ActualInitializationHorizon.runFrom p rate source rewards block carry
    let before := Continuation.prelaunch (ActualInitializationRun.beginBlock p rate block source carry).coordinator
    recordsMatch before run.records ∧ run.records.foldl recordStep before = run.terminalFold.phase := by
  induction fuel generalizing block with
  | zero => have hb := block.isLt; omega
  | succ fuel ih =>
      let folded := ActualInitializationRun.foldBlock p rate block source rewards carry
      let handoff := ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards
        carry.C_star carry.C_h folded
      have hfold := foldBlock_replay (source := source) (rewards := rewards) block carry
      cases hd : handoff.disposition with
      | continueNext next nextCarry =>
          have hf := ActualInitializationHorizon.combinedBoundaryHandoff_continueNext_facts folded next nextCarry hd
          have hm : n_boot p - next.val = fuel := by omega
          have ht := ih next hm nextCarry
          let tail := ActualInitializationHorizon.runFrom p rate source rewards next nextCarry
          have hidx : next.val ≤ tail.terminalBlock.val := by
            rw [tail.terminalBlock_index]
            omega
          have hstart : BootstrapObservedFollower.blockStart p next ≤
              BootstrapObservedFollower.blockStart p tail.terminalBlock :=
            Nat.mul_le_mul_right (B_boot p) hidx
          have hpositive : 0 < BootstrapObservedFollower.blockStop p tail.terminalBlock -
              BootstrapObservedFollower.blockStart p next := by
            have hend := BootstrapObservedFollower.blockStart_lt_blockStop p tail.terminalBlock
            omega
          have hswitch := records_congr_start tail.records _ _ hpositive tail.chronological
            folded.phase (.prelaunch (ActualInitializationRun.beginBlock p rate next source nextCarry).coordinator)
            (continue_normalizes folded next nextCarry hd)
          have hdata := ActualInitializationHorizonObservation.runData_continue (source := source) carry next
            nextCarry hd
          have hr := congrArg (fun data => data.2.1) hdata
          have hp := congrArg (fun data => data.1.2.2.2.1.phase) hdata
          dsimp only [ActualInitializationHorizonObservation.runData,
            ActualInitializationHorizonObservation.terminalData] at hr hp ⊢
          rw [hr, hp, recordsMatch_append, List.foldl_append, hfold.2]
          exact ⟨⟨hfold.1, hswitch.1.mpr ht.1⟩, hswitch.2.trans ht.2⟩
      | launched launch seed =>
          have hdata := ActualInitializationHorizonObservation.runData_stop (source := source) carry (by
            intro next nextCarry he
            rw [show handoff.disposition = _ from hd] at he
            cases he)
          have hr := congrArg (fun data => data.2.1) hdata
          have hp := congrArg (fun data => data.1.2.2.2.1.phase) hdata
          dsimp only [ActualInitializationHorizonObservation.runData,
            ActualInitializationHorizonObservation.terminalData] at hr hp ⊢
          rw [hr, hp]
          exact hfold
      | exhausted live =>
          have hdata := ActualInitializationHorizonObservation.runData_stop (source := source) carry (by
            intro next nextCarry he
            rw [show handoff.disposition = _ from hd] at he
            cases he)
          have hr := congrArg (fun data => data.2.1) hdata
          have hp := congrArg (fun data => data.1.2.2.2.1.phase) hdata
          dsimp only [ActualInitializationHorizonObservation.runData,
            ActualInitializationHorizonObservation.terminalData] at hr hp ⊢
          rw [hr, hp]
          exact hfold

private theorem consecutiveNat_get (start count i : ℕ) (hi : i < count) :
    (ActualInitializationHorizon.consecutiveNat start count)[i]'(by
      rw [ActualInitializationHorizon.consecutiveNat_length]
      exact hi) = start + i := by
  induction count generalizing start i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (ActualInitializationHorizon.consecutiveNat (start + 1) count)[i]'(by
            rw [ActualInitializationHorizon.consecutiveNat_length]; omega) = start + (i + 1)
          rw [ih (start + 1) i (by omega)]
          omega

private theorem chronological_time
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hchron : (ActualInitializationRun.PhysicalRoundRecord.times records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat 0 records.length) (i : ℕ) (hi : i < records.length) :
    records[i].time.val = i := by
  have he := congrArg (fun values : List ℕ => values[i]?) hchron
  have hl : i < (ActualInitializationHorizon.consecutiveNat 0 records.length).length := by
    rw [ActualInitializationHorizon.consecutiveNat_length]; exact hi
  simpa only [ActualInitializationRun.PhysicalRoundRecord.times, List.getElem?_map,
    List.getElem?_eq_getElem hi, Option.map_some, List.getElem?_eq_getElem hl,
    consecutiveNat_get 0 records.length i hi, Nat.zero_add, Option.some.injEq] using he

private theorem replayRaw_eq_records
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hchron : (ActualInitializationRun.PhysicalRoundRecord.times records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat 0 records.length)
    (C_star C_h : ℝ) (n : ℕ) (hn : n ≤ p.T) (hlen : n ≤ records.length)
    (feedback : Fin n → Fin (D p + 1))
    (hfeedback : ∀ j : Fin n, feedback j =
      (records[j.val]'(lt_of_lt_of_le j.isLt hlen)).result.feedback
        (ActiveRoundActions.coordinator p.two_le_m)) :
    replayRaw source.1 (ownCoordinates source) C_star C_h n hn feedback =
      (records.take n).foldl recordStep (replayInitial source.1 (ownCoordinates source) C_star C_h) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hi : n < records.length := by omega
      have ht : records[n].time = (⟨n, by omega⟩ : Fin p.T) :=
        Fin.ext (chronological_time records hchron n hi)
      rw [replayRaw, ih (by omega) (by omega)
        (fun j => feedback j.castSucc) (fun j => hfeedback j.castSucc),
        hfeedback (Fin.last n), ← ht,
        List.take_succ_eq_append_getElem hi, List.foldl_append]
      rfl

private theorem recordsMatch_at_index (phase : Continuation p)
    (records : List (ActualInitializationRun.PhysicalRoundRecord p rate source rewards))
    (hmatch : recordsMatch phase records) (i : ℕ) (hi : i < records.length) :
    atPosition (ownCoordinates source) records[i].time.val
        ((records.take i).foldl recordStep phase) = .prelaunch records[i].coordinatorBefore := by
  induction records generalizing phase i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons head tail ih =>
      cases i with
      | zero => exact hmatch.1
      | succ i =>
          exact ih (recordStep phase head) hmatch.2 i (by simpa using hi)

variable (rate) (source) (rewards) (C_star C_h : ℝ)

private theorem source_feedback_length :
    (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
      (ActiveRoundActions.coordinator p.two_le_m)).length = p.T := by
  simpa only [ActualCompletePhysicalHistory.playerGridFeedbackHistory, List.length_map] using
    (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_lengths p rate source rewards C_star C_h).2.2

/-- Exactly the strict own grid-feedback prefix `Y_n`, on `Fin n`. Its list
form is proved equal to H's `take n` below. No other observation is retained. -/
def sourceOwnFeedbackPrefix (n : ℕ) (hn : n ≤ p.T) : Fin n → Fin (D p + 1) :=
  fun j => (ActualCompletePhysicalHistory.playerGridFeedbackHistory
    (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
    (ActiveRoundActions.coordinator p.two_le_m))[j.val]'(by
      rw [source_feedback_length]; exact lt_of_lt_of_le j.isLt hn)

theorem sourceOwnFeedbackPrefix_list (n : ℕ) (hn : n ≤ p.T) :
    List.ofFn (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn) =
      (ActualCompletePhysicalHistory.playerGridFeedbackHistory
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
        (ActiveRoundActions.coordinator p.two_le_m)).take n := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_take, source_feedback_length,
      Nat.min_eq_left hn]
  · intro i hi hj
    simp only [List.getElem_ofFn, sourceOwnFeedbackPrefix, List.getElem_take]

private theorem source_records_chronological :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    (ActualInitializationRun.PhysicalRoundRecord.times run.records).map Fin.val =
      ActualInitializationHorizon.consecutiveNat 0 run.records.length := by
  dsimp only
  rw [ActualCompletePhysicalHistory.initializationRun_record_count]
  exact ActualInitializationHorizon.sourceInitializedRun_chronological p rate source rewards C_star C_h

theorem sourceInitializationRecordCount_le :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.length ≤ p.T := by
  rw [ActualCompletePhysicalHistory.initializationRun_record_count]
  exact Nat.min_le_left _ _

private theorem source_prefix_feedback (n : ℕ) (hn : n ≤ p.T)
    (hlen : n ≤ (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.length)
    (j : Fin n) :
    sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn j =
      ((ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records[j.val]'
        (lt_of_lt_of_le j.isLt hlen)).result.feedback
          (ActiveRoundActions.coordinator p.two_le_m) := by
  let history := ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
    p rate source rewards C_star C_h
  have hlist := ActualCompletePhysicalHistory.playerGridFeedbackHistory_projection
    p rate source rewards C_star C_h history (ActiveRoundActions.coordinator p.two_le_m)
  simp only [ActualInitializationRun.PhysicalRoundRecord.feedback,
    ActualCompletePhysicalHistory.initializationRecords, List.map_map, Function.comp_def] at hlist
  have hj : j.val < (ActualInitializationHorizon.sourceInitializedRun
      p rate source rewards C_star C_h).records.length := lt_of_lt_of_le j.isLt hlen
  have hfull : j.val < (ActualCompletePhysicalHistory.playerGridFeedbackHistory history
      (ActiveRoundActions.coordinator p.two_le_m)).length := by
    rw [source_feedback_length]; exact lt_of_lt_of_le j.isLt hn
  have he := congrArg (fun values : List (Fin (D p + 1)) => values[j.val]?) hlist
  rw [List.getElem?_append_left
    (l₁ := (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.map
      (fun record => record.result.feedback (ActiveRoundActions.coordinator p.two_le_m)))
    (by simpa only [List.length_map] using hj)] at he
  simp only [List.getElem?_eq_getElem hfull, List.getElem?_map,
    List.getElem?_eq_getElem hj, Option.map_some] at he
  exact Option.some.inj he

private theorem source_run_replay :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    let initial := replayInitial source.1 (ownCoordinates source) C_star C_h
    recordsMatch initial run.records ∧ run.records.foldl recordStep initial = run.terminalFold.phase := by
  exact runFrom_replay (n_boot p) (ActualInitializationRun.firstBlock p) (by simp [ActualInitializationRun.firstBlock])
    (ActualInitializationRun.initialCarry p rate C_star C_h)

/-- Single-source reconstruction of the entire existing before-state at every
actual initialization record. The sole record premise is membership in H's
generated initialization prefix, not a supplied trace or state equality. -/
theorem sourceInitialized_initialization_coordinator_replay
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hrecord : record ∈ ActualCompletePhysicalHistory.initializationRecords
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)) :
    initializationReplay source.1 (ownCoordinates source) C_star C_h record.time.val
        record.time.isLt.le
        (sourceOwnFeedbackPrefix rate source rewards C_star C_h record.time.val record.time.isLt.le) =
      .prelaunch record.coordinatorBefore := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  change record ∈ run.records at hrecord
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hrecord
  change run.records[i] = record at he
  have ht : record.time.val = i := by
    rw [← he]
    exact chronological_time run.records (source_records_chronological rate source rewards C_star C_h) i hi
  have hlen : record.time.val ≤ run.records.length := by omega
  unfold initializationReplay
  rw [replayRaw_eq_records run.records
    (source_records_chronological rate source rewards C_star C_h) C_star C_h _ _ hlen _
    (source_prefix_feedback rate source rewards C_star C_h _ _ hlen)]
  rw [ht]
  simpa only [he, ht] using recordsMatch_at_index _ run.records
    (source_run_replay rate source rewards C_star C_h).1 i hi

/-- Source initial monitor and block reset, with the same constants, row and
target scalar as the actual initial carry. -/
theorem replayInitial_eq_actual :
    replayInitial source.1 (ownCoordinates source) C_star C_h =
      .prelaunch (ActualInitializationRun.beginBlock p rate (ActualInitializationRun.firstBlock p) source
        (ActualInitializationRun.initialCarry p rate C_star C_h)).coordinator := rfl

private theorem source_replayRaw_endpoint :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    replayRaw source.1 (ownCoordinates source) C_star C_h run.records.length
        (sourceInitializationRecordCount_le rate source rewards C_star C_h)
        (sourceOwnFeedbackPrefix rate source rewards C_star C_h run.records.length
          (sourceInitializationRecordCount_le rate source rewards C_star C_h)) = run.terminalFold.phase := by
  dsimp only
  rw [replayRaw_eq_records _ (source_records_chronological rate source rewards C_star C_h)
    C_star C_h _ _ le_rfl _ (source_prefix_feedback rate source rewards C_star C_h _ _ le_rfl),
    List.take_length]
  exact (source_run_replay rate source rewards C_star C_h).2

private theorem phase_of_launched_handoff {block : Fin (n_boot p)} {a b : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards a b 0)
    (launch : LaunchedBlock p) (seed : ActualInitializationRun.CoordinatorLearnerZeroSeed p)
    (hd : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards a b folded).disposition =
      .launched launch seed) : folded.phase = .launched launch := by
  rcases folded with ⟨consumed, phase, followers, records, invariant,
    consumed_eq, record_count, chronological⟩
  cases phase with
  | launched active =>
      dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hd
      cases hd
      rfl
  | prelaunch live =>
      dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hd
      by_cases hl : block.val + 1 = n_boot p
      · rw [dite_eq_left hl] at hd; cases hd
      · rw [dite_eq_right hl] at hd; cases hd

private theorem phase_of_exhausted_handoff {block : Fin (n_boot p)} {a b : ℝ}
    (folded : ActualInitializationRun.BlockFoldOutput p rate block source rewards a b 0)
    (live : PrelaunchBlock p)
    (hd : (ActualInitializationRun.combinedBoundaryHandoff p rate block source rewards a b folded).disposition =
      .exhausted live) : folded.phase = .prelaunch live := by
  rcases folded with ⟨consumed, phase, followers, records, invariant,
    consumed_eq, record_count, chronological⟩
  cases phase with
  | launched active =>
      dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hd
      cases hd
  | prelaunch before =>
      dsimp [ActualInitializationRun.combinedBoundaryHandoff, id] at hd
      by_cases hl : block.val + 1 = n_boot p
      · rw [dite_eq_left hl] at hd
        cases hd
        rfl
      · rw [dite_eq_right hl] at hd; cases hd

private theorem terminal_prelaunch_horizon (live : PrelaunchBlock p)
    (hp : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalFold.phase =
      .prelaunch live) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.length = p.T := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  cases hd : run.terminalDisposition with
  | continueNext next carry =>
      exact (ActualCompletePhysicalHistory.sourceRun_not_continueNext p rate source rewards C_star C_h
        run next carry hd).elim
  | launched launch seed =>
      have hh : (ActualInitializationRun.combinedBoundaryHandoff p rate run.terminalBlock source rewards
          run.terminalC_star run.terminalC_h run.terminalFold).disposition = .launched launch seed := by
        rw [← run.terminalHandoff_eq, ← run.terminalDisposition_eq]; exact hd
      have hf := phase_of_launched_handoff rate source rewards run.terminalFold launch seed hh
      rw [hp] at hf
      cases hf
  | exhausted before =>
      have he := ActualInitializationHorizon.sourceInitializedRun_exhaustion_reaches_horizon p rate source
        rewards C_star C_h before hd
      exact (ActualCompletePhysicalHistory.initializationRun_record_count p rate source rewards C_star C_h).trans he.1

/-- At the actual initialization endpoint the local replay is the actual
terminal continuation. A final-boundary launch is retained, and exhaustion
does not prepare another block at `T`. -/
theorem sourceInitialized_initializationReplay_endpoint :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    initializationReplay source.1 (ownCoordinates source) C_star C_h run.records.length
        (sourceInitializationRecordCount_le rate source rewards C_star C_h)
        (sourceOwnFeedbackPrefix rate source rewards C_star C_h run.records.length
          (sourceInitializationRecordCount_le rate source rewards C_star C_h)) = run.terminalFold.phase := by
  dsimp only
  rw [initializationReplay, source_replayRaw_endpoint]
  cases hp : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalFold.phase with
  | launched launch => rfl
  | prelaunch live =>
      rw [terminal_prelaunch_horizon rate source rewards C_star C_h live hp, atPosition_horizon]

private theorem source_raw_launched_persistent (n : ℕ) (hn : n ≤ p.T)
    (launch : LaunchedBlock p)
    (hbase : replayRaw source.1 (ownCoordinates source) C_star C_h n hn
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn) = .launched launch)
    (k : ℕ) (hnk : n ≤ k) (hk : k ≤ p.T) :
    replayRaw source.1 (ownCoordinates source) C_star C_h k hk
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h k hk) = .launched launch := by
  induction k, hnk using Nat.le_induction with
  | base => exact hbase
  | succ k hnk ih =>
      have hkprev : k ≤ p.T := by omega
      change replayStep (ownCoordinates source) ⟨k, by omega⟩
        (replayRaw source.1 (ownCoordinates source) C_star C_h k hkprev
          (sourceOwnFeedbackPrefix rate source rewards C_star C_h k hkprev)) _ = _
      rw [ih (by omega)]
      rfl

theorem sourceInitialized_initializationReplay_of_ge_prefix
    (n : ℕ) (hn : n ≤ p.T)
    (hprefix : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.length ≤ n) :
    initializationReplay source.1 (ownCoordinates source) C_star C_h n hn
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn) =
        (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalFold.phase := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  cases hp : run.terminalFold.phase with
  | launched launch =>
      have hbase := (source_replayRaw_endpoint rate source rewards C_star C_h).trans hp
      rw [initializationReplay, source_raw_launched_persistent rate source rewards C_star C_h
        run.records.length (sourceInitializationRecordCount_le rate source rewards C_star C_h) launch hbase n
          hprefix hn]
      rfl
  | prelaunch live =>
      have hlen := terminal_prelaunch_horizon rate source rewards C_star C_h live hp
      change run.records.length = p.T at hlen
      change run.records.length ≤ n at hprefix
      have he : n = run.records.length := by omega
      subst n
      exact (sourceInitialized_initializationReplay_endpoint rate source rewards C_star C_h).trans hp

private theorem source_prefix_count :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).records.length =
      ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h) :=
  (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory_component_counts p rate source rewards
    C_star C_h
    (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)).1

/-- Before `T`, surviving initialization is determined by strict own past.
This says nothing about a future launch beyond an unlaunched prefix. -/
theorem sourceInitialized_initializationReplay_prelaunch_iff
    (n : ℕ) (hn : n < p.T) :
    (∃ live, initializationReplay source.1 (ownCoordinates source) C_star C_h n hn.le
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn.le) = .prelaunch live) ↔
    n < ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h) := by
  rw [← source_prefix_count rate source rewards C_star C_h]
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  constructor
  · rintro ⟨live, hlive⟩
    by_contra hnot
    have he := sourceInitialized_initializationReplay_of_ge_prefix rate source rewards C_star C_h
      n hn.le (by omega)
    have hp : run.terminalFold.phase = .prelaunch live := he.symm.trans hlive
    have hlen := terminal_prelaunch_horizon rate source rewards C_star C_h live hp
    omega
  · intro hlt
    have ht := chronological_time run.records
      (source_records_chronological rate source rewards C_star C_h) n hlt
    have he := recordsMatch_at_index _ run.records
      (source_run_replay rate source rewards C_star C_h).1 n hlt
    rw [ht] at he
    refine ⟨run.records[n].coordinatorBefore, ?_⟩
    unfold initializationReplay
    rw [replayRaw_eq_records run.records
      (source_records_chronological rate source rewards C_star C_h) C_star C_h n hn.le
      hlt.le _ (source_prefix_feedback rate source rewards C_star C_h n hn.le hlt.le)]
    exact he

/-- A launch already present in the finite replay is the actual terminal
launch, including the entire saved monitor, trigger and local data. -/
theorem sourceInitialized_initializationReplay_launched
    (n : ℕ) (hn : n ≤ p.T) (launch : LaunchedBlock p)
    (hlaunch : initializationReplay source.1 (ownCoordinates source) C_star C_h n hn
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn) = .launched launch) :
    (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalFold.phase =
      .launched launch := by
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  by_cases hlt : n < run.records.length
  · have hnT : n < p.T := lt_of_lt_of_le hlt (sourceInitializationRecordCount_le rate source rewards C_star C_h)
    obtain ⟨live, he⟩ := (sourceInitialized_initializationReplay_prelaunch_iff rate source rewards C_star C_h n hnT).mpr
      (by rwa [← source_prefix_count rate source rewards C_star C_h])
    rw [hlaunch] at he
    cases he
  · have hge : run.records.length ≤ n := Nat.le_of_not_gt hlt
    exact (sourceInitialized_initializationReplay_of_ge_prefix rate source rewards C_star C_h
      n hn hge).symm.trans hlaunch

private def phaseBase (phase : Continuation p) : CoordinatorContinuousBase p :=
  (((ActualInitializationRun.continuationData p phase).row, (ActualInitializationRun.continuationData p phase).ids),
    ((ActualInitializationRun.continuationData p phase).C_star, (ActualInitializationRun.continuationData p phase).C_h))

private theorem atRound_base (own : OwnCoordinates p) (t : Fin p.T) (live : PrelaunchBlock p) :
    (prelaunchCoordinates p (atRound own t live)).1 = (prelaunchCoordinates p live).1 := by
  unfold atRound
  split <;> rfl

private theorem replayStep_base (own : OwnCoordinates p) (t : Fin p.T)
    (phase : Continuation p) (y : Fin (D p + 1)) :
    phaseBase (replayStep own t phase y) = phaseBase phase := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      unfold replayStep observe prepare phaseBase
      rw [ActualInitializationRun.continuationAfterObservation_data]
      exact atRound_base own t live

private theorem atPosition_base (own : OwnCoordinates p) (n : ℕ) (phase : Continuation p) :
    phaseBase (atPosition own n phase) = phaseBase phase := by
  cases phase with
  | launched launch => rfl
  | prelaunch live =>
      by_cases hn : n < p.T
      · simp only [atPosition, hn, ↓reduceDIte]
        change (prelaunchCoordinates p (atRound own ⟨n, hn⟩ live)).1 = _
        exact atRound_base own ⟨n, hn⟩ live
      · simp only [atPosition, hn, ↓reduceDIte]

private theorem replayRaw_base (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (n : ℕ) (hn : n ≤ p.T)
    (feedback : Fin n → Fin (D p + 1)) :
    phaseBase (replayRaw published own a b n hn feedback) =
      ((published.2 (PrivateSourceStreams.coordinatorIndex p own.1), published.1), (a, b)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [replayRaw, replayStep_base, ih]

private def liveOf (phase : Continuation p)
    (hpre : (ActualInitializationBlockMeasurability.continuationCodeOf phase).2.2.2.2 = none) : PrelaunchBlock p :=
  match he : phase with
  | .prelaunch live => live
  | .launched launch => False.elim (by
      cases hpre)

private theorem liveOf_eq (phase : Continuation p)
    (hpre : (ActualInitializationBlockMeasurability.continuationCodeOf phase).2.2.2.2 = none) :
    Continuation.prelaunch (liveOf phase hpre) = phase := by
  cases phase with
  | prelaunch live => rfl
  | launched launch => cases hpre

private theorem measurable_liveOf {α : Type*} [MeasurableSpace α]
    (phase : α → Continuation p)
    (hpre : ∀ x, (ActualInitializationBlockMeasurability.continuationCodeOf (phase x)).2.2.2.2 = none)
    (hbase : Measurable (fun x => phaseBase (phase x)))
    (hcode : Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (phase x))) :
    Measurable (fun x => liveOf (phase x) (hpre x)) := by
  let live := fun x => liveOf (phase x) (hpre x)
  have hlocal : Measurable (fun x => (prelaunchCoordinates p (live x)).2) := by
    apply FollowerDownJointMeasurability.measurable_of_countable_read_factorization
      (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (phase x)) hcode
    intro x y he
    rw [← liveOf_eq (phase x) (hpre x), ← liveOf_eq (phase y) (hpre y)] at he
    have hb := congrArg Prod.fst he
    have ht := congrArg (fun c => c.2.1) he
    have hc := congrArg (fun c => c.2.2.1) he
    have hm := congrArg (fun c => c.2.2.2.1) he
    exact coordinatorLocalCodeFields_injective p
      (Prod.ext hb (Prod.ext ht (Prod.ext hc (Subtype.ext hm))))
  apply measurable_comap_iff.mpr
  have hbeq : (fun x => (prelaunchCoordinates p (live x)).1) =
      (fun x => phaseBase (phase x)) := by
    funext x
    rw [← liveOf_eq (phase x) (hpre x)]
    rfl
  exact (hbeq ▸ hbase).prodMk hlocal

private theorem measurable_begin {α : Type*} [MeasurableSpace α]
    (live : α → PrelaunchBlock p) (hlive : Measurable live)
    (block : Fin (n_boot p)) (target : α → PrivateSourceStreams.Scalar)
    (htarget : Measurable target) :
    Measurable (fun x => beginBlock p block (live x).data.row (live x).data.ids
      (live x).data.coordinator (live x).monitor (live x).data.C_star (live x).data.C_h (target x)) := by
  let inputs := fun x => ({
    base := (prelaunchCoordinates p (live x)).1
    block := block
    carried := (prelaunchCoordinates p (live x)).2.coordinator
    monitor := (prelaunchCoordinates p (live x)).2.monitor
    targetScalar := target x } : CoordinatorBeginBlockInput p)
  have hc := (measurable_prelaunchCoordinates p).comp hlive
  have hb := measurable_fst.comp hc
  have hl := measurable_snd.comp hc
  have hi : Measurable inputs := by
    apply measurable_comap_iff.mpr
    exact hb.prodMk (measurable_const.prodMk
      (((measurable_of_countable fun c : CoordinatorLocalCode p => c.coordinator).comp hl).prodMk
        (((measurable_of_countable fun c : CoordinatorLocalCode p => c.monitor).comp hl).prodMk htarget)))
  apply measurable_comap_iff.mpr
  convert (measurable_coordinatorBeginBlockCode p).comp hi using 1
  funext x
  dsimp only [Function.comp_def]
  simp only [coordinatorBeginBlockCode, inputs, prelaunchCoordinates, beginBlock]
  rw [show resetCoordinatorBlockState p (live x).data.coordinator =
    BootstrapPhysicalBlock.initialState p from
      beginBlock_resets_list_mode_and_audit p block (live x).data.row (live x).data.ids
        (live x).data.coordinator (live x).monitor (live x).data.C_star (live x).data.C_h (target x)]

private theorem measurable_atRound {α : Type*} [MeasurableSpace α]
    (own : α → OwnCoordinates p) (hown : Measurable own) (t : Fin p.T)
    (live : α → PrelaunchBlock p) (hlive : Measurable live) :
    Measurable (fun x => atRound (own x) t (live x)) := by
  have hl := (measurable_prelaunchLocalCode p).comp hlive
  have hb : Measurable (fun x => (live x).data.block) :=
    (measurable_of_countable fun c : CoordinatorLocalCode p => c.block).comp hl
  have hs : MeasurableSet {x | t ∈ calendarBlock p (live x).data.block} :=
    hb (Set.to_countable {block : Fin (n_boot p) | t ∈ calendarBlock p block}).measurableSet
  exact Measurable.ite hs hlive (measurable_begin live hlive (roundBlockIndex p t)
    (fun x => (own x).2.2 (roundBlockIndex p t))
    ((measurable_pi_apply _).comp (measurable_snd.comp (measurable_snd.comp hown))))

private theorem decoded_observeCode_phase (a b : ℝ)
    (input : CoordinatorFixedRoundInput p a b) (code : CoordinatorObservationCode p)
    (observed : ObservationResult p)
    (h : reconstructCoordinatorObservationCode p a b input code = some observed) :
    ActualInitializationBlockMeasurability.continuationCodeOf observed.next =
      (code.block, (code.target, (code.coordinator, (code.monitor, code.trigger)))) := by
  unfold reconstructCoordinatorObservationCode at h
  split_ifs at h <;> cases h <;>
    simp_all [ActualInitializationBlockMeasurability.continuationCodeOf,
      ActualInitializationRun.continuationData, Continuation.coordinatorState,
      Continuation.monitorState, coordinatorObservationDataOfCode, coordinatorStateCode,
      coordinatorStateOfCode, monitorCode, monitorStateOfCode]
  all_goals
    apply monitorCodeFields_injective p
    simp_all

private theorem observeCode_phase (a b : ℝ) (input : CoordinatorObserveInput p a b) :
    ActualInitializationBlockMeasurability.continuationCodeOf (coordinatorObserveResult p a b input).next =
      let code := coordinatorObserveCode p a b input
      (code.block, (code.target, (code.coordinator, (code.monitor, code.trigger)))) :=
  decoded_observeCode_phase a b input.fixed (coordinatorObserveCode p a b input)
    (coordinatorObserveResult p a b input) (reconstruct_coordinatorObserveCode p a b input)

private theorem prepare_coordinates (before : PrelaunchBlock p) (t : Fin p.T)
    (ht : t ∈ calendarBlock p before.data.block) (v : PrivateSourceStreams.Scalar) :
    coordinatorPreparedRound p
      ⟨(prelaunchCoordinates p before).1, (prelaunchCoordinates p before).2, t, ht⟩ v =
        prepare p before t ht v := by
  rcases before with ⟨⟨block, row, ids, target, state, a, b⟩, ⟨monitor, hmonitor⟩⟩
  cases state
  cases monitor
  rfl

private theorem measurable_stepCode {α : Type*} [MeasurableSpace α]
    (a b : ℝ) (own : α → OwnCoordinates p) (hown : Measurable own)
    (t : Fin p.T) (phase : α → Continuation p)
    (hbase : Measurable (fun x => phaseBase (phase x)))
    (hcode : Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (phase x)))
    (hconstants : ∀ x, (phaseBase (phase x)).2 = (a, b))
    (feedback : α → Fin (D p + 1)) (hfeedback : Measurable feedback) :
    Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (replayStep (own x) t (phase
      x) (feedback x))) := by
  let s : Set α := {x | (ActualInitializationBlockMeasurability.continuationCodeOf (phase x)).2.2.2.2 = none}
  have hs : MeasurableSet s := measurableSet_eq_fun
    ((measurable_of_countable fun c : ActualInitializationBlockMeasurability.ContinuationCode p =>
      c.2.2.2.2).comp hcode) measurable_const
  apply measurable_of_restrict_of_restrict_compl hs
  · let live := fun x : s => liveOf (phase x.val) x.property
    have hlive : Measurable live := measurable_liveOf (fun x : s => phase x.val)
      (fun x => x.property) (hbase.comp measurable_subtype_coe) (hcode.comp measurable_subtype_coe)
    let before := fun x : s => atRound (own x.val) t (live x)
    have hbefore : Measurable before := measurable_atRound (fun x : s => own x.val)
      (hown.comp measurable_subtype_coe) t live hlive
    have hc := (measurable_prelaunchCoordinates p).comp hbefore
    have hconst : ∀ x : s, (prelaunchCoordinates p (before x)).1.2 = (a, b) := by
      intro x
      rw [atRound_base]
      have hh := hconstants x.val
      rw [← liveOf_eq (phase x.val) x.property] at hh
      exact hh
    let inputs := fun x : s => ({
      fixed := ⟨⟨(prelaunchCoordinates p (before x)).1,
        (prelaunchCoordinates p (before x)).2, t, atRound_mem _ _ _⟩, hconst x⟩
      ownArmScalar := (own x.val).2.1 t
      feedback := feedback x.val } : CoordinatorObserveInput p a b)
    have hround : Measurable (fun x : s => (inputs x).fixed.input) := by
      apply measurable_comap_iff.mpr
      exact (measurable_fst.comp hc).prodMk ((measurable_snd.comp hc).prodMk measurable_const)
    have hfixed : Measurable (fun x : s => (inputs x).fixed) :=
      measurable_comap_iff.mpr hround
    have hi : Measurable inputs := by
      apply measurable_comap_iff.mpr
      exact hfixed.prodMk
        (((measurable_pi_apply t).comp (measurable_fst.comp
          (measurable_snd.comp (hown.comp measurable_subtype_coe)))).prodMk
            (hfeedback.comp measurable_subtype_coe))
    have hout := measurable_snd.comp
      ((comap_measurable (coordinatorObservationCodeFields p)).comp
        ((measurable_coordinatorObserveCode p a b).comp hi))
    have heq : (fun x : s => ActualInitializationBlockMeasurability.continuationCodeOf
        (replayStep (own x.val) t (phase x.val) (feedback x.val))) =
        (fun x : s => (coordinatorObservationCodeFields p
          (coordinatorObserveCode p a b (inputs x))).2) := by
      funext x
      dsimp only [coordinatorObservationCodeFields]
      rw [← observeCode_phase a b (inputs x)]
      rw [← liveOf_eq (phase x.val) x.property]
      change ActualInitializationBlockMeasurability.continuationCodeOf (observe (prepare p (before x) t _ _ ) _).next =
        ActualInitializationBlockMeasurability.continuationCodeOf (coordinatorObserveResult p a b (inputs x)).next
      unfold coordinatorObserveResult
      dsimp only [inputs]
      rw [prepare_coordinates]
    change Measurable (fun x : s => ActualInitializationBlockMeasurability.continuationCodeOf
      (replayStep (own x.val) t (phase x.val) (feedback x.val)))
    rw [heq]
    exact hout
  · have heq : (fun x : (sᶜ : Set α) => ActualInitializationBlockMeasurability.continuationCodeOf
        (replayStep (own x.val) t (phase x.val) (feedback x.val))) =
        (fun x : (sᶜ : Set α) => ActualInitializationBlockMeasurability.continuationCodeOf (phase x.val)) := by
      funext x
      cases hp : phase x.val with
      | launched launch => rfl
      | prelaunch live =>
          exact (x.property (by
            change (ActualInitializationBlockMeasurability.continuationCodeOf (phase x.val)).2.2.2.2 = none
            rw [hp]; rfl)).elim
    change Measurable (fun x : (sᶜ : Set α) => ActualInitializationBlockMeasurability.continuationCodeOf
      (replayStep (own x.val) t (phase x.val) (feedback x.val)))
    rw [heq]
    exact hcode.comp measurable_subtype_coe

private theorem measurable_atPosition_code {α : Type*} [MeasurableSpace α]
    (own : α → OwnCoordinates p) (hown : Measurable own) (n : ℕ)
    (phase : α → Continuation p)
    (hbase : Measurable (fun x => phaseBase (phase x)))
    (hcode : Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (phase x))) :
    Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (atPosition (own x) n (phase
      x))) := by
  by_cases hn : n < p.T
  · let s : Set α := {x | (ActualInitializationBlockMeasurability.continuationCodeOf (phase x)).2.2.2.2 = none}
    have hs : MeasurableSet s := measurableSet_eq_fun
      ((measurable_of_countable fun c : ActualInitializationBlockMeasurability.ContinuationCode p =>
        c.2.2.2.2).comp hcode) measurable_const
    apply measurable_of_restrict_of_restrict_compl hs
    · let live := fun x : s => liveOf (phase x.val) x.property
      have hl := measurable_liveOf (fun x : s => phase x.val) (fun x => x.property)
        (hbase.comp measurable_subtype_coe) (hcode.comp measurable_subtype_coe)
      have hb := measurable_atRound (fun x : s => own x.val) (hown.comp measurable_subtype_coe)
        ⟨n, hn⟩ live hl
      have hout := (measurable_of_countable fun c : CoordinatorLocalCode p =>
        (c.block, (c.target, (c.coordinator, (c.monitor.val, (none : Option (Fin p.T))))))).comp
          ((measurable_prelaunchLocalCode p).comp hb)
      convert hout using 1
      funext x
      dsimp only [Set.domRestrict, Function.comp_def]
      rw [← liveOf_eq (phase x.val) x.property]
      simp only [atPosition, hn, ↓reduceDIte, ActualInitializationBlockMeasurability.continuationCodeOf,
        ActualInitializationRun.continuationData,
        Continuation.coordinatorState, Continuation.monitorState, prelaunchCoordinates]
      rfl
    · have heq : (fun x : (sᶜ : Set α) => ActualInitializationBlockMeasurability.continuationCodeOf (atPosition
      (own x.val) n (phase x.val))) =
          (fun x : (sᶜ : Set α) => ActualInitializationBlockMeasurability.continuationCodeOf (phase x.val)) := by
        funext x
        cases hp : phase x.val with
        | launched launch => rfl
        | prelaunch live =>
            exact (x.property (by
              change (ActualInitializationBlockMeasurability.continuationCodeOf (phase x.val)).2.2.2.2 = none
              rw [hp]; rfl)).elim
      change Measurable (fun x : (sᶜ : Set α) => ActualInitializationBlockMeasurability.continuationCodeOf
        (atPosition (own x.val) n (phase x.val)))
      rw [heq]
      exact hcode.comp measurable_subtype_coe
  · have heq : ∀ x, atPosition (own x) n (phase x) = phase x := by
      intro x
      cases phase x <;> simp only [atPosition, hn, ↓reduceDIte]
    convert hcode using 1
    funext x
    rw [heq x]

private abbrev ReplayInput (p : Parameters) (n : ℕ) :=
  CompletePublicTable.PublishedOutput p × (OwnCoordinates p × (Fin n → Fin (D p + 1)))

private def replayBase (a b : ℝ) {n : ℕ} (x : ReplayInput p n) : CoordinatorContinuousBase p :=
  ((x.1.2 (PrivateSourceStreams.coordinatorIndex p x.2.1.1), x.1.1), (a, b))

private theorem measurable_replayBase (a b : ℝ) (n : ℕ) :
    Measurable (replayBase (p := p) a b : ReplayInput p n → _) := by
  have hJ : Measurable (fun x : ReplayInput p n =>
      PrivateSourceStreams.coordinatorIndex p x.2.1.1) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_fst.comp (measurable_fst.comp measurable_snd))
  have hr : Measurable (fun x : ReplayInput p n => x.1.2) := measurable_snd.comp measurable_fst
  have hselected : Measurable (fun x : ReplayInput p n =>
      x.1.2 (PrivateSourceStreams.coordinatorIndex p x.2.1.1)) := by
    intro s hs
    rw [show (fun x : ReplayInput p n => x.1.2
        (PrivateSourceStreams.coordinatorIndex p x.2.1.1)) ⁻¹' s =
        ⋃ j : Fin (M p), {x | PrivateSourceStreams.coordinatorIndex p x.2.1.1 = j} ∩
          {x | x.1.2 j ∈ s} by ext x; simp]
    exact MeasurableSet.iUnion fun j => (measurableSet_eq_fun hJ measurable_const).inter
      (((measurable_pi_apply j).comp hr) hs)
  exact (hselected.prodMk (measurable_fst.comp measurable_fst)).prodMk
    (measurable_const.prodMk measurable_const)

private theorem measurable_initial_code (a b : ℝ) (n : ℕ) :
    Measurable (fun x : ReplayInput p n =>
      ActualInitializationBlockMeasurability.continuationCodeOf (replayInitial x.1 x.2.1 a b)) := by
  let inputs := fun x : ReplayInput p n => ({
    base := replayBase a b x
    block := ActualInitializationRun.firstBlock p
    carried := coordinatorStateCode p (BootstrapPhysicalBlock.initialState p)
    monitor := ⟨monitorCode p (ActualInitializationRun.initialUnlaunchedMonitor p).val,
      (ActualInitializationRun.initialUnlaunchedMonitor p).property⟩
    targetScalar := x.2.1.2.2 (ActualInitializationRun.firstBlock p) } : CoordinatorBeginBlockInput p)
  have hi : Measurable inputs := by
    apply measurable_comap_iff.mpr
    exact (measurable_replayBase a b n).prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_const.prodMk
        ((measurable_pi_apply _).comp (measurable_snd.comp (measurable_snd.comp
          (measurable_fst.comp measurable_snd)))))))
  have hout := (measurable_of_countable fun c : CoordinatorLocalCode p =>
    (c.block, (c.target, (c.coordinator, (c.monitor.val, (none : Option (Fin p.T))))))).comp
      (measurable_snd.comp ((measurable_coordinatorBeginBlockCode p).comp hi))
  exact hout

private theorem measurable_replayRaw_code (a b : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (fun x : ReplayInput p n => ActualInitializationBlockMeasurability.continuationCodeOf
      (replayRaw x.1 x.2.1 a b n hn x.2.2)) := by
  induction n with
  | zero => exact measurable_initial_code a b 0
  | succ n ih =>
      let restrict := fun x : ReplayInput p (n + 1) =>
        (x.1, (x.2.1, fun j : Fin n => x.2.2 j.castSucc))
      have hr : Measurable restrict := measurable_fst.prodMk
        ((measurable_fst.comp measurable_snd).prodMk
          (measurable_pi_iff.mpr fun j => (measurable_pi_apply j.castSucc).comp
            (measurable_snd.comp measurable_snd)))
      let phase := fun x : ReplayInput p (n + 1) =>
        replayRaw x.1 x.2.1 a b n (by omega) (fun j => x.2.2 j.castSucc)
      have hc : Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (phase x)) :=
        (ih (by omega)).comp hr
      have hb : Measurable (fun x => phaseBase (phase x)) := by
        convert (measurable_replayBase (p := p) a b (n + 1)) using 1
        funext x
        exact replayRaw_base x.1 x.2.1 a b n (by omega) (fun j => x.2.2 j.castSucc)
      have hconst : ∀ x, (phaseBase (phase x)).2 = (a, b) := by
        intro x; rw [replayRaw_base]
      exact measurable_stepCode a b (fun x : ReplayInput p (n + 1) => x.2.1)
        (measurable_fst.comp measurable_snd) ⟨n, by omega⟩ phase hb hc hconst
        (fun x => x.2.2 (Fin.last n))
        ((measurable_pi_apply _).comp (measurable_snd.comp measurable_snd))

/-- Joint Borel measurability on the actual whole-public/own/finite-grid-history
product. Continuous coordinates retain their original product Borel spaces;
only the existing local/monitor/launch fields use countable codes. -/
theorem measurable_initializationReplayCode (a b : ℝ) (n : ℕ) (hn : n ≤ p.T) :
    Measurable (initializationReplayCode (p := p) a b n hn) := by
  have hb : Measurable (fun x : ReplayInput p n => phaseBase
      (replayRaw x.1 x.2.1 a b n hn x.2.2)) := by
    convert (measurable_replayBase (p := p) a b n) using 1
    funext x
    exact replayRaw_base x.1 x.2.1 a b n hn x.2.2
  exact measurable_atPosition_code (fun x : ReplayInput p n => x.2.1)
    (measurable_fst.comp measurable_snd) n _ hb (measurable_replayRaw_code a b n hn)

/-- The actual next initialization preparation. The launched branch has no
bootstrap preparation or fabricated arm. -/
def initializationPreparedRound (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (t : Fin p.T)
    (feedback : Fin t.val → Fin (D p + 1)) : Option (PreparedRound p) :=
  match initializationReplay published own a b t.val t.isLt.le feedback with
  | .launched _ => none
  | .prelaunch live => some (prepare p (atRound own t live) t (atRound_mem own t live) (own.2.1 t))

theorem sourceInitialized_initialization_prepared_arm
    (record : ActualInitializationRun.PhysicalRoundRecord p rate source rewards)
    (hrecord : record ∈ ActualCompletePhysicalHistory.initializationRecords
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)) :
    (initializationPreparedRound source.1 (ownCoordinates source) C_star C_h record.time
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h record.time.val record.time.isLt.le)).map
        PreparedRound.arm = some (record.result.actions (ActiveRoundActions.coordinator p.two_le_m)) := by
  unfold initializationPreparedRound
  rw [sourceInitialized_initialization_coordinator_replay rate source rewards C_star C_h record hrecord]
  simp only [atRound_eq _ _ _ (record_mem record), Option.map_some, prepare]
  change some (coordinatorArmChoice p record.coordinatorBefore.data.row record.coordinatorBefore.data.target
    record.coordinatorBefore.data.coordinator record.time ((ownCoordinates source).2.1 record.time)) =
      some (ActualInitializationPhysicalStep.actionProfile record.result.prepared
        (ActiveRoundActions.coordinator p.two_le_m))
  rw [ActualInitializationPhysicalStep.actionProfile_coordinator]
  have ha := congrArg PreparedRound.arm record.result.prepared.coordinator_eq
  simp only [prepare] at ha
  rw [(record_inputs record).1, (record_inputs record).2, record.result_time] at ha
  exact congrArg some ha.symm

/-- At `T` the two terminal tags remain distinct. Both an exhausted run and a
launch at the final boundary have prefix length `T`; the saved launch position
in the launched branch is the actual prefix length. -/
theorem sourceInitialized_initializationReplay_terminal_cases :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    let replay := initializationReplay source.1 (ownCoordinates source) C_star C_h p.T le_rfl
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h p.T le_rfl)
    match run.terminalDisposition with
    | .continueNext _ _ => False
    | .launched launch _ => replay = .launched launch ∧
        run.records.length = launch.monitor.launchPosition
    | .exhausted live => replay = .prelaunch live ∧ run.records.length = p.T := by
  dsimp only
  let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
  have he := sourceInitialized_initializationReplay_of_ge_prefix rate source rewards C_star C_h
    p.T le_rfl (sourceInitializationRecordCount_le rate source rewards C_star C_h)
  cases hd : (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star
    C_h).terminalDisposition with
  | continueNext next carry =>
      exact (ActualCompletePhysicalHistory.sourceRun_not_continueNext p rate source rewards C_star C_h run next
        carry hd).elim
  | launched launch seed =>
      have hh : (ActualInitializationRun.combinedBoundaryHandoff p rate run.terminalBlock source rewards
          run.terminalC_star run.terminalC_h run.terminalFold).disposition = .launched launch seed := by
        rw [← run.terminalHandoff_eq, ← run.terminalDisposition_eq]; exact hd
      have hp := phase_of_launched_handoff rate source rewards run.terminalFold launch seed hh
      have hl := ActualInitializationHorizon.sourceInitializedRun_terminal_launch_strict p rate source rewards
        C_star C_h launch seed hd
      exact ⟨he.trans hp, (ActualCompletePhysicalHistory.initializationRun_record_count p rate source rewards
        C_star C_h).trans hl.2.2.2.symm⟩
  | exhausted live =>
      have hh : (ActualInitializationRun.combinedBoundaryHandoff p rate run.terminalBlock source rewards
          run.terminalC_star run.terminalC_h run.terminalFold).disposition = .exhausted live := by
        rw [← run.terminalHandoff_eq, ← run.terminalDisposition_eq]; exact hd
      have hp := phase_of_exhausted_handoff rate source rewards run.terminalFold live hh
      exact ⟨he.trans hp, terminal_prelaunch_horizon rate source rewards C_star C_h live hp⟩

variable (other : SourceInput p) (otherRewards : GridRewardTable p)

/-- Two original sources and reward tables have the same entire initialization
continuation from equality of the whole public output, exactly the own private
projection, and strictly earlier own feedback. No launch or state is assumed. -/
theorem initialization_replay_own_history_local (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1) (hown : ownCoordinates source = ownCoordinates other)
    (hpast : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
      (ActiveRoundActions.coordinator p.two_le_m)).take n =
        (ActualCompletePhysicalHistory.playerGridFeedbackHistory
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards C_star C_h)
          (ActiveRoundActions.coordinator p.two_le_m)).take n) :
    initializationReplay source.1 (ownCoordinates source) C_star C_h n hn
      (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn) =
    initializationReplay other.1 (ownCoordinates other) C_star C_h n hn
      (sourceOwnFeedbackPrefix rate other otherRewards C_star C_h n hn) := by
  have hfeedback := List.ofFn_injective
    ((sourceOwnFeedbackPrefix_list rate source rewards C_star C_h n hn).trans
      (hpast.trans (sourceOwnFeedbackPrefix_list rate other otherRewards C_star C_h n hn).symm))
  rw [hpublic, hown, hfeedback]

theorem initialization_survival_own_history_local (n : ℕ) (hn : n < p.T)
    (hpublic : source.1 = other.1) (hown : ownCoordinates source = ownCoordinates other)
    (hpast : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
      (ActiveRoundActions.coordinator p.two_le_m)).take n =
        (ActualCompletePhysicalHistory.playerGridFeedbackHistory
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards C_star C_h)
          (ActiveRoundActions.coordinator p.two_le_m)).take n) :
    (n < ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)) ↔
    (n < ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards C_star C_h)) := by
  rw [← sourceInitialized_initializationReplay_prelaunch_iff rate source rewards C_star C_h n hn,
    ← sourceInitialized_initializationReplay_prelaunch_iff rate other otherRewards C_star C_h n hn,
    initialization_replay_own_history_local rate source rewards C_star C_h other otherRewards n hn.le hpublic
      hown hpast]

theorem initialization_prechoice_own_history_local (t : Fin p.T)
    (hpublic : source.1 = other.1) (hown : ownCoordinates source = ownCoordinates other)
    (hpast : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
      (ActiveRoundActions.coordinator p.two_le_m)).take t.val =
        (ActualCompletePhysicalHistory.playerGridFeedbackHistory
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards C_star C_h)
          (ActiveRoundActions.coordinator p.two_le_m)).take t.val) :
    initializationPreparedRound source.1 (ownCoordinates source) C_star C_h t
        (sourceOwnFeedbackPrefix rate source rewards C_star C_h t.val t.isLt.le) =
      initializationPreparedRound other.1 (ownCoordinates other) C_star C_h t
        (sourceOwnFeedbackPrefix rate other otherRewards C_star C_h t.val t.isLt.le) := by
  unfold initializationPreparedRound
  rw [initialization_replay_own_history_local rate source rewards C_star C_h other otherRewards
    t.val t.isLt.le hpublic hown hpast, hown]

private theorem atRound_block (own : OwnCoordinates p) (t : Fin p.T) (live : PrelaunchBlock p) :
    (atRound own t live).data.block = roundBlockIndex p t := by
  unfold atRound
  split
  · rename_i ht
    exact Fin.ext ((mem_calendarBlock_iff_quotient p live.data.block t).mp ht)
  · rfl

/-- For any supplied finite feedback, a still-live post-observation state is
in the block of the last consumed round. Thus the replay cannot skip a block. -/
theorem replayRaw_prelaunch_block (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (k : ℕ) (hk : k + 1 ≤ p.T)
    (feedback : Fin (k + 1) → Fin (D p + 1)) (live : PrelaunchBlock p)
    (hphase : replayRaw published own a b (k + 1) hk feedback = .prelaunch live) :
    live.data.block = roundBlockIndex p ⟨k, by omega⟩ := by
  change replayStep own ⟨k, by omega⟩
    (replayRaw published own a b k (by omega) (fun j => feedback j.castSucc))
    (feedback (Fin.last k)) = .prelaunch live at hphase
  cases hp : replayRaw published own a b k (by omega) (fun j => feedback j.castSucc) with
  | launched launch => rw [hp] at hphase; cases hphase
  | prelaunch before =>
      rw [hp] at hphase
      have hd := congrArg (fun phase => (ActualInitializationRun.continuationData p phase).block) hphase
      dsimp only [replayStep, observe, prepare] at hd
      rw [ActualInitializationRun.continuationAfterObservation_data] at hd
      exact hd.symm.trans (atRound_block own ⟨k, by omega⟩ before)

/-- Every reset reached by this recursion is exactly a calendar block start
following a completed live block. The domain excludes the nonexistent next
choice at `T`, which `initializationReplay` already leaves untouched. -/
theorem replay_reset_at_block_start (published : CompletePublicTable.PublishedOutput p)
    (own : OwnCoordinates p) (a b : ℝ) (k : ℕ) (hk : k + 1 < p.T)
    (feedback : Fin (k + 1) → Fin (D p + 1)) (live : PrelaunchBlock p)
    (hphase : replayRaw published own a b (k + 1) hk.le feedback = .prelaunch live)
    (hreset : (⟨k + 1, hk⟩ : Fin p.T) ∉ calendarBlock p live.data.block) :
    k + 1 = BootstrapObservedFollower.blockStop p live.data.block ∧
      k + 1 = BootstrapObservedFollower.blockStart p (roundBlockIndex p ⟨k + 1, hk⟩) := by
  have hb := replayRaw_prelaunch_block published own a b k hk.le feedback live hphase
  have hm : (⟨k, by omega⟩ : Fin p.T) ∈ calendarBlock p live.data.block := by
    rw [hb]; exact round_mem_quotient_block p _
  have hp := (mem_calendarBlock_iff p live.data.block _).mp hm
  change BootstrapObservedFollower.blockStart p live.data.block ≤ k ∧
    k < BootstrapObservedFollower.blockStop p live.data.block at hp
  have hn : ¬ k + 1 < BootstrapObservedFollower.blockStop p live.data.block := by
    intro ht
    apply hreset
    apply (mem_calendarBlock_iff p live.data.block _).mpr
    exact ⟨le_trans hp.1 (Nat.le_succ k), ht⟩
  have he : k + 1 = BootstrapObservedFollower.blockStop p live.data.block := by omega
  refine ⟨he, ?_⟩
  have hmultiple : k + 1 = (live.data.block.val + 1) * B_boot p := by
    rw [BootstrapObservedFollower.blockStop] at he
    omega
  change k + 1 = ((k + 1) / B_boot p) * B_boot p
  rw [hmultiple, Nat.mul_div_cancel _ (B_boot_pos p)]

/-- Equality of a prefix reconstructs every strictly earlier own preparation;
past arm entries need not be supplied as additional hypotheses. -/
theorem initialization_earlier_preparations_own_history_local (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1) (hown : ownCoordinates source = ownCoordinates other)
    (hpast : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
      (ActiveRoundActions.coordinator p.two_le_m)).take n =
        (ActualCompletePhysicalHistory.playerGridFeedbackHistory
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards C_star C_h)
          (ActiveRoundActions.coordinator p.two_le_m)).take n) (j : Fin n) :
    initializationPreparedRound source.1 (ownCoordinates source) C_star C_h ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
        (sourceOwnFeedbackPrefix rate source rewards C_star C_h j.val (by omega)) =
      initializationPreparedRound other.1 (ownCoordinates other) C_star C_h ⟨j.val, lt_of_lt_of_le j.isLt hn⟩
        (sourceOwnFeedbackPrefix rate other otherRewards C_star C_h j.val (by omega)) := by
  apply initialization_prechoice_own_history_local rate source rewards C_star C_h other otherRewards
    _ hpublic hown
  have he := congrArg (List.take j.val) hpast
  simpa only [List.take_take, Nat.min_eq_left j.isLt.le] using he

/-- The existing prepared-round code, absent exactly after launch. -/
def initializationPreparedCode (a b : ℝ) (t : Fin p.T)
    (x : CompletePublicTable.PublishedOutput p ×
      (OwnCoordinates p × (Fin t.val → Fin (D p + 1)))) : Option (PreparedRoundCode p) :=
  (initializationPreparedRound x.1 x.2.1 a b t x.2.2).map (encodePreparedRound p)

theorem measurable_initializationPreparedCode (a b : ℝ) (t : Fin p.T) :
    Measurable (initializationPreparedCode (p := p) a b t) := by
  let phase := fun x : ReplayInput p t.val => initializationReplay x.1 x.2.1 a b t.val t.isLt.le x.2.2
  have hc : Measurable (fun x => ActualInitializationBlockMeasurability.continuationCodeOf (phase x)) :=
    measurable_initializationReplayCode a b t.val t.isLt.le
  have hb : Measurable (fun x => phaseBase (phase x)) := by
    convert (measurable_replayBase (p := p) a b t.val) using 1
    funext x
    dsimp only [phase, initializationReplay]
    rw [atPosition_base, replayRaw_base]
    rfl
  let s : Set (ReplayInput p t.val) := {x | (ActualInitializationBlockMeasurability.continuationCodeOf (phase
    x)).2.2.2.2 = none}
  have hs : MeasurableSet s := measurableSet_eq_fun
    ((measurable_of_countable fun c : ActualInitializationBlockMeasurability.ContinuationCode p =>
      c.2.2.2.2).comp hc) measurable_const
  apply measurable_of_restrict_of_restrict_compl hs
  · let live := fun x : s => liveOf (phase x.val) x.property
    have hl := measurable_liveOf (fun x : s => phase x.val) (fun x => x.property)
      (hb.comp measurable_subtype_coe) (hc.comp measurable_subtype_coe)
    let before := fun x : s => atRound x.val.2.1 t (live x)
    have hbefore : Measurable before := measurable_atRound (fun x : s => x.val.2.1)
      ((measurable_fst.comp measurable_snd).comp measurable_subtype_coe) t live hl
    let inputs := fun x : s =>
      (⟨(prelaunchCoordinates p (before x)).1, (prelaunchCoordinates p (before x)).2,
        t, atRound_mem _ _ _⟩ : CoordinatorRoundInput p)
    have hcoords := (measurable_prelaunchCoordinates p).comp hbefore
    have hi : Measurable inputs := by
      apply measurable_comap_iff.mpr
      exact (measurable_fst.comp hcoords).prodMk
        ((measurable_snd.comp hcoords).prodMk measurable_const)
    have hv : Measurable (fun x : s => x.val.2.1.2.1 t) :=
      (measurable_pi_apply t).comp (measurable_fst.comp (measurable_snd.comp
        (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))))
    have hout := (measurable_of_countable (some : PreparedRoundCode p → Option (PreparedRoundCode p))).comp
      ((measurable_coordinatorPreparedRoundCode p).comp (hi.prodMk hv))
    convert hout using 1
    funext x
    dsimp only [Set.domRestrict, Function.comp_def, initializationPreparedCode]
    have hp : initializationReplay x.val.1 x.val.2.1 a b t.val t.isLt.le x.val.2.2 =
        .prelaunch (live x) := (liveOf_eq (phase x.val) x.property).symm
    simp only [initializationPreparedRound, hp, Option.map_some]
    change some (encodePreparedRound p (prepare p (before x) t _ _)) =
      some (coordinatorPreparedRoundCode p (inputs x) _)
    unfold coordinatorPreparedRoundCode
    dsimp only [inputs]
    rw [prepare_coordinates]
  · have heq : ∀ x : (sᶜ : Set (ReplayInput p t.val)), initializationPreparedCode a b t x.val = none := by
      intro x
      cases hp : phase x.val with
      | prelaunch live =>
          exact (x.property (by
            change (ActualInitializationBlockMeasurability.continuationCodeOf (phase x.val)).2.2.2.2 = none
            rw [hp]; rfl)).elim
      | launched launch =>
          have hp' : initializationReplay x.val.1 x.val.2.1 a b t.val t.isLt.le x.val.2.2 =
              .launched launch := hp
          simp only [initializationPreparedCode, initializationPreparedRound, hp', Option.map_none]
    convert (measurable_const : Measurable (fun _ : (sᶜ : Set (ReplayInput p t.val)) =>
      (none : Option (PreparedRoundCode p)))) using 1
    funext x
    exact heq x

/-- Once launch has occurred by the queried prefix, the two actual terminal
launches and their cuts agree. No equality of future cuts is asserted for a
prefix which is still live. The only root inputs are the three local equalities. -/
theorem initialization_launched_own_history_local (n : ℕ) (hn : n ≤ p.T)
    (hpublic : source.1 = other.1) (hown : ownCoordinates source = ownCoordinates other)
    (hpast : (ActualCompletePhysicalHistory.playerGridFeedbackHistory
      (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate source rewards C_star C_h)
      (ActiveRoundActions.coordinator p.two_le_m)).take n =
        (ActualCompletePhysicalHistory.playerGridFeedbackHistory
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards C_star C_h)
          (ActiveRoundActions.coordinator p.two_le_m)).take n) :
    ∀ launch, initializationReplay source.1 (ownCoordinates source) C_star C_h n hn
        (sourceOwnFeedbackPrefix rate source rewards C_star C_h n hn) = .launched launch →
      (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h).terminalFold.phase =
        .launched launch ∧
      (ActualInitializationHorizon.sourceInitializedRun p rate other otherRewards C_star
        C_h).terminalFold.phase = .launched launch ∧
      ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount
        (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory
        p rate source rewards C_star C_h) = ActualCompletePhysicalHistory.CompleteHistory.prefixRoundCount
          (ActualCompletePhysicalHistory.sourceInitializedActualCompleteHistory p rate other otherRewards
            C_star C_h) := by
  intro launch hlaunch
  have hlocal := initialization_replay_own_history_local rate source rewards C_star C_h
    other otherRewards n hn hpublic hown hpast
  have hfirst := sourceInitialized_initializationReplay_launched rate source rewards C_star C_h n hn launch hlaunch
  have hsecond := sourceInitialized_initializationReplay_launched rate other otherRewards C_star C_h
    n hn launch (hlocal.symm.trans hlaunch)
  refine ⟨hfirst, hsecond, ?_⟩
  have ha := (ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star
    C_h).terminalFold.invariant.1.1
  have hb := (ActualInitializationHorizon.sourceInitializedRun p rate other otherRewards C_star
    C_h).terminalFold.invariant.1.1
  rw [hfirst] at ha
  rw [hsecond] at hb
  have hblock := ha.symm.trans hb
  rw [← source_prefix_count rate source rewards C_star C_h,
    ← source_prefix_count rate other otherRewards C_star C_h,
    ActualCompletePhysicalHistory.initializationRun_record_count,
      ActualCompletePhysicalHistory.initializationRun_record_count, hblock]

/-- Identify the replay endpoint with the actual terminal block and carried
input reconstructed by the existing horizon observation theorem. -/
theorem sourceInitialized_initializationReplay_terminal_reconstruction :
    let run := ActualInitializationHorizon.sourceInitializedRun p rate source rewards C_star C_h
    ∃ (terminal : Fin (n_boot p)) (carry : ActualInitializationBlockMeasurability.FixedConstantsBlockCarry
        p rate terminal C_star C_h),
      initializationReplay source.1 (ownCoordinates source) C_star C_h run.records.length
          (sourceInitializationRecordCount_le rate source rewards C_star C_h)
          (sourceOwnFeedbackPrefix rate source rewards C_star C_h run.records.length
            (sourceInitializationRecordCount_le rate source rewards C_star C_h)) =
        (ActualInitializationRun.foldBlock p rate terminal source rewards carry.val).phase ∧
      ActualInitializationHorizonObservation.finalCarriedInput
        ⟨ActualInitializationRun.firstBlock p, ActualInitializationRun.initialCarry p rate C_star C_h⟩
        run.continuedBlocks = ⟨terminal, carry.val⟩ := by
  let input : ActualInitializationBlockMeasurability.BlockInput p rate
      (ActualInitializationRun.firstBlock p) C_star C_h :=
    (source, ⟨ActualInitializationRun.initialCarry p rate C_star C_h, rfl, rfl⟩)
  obtain ⟨terminal, carry, _, _, hcarry, _, _, _, _, _, hdata⟩ :=
    ActualInitializationHorizonObservation.runFrom_terminal_reconstruction
      (rewards := rewards) (ActualInitializationRun.firstBlock p) input
  have hp := congrArg (fun data => data.2.2.2.1.phase) hdata
  exact ⟨terminal, carry,
    (sourceInitialized_initializationReplay_endpoint rate source rewards C_star C_h).trans hp, hcarry⟩

end Bandits.Support.ActualInitializationCoordinatorOwnHistory

end
