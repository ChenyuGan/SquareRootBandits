/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionLateUpSender
public import Bandits.Support.ReferenceFirstCollectionLateUpReceiverEligibility
public import Bandits.Support.ReferenceFixedUpCompletedWindowTruth

/-!
# Actual late first-collection UP second window

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,277-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,151-157`.

This module connects the actual corrected launch to the general saved-window
cut.  The local endpoint and positive-count conditions remain visible at the
query where they are needed.  It uses the admitted sender root only for the
first-collection index bound; sender-word truth and receiver acceptance are
not yet composed here, and this conditional query is not a service or
manuscript-closure claim.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceUpDecoderBankInvariant

namespace Bandits.Support.ReferenceFirstCollectionLateUpSecondWindow

local instance propDecidable (q : Prop) : Decidable q := Classical.propDecidable q

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput

variable {p : Parameters}

/-- The actual corrected launch supplies the invariant and empty initial UP
batch required by the general interval theorem.  The run result is included
so callers can use the same produced invariant at their actual local endpoint.
-/
theorem actual_launch_up_bank_seed
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T) :
    let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    upBankInvariant initial ∧
      (∀ i, AffineBatchDecoder.collected (initial.upDecoderBank i) = []) ∧
      upBankInvariant
        (ReferenceActivePhysicalHorizon.run initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
          start count hspan active).finalState := by
  classical
  intro initial start active
  let launched :=
    ReferenceFirstLaunchNumericalCell.actual_launch_seed rate source rewards C_star C_h hcross
  have hfirst : initial.coordinator = .first := by
    dsimp only [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
    exact launched.2.2.2.1
  have hbank : initial.upDecoderBank = CoordinatorUpReception.initialUpDecoderBank p := by
    dsimp only [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
    exact launched.2.2.2.2.1
  have hmode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start := by
    dsimp only [initial, start, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
    exact launched.2.1
  have hinitial : upBankInvariant initial := by
    unfold upBankInvariant
    rw [hfirst, hbank]
    exact ⟨CoordinatorUpReception.initialUpDecoderBank_wellFormed p, fun _ => rfl⟩
  have hseed : ∀ i, AffineBatchDecoder.collected (initial.upDecoderBank i) = [] := by
    intro i
    rw [hbank]
    simp [CoordinatorUpReception.initialUpDecoderBank,
      AffineBatchDecoder.collected, AffineBatchDecoder.initial]
  have hrun := ReferenceUpDecoderBankInvariant.run_upBankInvariant
    initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
    rewards start count hspan active hinitial
  exact ⟨hinitial, hseed, hrun⟩

/-- The indexed collection-window record is an actual record in the original
first-collection run.  This bound is taken from A's produced source lookup.
-/
theorem first_collection_window_index_lt_count
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (k : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records)
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length) :
    (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length + k.val < count := by
  let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
  let b0 := ReferenceInitializationRun.output x0
  let s := ReferenceInitializationRun.elapsed p b0.completed
  let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
    rate source rewards C_star C_h hcross).1
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let w := W.length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hroot := ReferenceFirstCollectionLateUpSender.actual_first_collection_late_up_sender
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hroot with
    ⟨_cutoffRecord, _suffix, _registers, _owned, _base, _P0, _birth,
      _hsplit, _hindex, _htime, _hstate, _hcutoffChosen, _hP0, _hP0sigma,
      _hP0queues, _hfirstCutoff, _hbirth, _hbirthInstall, _hbirthTime,
      hwindow, _hqueries⟩
  have hwindowK := hwindow k
  have hElen : E.records.length = count := by
    dsimp only [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
  have hindex : w + k.val < E.records.length :=
    (List.getElem?_eq_some_iff.mp hwindowK.1).1
  rw [hElen] at hindex
  exact hindex

/-- The actual saved-window result from the public general interval cut. -/
abbrev SavedCutOutput
    (rate : RateInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ)
    (hspanA : start + a ≤ p.T)
    (hspan : start + b ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (i : Fin (p.m - 1)) : Prop :=
  let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a hspanA mode
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start b hspan mode
  let interval := full.records.drop a
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
  let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
    initial rows selected rewards start a b hspan mode
  let positive := AffineBatchDecoder.positives p trace rounds
  let channel := preRun.finalState.upDecoderBank i
  let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
  ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
    (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (index : Fin rounds.length)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
    let before := AffineBatchDecoder.run p trace (rounds.take index.val) channel
    first = channel.pending ++ positive.take
        (AffineBatchDecoder.quota p - channel.pending.length) ∧
    first.length = AffineBatchDecoder.quota p ∧
    window.length = AffineBatchDecoder.quota p ∧
    window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
    last ∈ window ∧
    AffineBatchDecoder.decisionTime window = some last.time ∧
    rounds.get index = last.time ∧
    record ∈ interval ∧
    record.input.time = last.time ∧
    record.output.coordinator.up = some diagnostic ∧
    diagnostic.input.selectedFollower = i ∧
    diagnostic.input.time = record.input.time ∧
    last = AffineBatchDecoder.entry p trace last.time ∧
    last.sample = ((record.input.rows record.input.selected).2 record.input.time).2
      (1, CoordinatorUpMeasurability.selectedChannelFollower
        ((record.input.rows record.input.selected).2 record.input.time)) ∧
    (∃ ledger,
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some ledger ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) = true ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger ∧
      diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger)).1 ∧
      diagnostic.input.time = record.input.time ∧
      diagnostic.input.selectedFollower =
        CoordinatorUpMeasurability.selectedFollowerIndex
          ((record.input.rows record.input.selected).2 record.input.time) ∧
      diagnostic.input.affineSample =
        ((record.input.rows record.input.selected).2 record.input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((record.input.rows record.input.selected).2 record.input.time)) ∧
      diagnostic.input.ownObservation =
        (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) ∧
      (ReferenceActivePhysicalStep.prepare record.input).feedback.feedback
          (ActiveRoundActions.coordinator p.two_le_m) =
        (if FiniteBanditModel.collisionFreeFor
            (ReferenceActivePhysicalStep.prepare record.input).arms.actions
              (ActiveRoundActions.coordinator p.two_le_m) then
          record.input.rewards record.input.time
            ((ReferenceActivePhysicalStep.prepare record.input).arms.actions
              (ActiveRoundActions.coordinator p.two_le_m))
        else 0) ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).receiverEnabled = true ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).sample =
        diagnostic.input.affineSample ∧
      (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic).roundedReward =
        CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation ∧
      (AffineBatchDecoder.eligible
        (ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput diagnostic) ↔
        CoordinatorUpReception.receptionGate diagnostic.input ∧
          0 < CoordinatorUpReception.roundedObservationValue p diagnostic.input.ownObservation) ∧
      record.output.ownEntries (ActiveRoundActions.coordinator p.two_le_m) =
        (record.output.preparation.arms.actions
          (ActiveRoundActions.coordinator p.two_le_m),
         ActualInitializationPhysicalStep.observationOfGrid p
          (record.output.preparation.feedback.feedback
            (ActiveRoundActions.coordinator p.two_le_m)))) ∧
    ReferenceActivePhysicalHorizon.Connected preRun.finalState
      (interval.take index.val) record.input.state ∧
    record.input.state.upDecoderBank =
      ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics
          (interval.take index.val)) ∧
    diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
    before = diagnostic.input.upDecoderBank i ∧
    before.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
    (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
    (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
      channel.completed ++ [first, window] ∧
    diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
    diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
    diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
    CoordinatorUpReception.decoderTransition diagnostic.input =
      (⟨[], channel.completed ++ [first, window]⟩,
        AffineBatchDecoder.batchOutput window) ∧
    AffineBatchDecoder.run p trace rounds channel =
      ⟨[], channel.completed ++ [first, window]⟩ ∧
    AffineBatchDecoder.run p trace rounds channel = full.finalState.upDecoderBank i

/-- D's actual interval result, with endpoint, bank, and count conditions
explicitly supplied at the local query. -/
theorem run_interval_saved_cut_exact
    (rate : RateInput p)
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p)
    (selected : Fin (ConstructorDimensions.M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a b : ℕ) (hab : a ≤ b)
    (hspan : start + b ≤ p.T) (hspanA : start + a ≤ p.T)
    (mode : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hordinary : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start b
      hspan mode).finalState.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (hpositiveCount :
      (AffineBatchDecoder.positives p
        (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
          (ReferenceCoordinatorUpIntervalWindow.intervalRecords initial rows selected rewards
            start a b hspan mode) i)
        (ReferenceCoordinatorUpIntervalWindow.intervalRounds
          initial rows selected rewards start a b hspan mode)).length =
      AffineBatchDecoder.quota p -
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start a
          hspanA mode).finalState.upDecoderBank i).pending.length +
          AffineBatchDecoder.quota p) :
    SavedCutOutput rate initial rows selected rewards start a b hspanA hspan mode i := by
  classical
  exact ReferenceCoordinatorUpWindowCompletedCut.run_interval_saved_completed_cut
    initial rows selected rewards start a b hab hspan mode hinitial hordinary i hseed
    hpositiveCount

/-- The actual saved second UP window in the late first-collection interval.
The outer telescope is the original source, whole reward grid, unrestricted
constants, actual initialization crossing, elapsed-prefix bound, and short
first live window.  The endpoint branch and exact two-batch positive count
remain local conditions.  The conclusion is D's actual saved-window and
diagnostic cut, including decoder provenance and before/after state.  It does
not assert service-count attainment, sent-word equality, or successful
reception.
-/
theorem actual_first_collection_late_up_second_window
    (rate : RateInput p)
    (source : SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∀ (k : Fin B.length) (i : Fin (p.m - 1))
      (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
      ReferenceAcceptedUpFollowerHistory.RetainedDown B[k] i M →
      let j := w + k.val
      let b := j + 1
      let Wlate := (E.records.drop b).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input)
      ∀ (n : ℕ) (_hn : n ≤ Wlate.length),
        ∃ hspan_n : s + (b + n) ≤ p.T,
        (ReferenceActivePhysicalHorizon.run I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + n)
          hspan_n active).finalState.coordinator ≠ .dagger →
        (AffineBatchDecoder.positives p
          (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace
            (ReferenceCoordinatorUpIntervalWindow.intervalRecords I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
              hspan_n active) i)
          (ReferenceCoordinatorUpIntervalWindow.intervalRounds I source.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
            hspan_n active)).length =
          AffineBatchDecoder.quota p -
            ((ReferenceActivePhysicalHorizon.run I source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b
              ((Nat.add_le_add_left (Nat.le_add_right b n) s).trans hspan_n)
              active).finalState.upDecoderBank i).pending.length +
            AffineBatchDecoder.quota p →
        SavedCutOutput rate I source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
          ((Nat.add_le_add_left (Nat.le_add_right b n) s).trans hspan_n)
          hspan_n active i := by
  classical
  intro x0 b0 s I active E W w B k i M hretained j b Wlate n _hn
  have hElen : E.records.length = count := by
    dsimp only [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun]
    exact ReferenceActivePhysicalHorizon.run_record_count I source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan active
  have hdropLen : (E.records.drop b).length = count - b := by
    rw [List.length_drop, hElen]
  have hlateBound : Wlate.length ≤ count - b := by
    calc
      Wlate.length ≤ (E.records.drop b).length := (List.takeWhile_prefix _).length_le
      _ = count - b := hdropLen
  have hb : b ≤ count := by
    dsimp only [b, j]
    exact Nat.succ_le_of_lt
      (first_collection_window_index_lt_count rate source rewards C_star C_h
        count hcross hspan hshort k)
  have hnc : n ≤ count - b := Nat.le_trans _hn hlateBound
  have hbound : b + n ≤ count := by
    simpa [Nat.add_comm] using Nat.add_le_of_le_sub hb hnc
  have hstart : s + count ≤ p.T := by
    dsimp only [s, b0, x0]
    exact hspan
  have hspan_n : s + (b + n) ≤ p.T := (Nat.add_le_add_left hbound s).trans hstart
  refine ⟨hspan_n, ?_⟩
  intro hOrd hCount
  let hlaunch := actual_launch_up_bank_seed rate source rewards C_star C_h count hcross hspan
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant I := by
    simpa only [I] using hlaunch.1
  have hseed : ∀ i, AffineBatchDecoder.collected (I.upDecoderBank i) = [] := by
    intro i
    simpa only [I] using hlaunch.2.1 i
  exact run_interval_saved_cut_exact rate I source.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s b (b + n)
    (Nat.le_add_right b n) hspan_n
    ((Nat.add_le_add_left (Nat.le_add_right b n) s).trans hspan_n)
    active hinitial hOrd i (hseed i) hCount

end Bandits.Support.ReferenceFirstCollectionLateUpSecondWindow

end
