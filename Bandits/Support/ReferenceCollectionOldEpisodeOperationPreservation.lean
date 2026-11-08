/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteOriginalCalendarRawLearningComparison

import Mathlib.Tactic

/-!
# Actual old-episode operation frames

The local frames below are indexed by records of the original complete suffix.
Their clocks, numerical cells, local successes, and transitions are derived
from that suffix and its source-generated launch.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCompletePhysicalHistory
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ActualInitializationPhysicalStep
open Bandits.Support.CoordinatorRoundDispatch
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLiveChoiceRecorderStep
open Bandits.Support.CoordinatorLiveServiceFinish
open Bandits.Support.CanonicalFastSampling
open Bandits.Support.ReferenceCoordinatorClockDomains
open Bandits.Support.ReferenceLaterLiveNumericalReadout
open Bandits.Support.ReferenceLaterCollectionArrivalReadout
open Bandits.Support.ReferenceFirstCollectionCurrentRetainedGate
open Bandits.Support.ReferenceCollectionPhaseHistory

namespace Bandits.Support.ReferenceCollectionOldEpisodeOperationPreservation

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem complete_suffix_member_clockAt
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ReferenceCoordinatorClockDomains.clockAt
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.state ∧
    ReferenceCoordinatorClockDomains.clockAt
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).output.next := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hk
      omega
  | some active =>
      have hc :=
        (ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
          rate source rewards C_star C_h).mp (by rw [hlaunch]; rfl)
      let launchState := ReferenceFirstLaunchNumericalCell.launchState
        rate source rewards C_star C_h hc
      let seed := ReferenceFirstWindowNumericalStream.actualFirstLiveSeed
        rate source rewards C_star C_h hc
      have hcanonical :=
        ReferenceFirstLaunchNumericalCell.correctedLaunch_eq_some_launchState
          rate source rewards C_star C_h hc
      have hrecords := ReferenceCompletePhysicalHistory.completeSuffixRecords_on_launch
        rate source rewards C_star C_h active hlaunch
      let J : Fin (M p) := ActualInitializationPhysicalStep.selectedRowIndex p source
      let rows : CompletePublicTable.CompleteRows p := source.1.2
      let start := ReferenceCompletePhysicalHistory.physicalStart
        rate source rewards C_star C_h
      let initial := active
      have hactiveLaunch : initial = launchState := by
        have hboth := hlaunch.symm.trans hcanonical
        exact Option.some.inj hboth
      have hseed : ReferenceCoordinatorClockDomains.clockAt rows J start initial := by
        have hfirst : initial.coordinator = .first := by
          rw [hactiveLaunch]
          exact seed.coordinatorFirst
        simp [ReferenceCoordinatorClockDomains.clockAt, hfirst]
      have hspan : start + (p.T - start) ≤ p.T := by
        have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
          rate source rewards C_star C_h
        omega
      have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
        rate source rewards C_star C_h active hlaunch
      let run := ReferenceActivePhysicalHorizon.run initial rows J rewards start
        (p.T - start) hspan hmode
      have hclockRun := ReferenceRunClockPreservation.run_clockAt initial rows J rewards
        start (p.T - start) hspan hmode hseed
      have hmember : (R[k.val]'k.isLt) ∈ run.records := by
        rw [← hrecords]
        exact List.getElem_mem k.isLt
      have hrecord := hclockRun.2.2.2 (R[k.val]'k.isLt) hmember
      constructor
      · rw [hrecord.2.2.1, hrecord.2.2.2.1]
        exact hrecord.1
      · rw [hrecord.2.2.1, hrecord.2.2.2.1]
        exact hrecord.2.1

private theorem complete_suffix_cell0
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length) :
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt) = some c := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hcells :=
    ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_cells
      rate rewards C_star C_h source
  cases hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h with
  | none =>
      have hk := k.isLt
      simp only [ReferenceCompletePhysicalHistory.completeSuffixRecords,
        hlaunch, dite_true, List.length_nil] at hk
      omega
  | some active =>
      simp only [hlaunch] at hcells
      obtain ⟨L, hlen, hmap, _hprefix, _hphase⟩ := hcells
      have htake : (R.map (ReferenceFirstCollectionCurrentRetainedGate.cell0 rate))[
          k.val]? = (L.map some)[k.val]? := congrArg
            (fun xs : List (Option (RecordedQueueRun.RoundInput p.K)) => xs[k.val]?) hmap
      simp only [List.getElem?_map] at htake
      have hgetR : R[k.val]? = some (R[k.val]'k.isLt) :=
        List.getElem?_eq_getElem k.isLt
      have hgetLbound : k.val < L.length := by omega
      have hgetL : L[k.val]? = some (L[k.val]'hgetLbound) :=
        List.getElem?_eq_getElem hgetLbound
      rw [hgetR, hgetL] at htake
      simp only [Option.map_some] at htake
      exact ⟨L[k.val]'hgetLbound, Option.some.inj htake⟩

private theorem collectionPostChoice_trace {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hsuccess : (ReferenceActivePhysicalStep.collectionPostChoice
      (x := x) prepared payload ledger started weights).failure = none) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (startedLedger : ReferenceActivePhysicalStep.Ledger rate)
      (decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (finished : ReferenceActivePhysicalStep.Ledger rate)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) =
          some recording ∧
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success startedLedger ∧
      ((ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
          .success (decoded, bank) ∨
        (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
          .rejected (decoded, bank)) ∧
      CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
        finished.pending x.row = .ok clockFinished ∧
      ReferenceActivePhysicalStep.collectionPostChoice
        (x := x) prepared payload ledger started weights =
        ⟨.collection payload finished clockFinished.clock.lastProposal, bank, none,
          some recording, (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).diagnostic⟩ := by
  classical
  unfold ReferenceActivePhysicalStep.collectionPostChoice at hsuccess
  dsimp only at hsuccess
  cases hrecording : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) with
  | none =>
      simp only [hrecording, ReferenceActivePhysicalStep.coordinatorFailure] at hsuccess
      exact False.elim ((Option.some_ne_none _) hsuccess)
  | some recording =>
      cases hstart : CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) with
      | invalid =>
          simp only [hrecording, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at hsuccess
          exact False.elim ((Option.some_ne_none _) hsuccess)
      | rejected rejected =>
          simp only [hrecording, hstart, ReferenceActivePhysicalStep.coordinatorFailure] at hsuccess
          exact False.elim ((Option.some_ne_none _) hsuccess)
      | success startedLedger =>
          have hfinishSuccess :
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                (ReferenceActivePhysicalStep.receiveUp prepared startedLedger)).failure = none := by
            simpa only [hrecording, hstart] using hsuccess
          let cut := ReferenceActivePhysicalStep.receiveUp prepared startedLedger
          have hfinishSuccessCut :
              (ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording
                cut).failure = none := by
            simpa only [cut] using hfinishSuccess
          have htail (decoded : ReferenceActivePhysicalStep.Ledger rate)
              (bank : CoordinatorUpReception.UpDecoderBank p)
              (hreception : cut.result = .success (decoded, bank) ∨
                cut.result = .rejected (decoded, bank)) :
              ∃ (finished : ReferenceActivePhysicalStep.Ledger rate)
                (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
                  finished.pending x.row = .ok clockFinished ∧
                ReferenceActivePhysicalStep.collectionFinish (x := x) payload started recording cut =
                  ⟨.collection payload finished clockFinished.clock.lastProposal, bank, none,
                    some recording, cut.diagnostic⟩ := by
            rcases hreception with haccepted | hrejected
            · have hfinishSuccess' := hfinishSuccessCut
              simp only [ReferenceActivePhysicalStep.collectionFinish, haccepted]
                at hfinishSuccess'
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid =>
                  simp only [hfinish, ReferenceActivePhysicalStep.coordinatorFailure]
                    at hfinishSuccess'
                  exact False.elim ((Option.some_ne_none _) hfinishSuccess')
              | rejected rejected =>
                  simp only [hfinish, ReferenceActivePhysicalStep.coordinatorFailure]
                    at hfinishSuccess'
                  exact False.elim ((Option.some_ne_none _) hfinishSuccess')
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock finished.pending x.row with
                  | error reason =>
                      simp only [hfinish, hclock,
                        ReferenceActivePhysicalStep.coordinatorFailure] at hfinishSuccess'
                      exact False.elim ((Option.some_ne_none _) hfinishSuccess')
                  | ok clockFinished =>
                      have hclockEq : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                          started.clock finished.pending x.row = .ok clockFinished := hclock
                      have hpost := ReferenceActivePhysicalStep.collectionFinish_success
                        (x := x) payload started recording cut decoded finished bank clockFinished
                        (Or.inl haccepted) hfinish hclockEq
                      exact ⟨finished, clockFinished, rfl, hclockEq, hpost⟩
            · have hfinishSuccess' := hfinishSuccessCut
              simp only [ReferenceActivePhysicalStep.collectionFinish, hrejected]
                at hfinishSuccess'
              cases hfinish : CoordinatorCollectionLedger.finishRound decoded with
              | invalid =>
                  simp only [hfinish, ReferenceActivePhysicalStep.coordinatorFailure]
                    at hfinishSuccess'
                  exact False.elim ((Option.some_ne_none _) hfinishSuccess')
              | rejected rejected =>
                  simp only [hfinish, ReferenceActivePhysicalStep.coordinatorFailure]
                    at hfinishSuccess'
                  exact False.elim ((Option.some_ne_none _) hfinishSuccess')
              | success finished =>
                  cases hclock : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                      started.clock finished.pending x.row with
                  | error reason =>
                      simp only [hfinish, hclock,
                        ReferenceActivePhysicalStep.coordinatorFailure] at hfinishSuccess'
                      exact False.elim ((Option.some_ne_none _) hfinishSuccess')
                  | ok clockFinished =>
                      have hclockEq : CoordinatorPhaseClock.finishRound p rate.eta.val x.time
                          started.clock finished.pending x.row = .ok clockFinished := hclock
                      have hpost := ReferenceActivePhysicalStep.collectionFinish_success
                        (x := x) payload started recording cut decoded finished bank clockFinished
                        (Or.inr hrejected) hfinish hclockEq
                      exact ⟨finished, clockFinished, rfl, hclockEq, hpost⟩
          cases hcut : cut.result with
          | invalid =>
              simp only [ReferenceActivePhysicalStep.collectionFinish, cut, hcut,
                ReferenceActivePhysicalStep.coordinatorFailure] at hfinishSuccess
              exact False.elim ((Option.some_ne_none _) hfinishSuccess)
          | success pair =>
              rcases pair with ⟨decoded, bank⟩
              obtain ⟨finished, clockFinished, hfinish, hclock, hpost⟩ :=
                htail decoded bank (Or.inl hcut)
              have hafter := ReferenceActivePhysicalStep.collectionPostChoice_after_start
                prepared payload ledger started weights recording startedLedger
                hrecording hstart
              refine ⟨recording, startedLedger, decoded, bank, finished, clockFinished,
                rfl, hstart, Or.inl hcut, hfinish, hclock, ?_⟩
              rw [hafter, hpost]
          | rejected pair =>
              rcases pair with ⟨decoded, bank⟩
              obtain ⟨finished, clockFinished, hfinish, hclock, hpost⟩ :=
                htail decoded bank (Or.inr hcut)
              have hafter := ReferenceActivePhysicalStep.collectionPostChoice_after_start
                prepared payload ledger started weights recording startedLedger
                hrecording hstart
              refine ⟨recording, startedLedger, decoded, bank, finished, clockFinished,
                rfl, hstart, Or.inr hcut, hfinish, hclock, ?_⟩
              rw [hafter, hpost]

private def actualDispatchOrigin {x : ReferenceActivePhysicalStep.RoundInput p rate} :
    ReferenceActivePhysicalStep.DispatchCut x → Prop
  | .first _ => x.state.coordinator = .first
  | .live r q base _ => x.state.coordinator = .live r q base
  | .collection payload ledger _ _ _ =>
      ∃ saved, x.state.coordinator = .collection payload ledger saved
  | .invalidCollectionCutoff =>
      ∃ payload ledger saved, x.state.coordinator = .collection payload ledger saved
  | .dagger => x.state.coordinator = .dagger

private theorem actual_dispatch_origin (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    actualDispatchOrigin (ReferenceActivePhysicalStep.prepare x).coordinator := by
  change actualDispatchOrigin (ReferenceActivePhysicalStep.dispatch x)
  unfold ReferenceActivePhysicalStep.dispatch
  cases hc : x.state.coordinator with
  | first => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | live r q base => simp only [CoordinatorRoundDispatch.dispatch]; exact hc
  | collection payload ledger saved =>
      simp only [CoordinatorRoundDispatch.dispatch]
      split
      · exact ⟨saved, hc⟩
      · exact ⟨payload, ledger, saved, hc⟩
  | dagger => exact hc

/-! Joint ledger and payload frame for one actual successful collection tail. -/

/-- The recording, START, filtered UP reception (including ordinary
rejection), ledger FINISH and phase FINISH equations are retained together.
Each successful ledger stage carries the original sigma, cutoff and freeze
boundary. -/
abbrev actualCollectionPostChoiceFrames
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ) : Prop :=
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (startedLedger decoded finished : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload started weights) =
          some recording ∧
      CoordinatorCollectionLedger.startRound ledger (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success startedLedger ∧
      ((ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
          .success (decoded, bank) ∨
        (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).result =
          .rejected (decoded, bank)) ∧
      CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val x.time started.clock
        finished.pending x.row = .ok clockFinished ∧
      startedLedger.sigma = ledger.sigma ∧ startedLedger.cutoff = ledger.cutoff ∧
      startedLedger.freezeAt = ledger.freezeAt ∧
      decoded.sigma = ledger.sigma ∧ decoded.cutoff = ledger.cutoff ∧
      decoded.freezeAt = ledger.freezeAt ∧
      finished.sigma = ledger.sigma ∧ finished.cutoff = ledger.cutoff ∧
      finished.freezeAt = ledger.freezeAt ∧
      ReferenceActivePhysicalStep.collectionPostChoice
        (x := x) prepared payload ledger started weights =
        ⟨.collection payload finished clockFinished.clock.lastProposal, bank, none,
          some recording, (ReferenceActivePhysicalStep.receiveUp prepared startedLedger).diagnostic⟩

theorem collectionPostChoice_actual_operation_frames
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (prepared : ReferenceActivePhysicalStep.PreparedRound x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (started : CoordinatorPhaseClock.StartRoundResult p)
    (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ)
    (hsuccess : (ReferenceActivePhysicalStep.collectionPostChoice
      (x := x) prepared payload ledger started weights).failure = none) :
    actualCollectionPostChoiceFrames prepared payload ledger started weights := by
  obtain ⟨recording, startedLedger, decoded, bank, finished, clockFinished,
      hrecording, hstart, hreceive, hfinish, hclock, hpost⟩ :=
    collectionPostChoice_trace prepared payload ledger started weights hsuccess
  have hstartFrame := ReferenceCollectionClockPreservation.ledger_startRound_frame
    ledger startedLedger x.time (ReferenceActivePhysicalStep.collectionEnabled ledger x.time)
    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) hstart
  have hreceiveFrame := ReferenceCollectionClockPreservation.receiveUp_frame
    prepared startedLedger (decoded, bank) hreceive
  have hfinishFrame := ReferenceCollectionClockPreservation.ledger_finishRound_frame
    decoded finished hfinish
  refine ⟨recording, startedLedger, decoded, finished, bank, clockFinished,
    hrecording, hstart, hreceive, hfinish, hclock,
    hstartFrame.1, hstartFrame.2.1, hstartFrame.2.2,
    hreceiveFrame.1.trans hstartFrame.1,
    hreceiveFrame.2.1.trans hstartFrame.2.1,
    hreceiveFrame.2.2.trans hstartFrame.2.2,
    hfinishFrame.1.trans (hreceiveFrame.1.trans hstartFrame.1),
    hfinishFrame.2.1.trans (hreceiveFrame.2.1.trans hstartFrame.2.1),
    hfinishFrame.2.2.trans (hreceiveFrame.2.2.trans hstartFrame.2.2), hpost⟩

/-- The admitted original suffix's actual collection readout supplies its
whole-arm rate and strict started-clock service bit. The phase tag is retained
as its literal constructor test, and all recording/reception/finish frames are
derived from the actual no-failure record. -/
theorem complete_suffix_collectionReadout_operation_frames
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (cell : RecordedQueueRun.RoundInput p.K)
    (hreadout : ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt) = some cell) :
    let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt
    ∃ (payload : ReferenceActivePhysicalStep.Payload rate)
      (ledger : ReferenceActivePhysicalStep.Ledger rate)
      (started : CoordinatorPhaseClock.StartRoundResult p)
      (weights : CanonicalFastSampling.FastArm payload.slowSet → ℝ),
      (match record.output.preparation.coordinator with
      | .collection _ _ _ _ (.continuing _ _ _ _) => True
      | .live registers _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
          0 < registers.payload.sigma.val
      | _ => False) ∧
      ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0 record =
        some ⟨payload, ledger, started, weights⟩ ∧
      cell.rate = payload.rate ∧
      cell.enabled = decide (record.input.time.val + 1 < started.clock.g) ∧
      (∃ (recording : CoordinatorRecordingOperation.Output p)
        (startedLedger decoded finished : ReferenceActivePhysicalStep.Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p)
        (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
        CoordinatorRecorderComplementBridge.run
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
            payload started weights) = some recording ∧
        CoordinatorCollectionLedger.startRound ledger (record.input.time.val + 1)
          (ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
            .success startedLedger ∧
        ((ReferenceActivePhysicalStep.receiveUp record.output.preparation startedLedger).result =
            .success (decoded, bank) ∨
          (ReferenceActivePhysicalStep.receiveUp record.output.preparation startedLedger).result =
            .rejected (decoded, bank)) ∧
        CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
        CoordinatorPhaseClock.finishRound p rate.eta.val record.input.time started.clock
          finished.pending record.input.row = .ok clockFinished ∧
        startedLedger.sigma = ledger.sigma ∧ startedLedger.cutoff = ledger.cutoff ∧
        startedLedger.freezeAt = ledger.freezeAt ∧
        decoded.sigma = ledger.sigma ∧ decoded.cutoff = ledger.cutoff ∧
        decoded.freezeAt = ledger.freezeAt ∧
        finished.sigma = ledger.sigma ∧ finished.cutoff = ledger.cutoff ∧
        finished.freezeAt = ledger.freezeAt ∧
        ReferenceActivePhysicalStep.collectionPostChoice
          record.output.preparation payload ledger started weights =
          ⟨.collection payload finished clockFinished.clock.lastProposal, bank, none,
            some recording,
            (ReferenceActivePhysicalStep.receiveUp record.output.preparation startedLedger).diagnostic⟩) := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt
  have hphase :=
    ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
      rate rewards C_star C_h source k
  obtain ⟨payload, ledger, started, weights, out, _hcall, hpost,
      _hrecording, _henabled, hstartedEnabled, hrate, _hreward, _hrecorded, _hgate, _harrival⟩ :=
    ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call 0 record cell hreadout
  have hsuccess : (ReferenceActivePhysicalStep.collectionPostChoice
      (x := record.input) record.output.preparation payload ledger started weights).failure = none := by
    rw [← hpost]
    exact hphase.1
  have hbranch :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp
      (by rw [hreadout]; rfl)
  have hframes := collectionPostChoice_actual_operation_frames
    record.output.preparation payload ledger started weights hsuccess
  exact ⟨payload, ledger, started, weights, hbranch.2, _hcall, hrate,
    hstartedEnabled, hframes⟩

/-- Actual continuing collection rounds keep the literal old payload and
collection clock through every same-round operation. Their date-indexed cell
is the one in `cell0`, and its enabled bit is the strict test against this same
old ledger's freeze boundary, including the false case. -/
theorem complete_suffix_continuing_collection_operation_frames
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceActivePhysicalStep.collectionInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input
        payload ledger clock cutoff))
    (snapshot : CoordinatorCollectionInteractive.PreparedSnapshot
      (ReferenceActivePhysicalStep.collectionInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input
        payload ledger clock cutoff))
    (boundaryValid : snapshot.clockStarted.clock.g ≤ p.T + 1)
    (scoresChecked : CoordinatorRoundDispatch.collectionCurrentScoresCheck
      (ReferenceActivePhysicalStep.collectionInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input
        payload ledger clock cutoff) = true)
    (hcontinuing : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator =
        .collection payload ledger clock cutoff
          (.continuing core snapshot boundaryValid scoresChecked)) :
    ∃ cell : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt) = some cell ∧
      cell.rate = payload.rate ∧
      cell.enabled = decide (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 < ledger.freezeAt) ∧
      (∃ (started : CoordinatorPhaseClock.StartRoundResult p),
        ReferenceLaterCollectionArrivalReadout.laterCollectionCall 0
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val]'k.isLt) =
          some ⟨payload, ledger, started,
            CoordinatorCollectionInteractive.PreObservationInputs.weights
              (ReferenceActivePhysicalStep.collectionInput
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate source rewards C_star C_h)[k.val]'k.isLt).input
                payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq⟩ ∧
        (∃ (recording : CoordinatorRecordingOperation.Output p)
          (startedLedger decoded finished : ReferenceActivePhysicalStep.Ledger rate)
          (bank : CoordinatorUpReception.UpDecoderBank p)
          (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation
              payload started
              (CoordinatorCollectionInteractive.PreObservationInputs.weights
                (ReferenceActivePhysicalStep.collectionInput
                  ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                    rate source rewards C_star C_h)[k.val]'k.isLt).input
                  payload ledger clock cutoff)
                snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)) =
                some recording ∧
          CoordinatorCollectionLedger.startRound ledger
            (((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled ledger
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).input.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
              .success startedLedger ∧
          ((ReferenceActivePhysicalStep.receiveUp
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation
            startedLedger).result = .success (decoded, bank) ∨
            (ReferenceActivePhysicalStep.receiveUp
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation
              startedLedger).result = .rejected (decoded, bank)) ∧
          CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
          CoordinatorPhaseClock.finishRound p rate.eta.val
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).input.time started.clock
            finished.pending
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).input.row = .ok clockFinished ∧
          startedLedger.sigma = ledger.sigma ∧ startedLedger.cutoff = ledger.cutoff ∧
          startedLedger.freezeAt = ledger.freezeAt ∧
          decoded.sigma = ledger.sigma ∧ decoded.cutoff = ledger.cutoff ∧
          decoded.freezeAt = ledger.freezeAt ∧
          finished.sigma = ledger.sigma ∧ finished.cutoff = ledger.cutoff ∧
          finished.freezeAt = ledger.freezeAt ∧
          ReferenceActivePhysicalStep.collectionPostChoice
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation
            payload ledger started
            (CoordinatorCollectionInteractive.PreObservationInputs.weights
              (ReferenceActivePhysicalStep.collectionInput
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate source rewards C_star C_h)[k.val]'k.isLt).input
                payload ledger clock cutoff)
              snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq) =
            ⟨.collection payload finished clockFinished.clock.lastProposal, bank, none,
              some recording,
              (ReferenceActivePhysicalStep.receiveUp
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation
                startedLedger).diagnostic⟩)) ∧

    ReferenceCoordinatorClockDomains.clockAt
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
      (((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1)
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt).output.next := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt
  have hprepare : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
      .collection payload ledger clock cutoff
        (.continuing core snapshot boundaryValid scoresChecked) := by
    calc
      _ = (ReferenceActivePhysicalStep.step record.input).preparation.coordinator := rfl
      _ = record.output.preparation.coordinator := by rw [← record.output_eq]
      _ = _ := hcontinuing
  have horigin := actual_dispatch_origin record.input
  rw [hprepare] at horigin
  obtain ⟨saved, hstate⟩ := horigin
  have hclocks := complete_suffix_member_clockAt rewards C_star C_h source k
  have hstepClock := ReferenceCollectionClockPreservation.step_clockAt_collection_continuing
    payload ledger saved clock cutoff
    (.continuing core snapshot boundaryValid scoresChecked) hstate hclocks.1 hprepare
  have hphase :=
    ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
      rate rewards C_star C_h source k
  have hnotLive : ¬ ReferenceLaterLiveNumericalReadout.laterLiveDomain 0 record := by
    intro hlive
    rcases hlive with ⟨selected, hselection, _hstart, hassignment, _hordinary⟩
    have hcutoffEq : CoordinatorLiveChoiceRecorderStep.cutoffFromClock p
        snapshot.clockStarted.clock.u =
        some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
      rw [snapshot.clockStarted_frame.1]
      rw [core.clock_cutoff_eq]
      rfl
    have hselection' := hselection
    rw [hcontinuing] at hselection'
    change ReferenceActivePhysicalStep.DispatchCut.selection
        (.collection payload ledger clock cutoff
          (.continuing core snapshot boundaryValid scoresChecked)) = some selected at hselection'
    simp only [ReferenceActivePhysicalStep.DispatchCut.selection, hcutoffEq] at hselection'
    have hselectedEq := Option.some.inj hselection'
    have hselectedEqCutoff := congrArg
      (fun s : ReferenceActivePhysicalStep.Selection record.input => s.view.cutoff) hselectedEq
    have hselectedCutoff : selected.view.cutoff =
        some (CoordinatorCollectionUpRoundStep.localCutoff cutoff) := by
      simpa only [hcutoffEq] using hselectedEqCutoff.symm
    have hbefore := hassignment.2
    rw [hselectedCutoff] at hbefore
    rw [CoordinatorCollectionUpRoundStep.localCutoff_round] at hbefore
    have htimeValid := core.clock_start_time_valid
    change CoordinatorPhaseClock.startRoundTimeValid p record.input.time clock at htimeValid
    unfold CoordinatorPhaseClock.startRoundTimeValid at htimeValid
    have hclockSigma : clock.sigma = some payload.sigma := by
      simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_sigma_eq
    have hclockCutoff : clock.u = some cutoff := by
      simpa [ReferenceActivePhysicalStep.collectionInput] using core.clock_cutoff_eq
    rw [hclockSigma, hclockCutoff] at htimeValid
    have htimeParts : payload.sigma.val < record.input.time.val ∧
        cutoff.val ≤ record.input.time.val := by simpa using htimeValid
    simp only [CoordinatorCollectionUpRoundStep.sourceCutoff] at hbefore
    dsimp [CoordinatorLocalArmChoice.sourceRound] at hbefore
    omega
  have hreadout : ∃ cell : RecordedQueueRun.RoundInput p.K,
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
    rcases hphase.2 with hlive | hcollection
    · exact False.elim (hnotLive hlive)
    · exact hcollection
  obtain ⟨cell, hcell⟩ := hreadout
  have hreadoutResult := complete_suffix_collectionReadout_operation_frames
    rewards C_star C_h source k cell hcell
  rcases hreadoutResult with ⟨outPayload, outLedger, started, weights,
    _hbranch, hcall, hrate, henabled, hframes⟩
  have hfollowers :=
    (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp
      (by rw [hcell]; rfl) |>.1
  have hfollowers' : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate source rewards C_star C_h)[k.val]'k.isLt) := by
    simpa only [record] using hfollowers
  let actualWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights
    (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
    snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq
  have hcallVal :
      (⟨payload, ledger, snapshot.clockStarted, actualWeights⟩ :
        Σ payload : ReferenceActivePhysicalStep.Payload rate,
          ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
            (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) =
      ⟨outPayload, outLedger, started, weights⟩ := by
    apply Option.some.inj
    simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
      ite_eq_left hfollowers', hcontinuing, actualWeights] using hcall
  cases hcallVal
  have hfreeze : snapshot.clockStarted.clock.g = ledger.freezeAt := by
    calc
      snapshot.clockStarted.clock.g = clock.g := by
        simpa [ReferenceActivePhysicalStep.collectionInput] using
          congrArg CoordinatorPhaseClock.ClockRegisters.g snapshot.clockStarted_frame.1
      _ = ledger.freezeAt := by
        have hf : ledger.freezeAt = clock.g := by
          simpa [ReferenceActivePhysicalStep.collectionInput] using core.ledger_freeze_eq
        exact hf.symm
  have henabledOld : cell.enabled = decide (record.input.time.val + 1 < ledger.freezeAt) := by
    rw [henabled, hfreeze]
  obtain ⟨cell0, hcell0⟩ := complete_suffix_cell0 rewards C_star C_h source k
  have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none :=
    (ReferenceLaterLiveNumericalReadout.laterLiveReadout_eq_none_iff 0 record).2 hnotLive
  have hactualCell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record =
      some cell := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveNone, hcell]
  have hcellEq : cell0 = cell := Option.some.inj (hcell0.symm.trans hactualCell)
  subst cell0
  have hstepClock' : ReferenceCoordinatorClockDomains.clockAt
      record.input.rows record.input.selected (record.input.time.val + 1)
      record.output.next := by
    have hstepClockAtStep : ReferenceCoordinatorClockDomains.clockAt
        record.input.rows record.input.selected (record.input.time.val + 1)
        (ReferenceActivePhysicalStep.step record.input).next := by
      simpa only [hprepare] using hstepClock
    rw [record.output_eq]
    exact hstepClockAtStep
  refine ⟨cell, hactualCell, hrate, henabledOld, ?_, hstepClock'⟩
  refine ⟨snapshot.clockStarted, ?_, hframes⟩
  simp only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
    ite_eq_left hfollowers', hcontinuing]

/-- The actual live cutoff constructor initializes the old payload's
collection ledger at its original one-based date. Its subsequent collection
readout, recorder, filtered receiver and FINISH retain that same payload and
clock frame, and the literal cell is retained in the original date slot. -/
theorem complete_suffix_live_cutoff_operation_frames
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (outcome : CoordinatorRoundDispatch.LiveOutcome
      (ReferenceActivePhysicalStep.liveInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate source rewards C_star C_h)[k.val]'k.isLt).input r q base))
    (hcut : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation.coordinator =
        .live r q base outcome) :
    match outcome with
    | .cutoffChosen dispatched _ newLedger _ _ _ _ _ _ _ =>
        let oldLedger := ReferenceActivePhysicalStep.sharedLedger newLedger
        ∃ cell : RecordedQueueRun.RoundInput p.K,
          ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt) = some cell ∧
          cell.rate = r.payload.rate ∧
          cell.enabled = decide (((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 < oldLedger.freezeAt) ∧
          oldLedger.cutoff =
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1 ∧
          ReferenceCoordinatorClockDomains.clockAt
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).input.rows
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).input.selected
              (((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1)
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).output.next ∧
            actualCollectionPostChoiceFrames
              ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                rate source rewards C_star C_h)[k.val]'k.isLt).output.preparation
              r.payload oldLedger dispatched.startResult
              (ReferenceActivePhysicalStep.liveRegistersAt r
                ((ReferenceCompletePhysicalHistory.completeSuffixRecords
                  rate source rewards C_star C_h)[k.val]'k.isLt).input.time).complementWeights
    | _ => True := by
  classical
  let record := (ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h)[k.val]'k.isLt
  cases outcome with
  | clockFailure failure dispatchEq => trivial
  | initializerFailure dispatched startRoundEq checked checkedEq => trivial
  | localFailure dispatched startRoundEq reason => trivial
  | continuingChosen dispatched startRoundEq continuation selection =>
      trivial
  | cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
      initializationDomainValid clockEq pendingEq noAssignment selection =>
      have hprepareStruct : ReferenceActivePhysicalStep.prepare record.input =
          record.output.preparation := by
        calc
          ReferenceActivePhysicalStep.prepare record.input =
              (ReferenceActivePhysicalStep.step record.input).preparation := rfl
          _ = record.output.preparation := by rw [← record.output_eq]
      have hprepare : (ReferenceActivePhysicalStep.prepare record.input).coordinator =
          .live r q base
            (.cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
              initializationDomainValid clockEq pendingEq noAssignment selection) := by
        rw [hprepareStruct]
        exact hcut
      have horigin := actual_dispatch_origin record.input
      rw [hprepare] at horigin
      have hstate : record.input.state.coordinator = .live r q base := horigin
      have hclocks := complete_suffix_member_clockAt rewards C_star C_h source k
      have hsourceCutoff :=
        Bandits.Support.complete_live_cutoff_post_choice
          rate rewards C_star C_h source k r q base hstate
      obtain ⟨hauditPrepare, _hauditBranch⟩ := hsourceCutoff
      have hchosenEq :
          .cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
            initializationDomainValid clockEq pendingEq noAssignment selection =
          CoordinatorRoundDispatch.dispatchLive
            (ReferenceActivePhysicalStep.liveInput record.input r q base) := by
        have houter := hprepare.symm.trans hauditPrepare
        injection houter with _ _ _ hchosen
      have hcutoffPhase :=
        ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
          rate rewards C_star C_h source k
      have hnotLive : ¬ ReferenceLaterLiveNumericalReadout.laterLiveDomain 0 record := by
        intro hlive
        rcases hlive with ⟨selectedLive, hselection, _hstart, hassignment, _hordinary⟩
        have hselection' := hselection
        rw [hcut] at hselection'
        change ReferenceActivePhysicalStep.DispatchCut.selection
            (.live r q base
              (.cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
                initializationDomainValid clockEq pendingEq noAssignment selection)) =
            some selectedLive at hselection'
        simp only [ReferenceActivePhysicalStep.DispatchCut.selection,
          ReferenceActivePhysicalStep.selectionAt] at hselection'
        have hselected := Option.some.inj hselection'
        have hcutoffEq := congrArg
          (fun s : ReferenceActivePhysicalStep.Selection record.input => s.view.cutoff) hselected
        have hcutoffSel : selectedLive.view.cutoff =
            CoordinatorLiveChoiceRecorderStep.cutoffFromClock p dispatched.startResult.clock.u :=
          hcutoffEq.symm
        have hclockU : dispatched.startResult.clock.u = some record.input.time := by
          have hu := congrArg CoordinatorPhaseClock.ClockRegisters.u clockEq
          have hu' : dispatched.startResult.clock.u =
              some (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).time := by
            simpa only [ReferenceActivePhysicalStep.liveInput,
              CoordinatorPhaseClock.ClockRegisters.u] using hu
          rw [(ReferenceActivePhysicalStep.liveRegistersAt_fields r record.input.time).2.2.2.2.2]
            at hu'
          exact hu'
        have hbefore := hassignment.2
        rw [hcutoffSel, CoordinatorLiveChoiceRecorderStep.cutoffRoundFromClock,
          hclockU] at hbefore
        dsimp [CoordinatorLocalArmChoice.sourceRound] at hbefore
        simp at hbefore
      have hreadout : ∃ cell : RecordedQueueRun.RoundInput p.K,
          ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 record = some cell := by
        rcases hcutoffPhase.2 with hlive | hcollection
        · exact False.elim (hnotLive hlive)
        · exact hcollection
      obtain ⟨cell, hcell⟩ := hreadout
      have hreadoutResult := complete_suffix_collectionReadout_operation_frames
        rewards C_star C_h source k cell hcell
      rcases hreadoutResult with ⟨outPayload, outLedger, started, weights,
        _hbranch, hcall, hrate, henabled, _hframes⟩
      have hfollowers :=
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp
          (by rw [hcell]; rfl) |>.1
      have hfollowers' : ReferenceLaterCollectionArrivalReadout.preparedFollowersUnoccupied
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate source rewards C_star C_h)[k.val]'k.isLt) := by
        simpa only [record] using hfollowers
      have hsigma :=
        (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_domain 0 record).mp
          (by rw [hcell]; rfl) |>.2
      have hpositive : 0 < r.payload.sigma.val := by
        rw [hcut] at hsigma
        exact hsigma
      have hnewFields := CoordinatorStartRoundCutoffDispatch.collectionStartLedger_fields
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base record.input.time
      have hledgerEq' : newLedger =
          CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time)
            (ReferenceActivePhysicalStep.liveOwnedAt r q record.input.time) base record.input.time := by
        simpa only [ReferenceActivePhysicalStep.liveInput,
          ReferenceActivePhysicalStep.liveOwnedAt,
          ReferenceActivePhysicalStep.liveRegistersAt] using ledgerEq
      rw [← hledgerEq'] at hnewFields
      have hnewCutoff : newLedger.cutoff = record.input.time.val + 1 := hnewFields.2.2.1
      have hnewFreeze : newLedger.freezeAt = r.gridBoundary := hnewFields.2.2.2.1
      have hshared := ReferenceActivePhysicalStep.sharedLedger_fields newLedger
      have hsharedCutoff :
          (ReferenceActivePhysicalStep.sharedLedger newLedger).cutoff =
            record.input.time.val + 1 := hshared.2.2.1.trans hnewCutoff
      have hsharedFreeze :
          (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt = r.gridBoundary :=
        hshared.2.2.2.1.trans hnewFreeze
      have hclockAtInput := hclocks.1
      simp only [record, ReferenceCoordinatorClockDomains.clockAt, hstate] at hclockAtInput
      have hstartGrid : dispatched.startResult.clock.g = r.gridBoundary := by
        calc
          dispatched.startResult.clock.g =
              (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).priorClock.g := by
                have hg := congrArg CoordinatorPhaseClock.ClockRegisters.g clockEq
                simpa only [ReferenceActivePhysicalStep.liveInput,
                  CoordinatorPhaseClock.ClockRegisters.g] using hg
          _ = r.priorClock.g := by
            rw [(ReferenceActivePhysicalStep.liveRegistersAt_fields r record.input.time).2.1]
          _ = r.gridBoundary := hclockAtInput.2.2.2.2.1.symm
      have hfreezeStart : dispatched.startResult.clock.g =
          (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt :=
        hstartGrid.trans hsharedFreeze.symm
      let liveWeights :=
        (ReferenceActivePhysicalStep.liveRegistersAt r record.input.time).complementWeights
      have hcallVal :
          (⟨r.payload, ReferenceActivePhysicalStep.sharedLedger newLedger,
            dispatched.startResult, liveWeights⟩ :
            Σ payload : ReferenceActivePhysicalStep.Payload rate,
              ReferenceActivePhysicalStep.Ledger rate × CoordinatorPhaseClock.StartRoundResult p ×
                (CanonicalFastSampling.FastArm payload.slowSet → ℝ)) =
          ⟨outPayload, outLedger, started, weights⟩ := by
        apply Option.some.inj
        simpa only [ReferenceLaterCollectionArrivalReadout.laterCollectionCall,
          ite_eq_left hfollowers', hcut, ite_eq_left hpositive, record,
          ReferenceActivePhysicalStep.liveRegistersAt_fields, liveWeights] using hcall
      cases hcallVal
      have hsuccess :
          (ReferenceActivePhysicalStep.collectionPostChoice
            record.output.preparation r.payload
            (ReferenceActivePhysicalStep.sharedLedger newLedger) dispatched.startResult
            liveWeights).failure = none := by
        have hcomplete :=
          ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
            rate rewards C_star C_h source
        have hselected := (hcomplete.1 k).2.1
        have hselectionNonempty :
            (ReferenceActivePhysicalStep.DispatchCut.live r q base
              (.cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
                initializationDomainValid clockEq pendingEq noAssignment selection)).selection ≠
              none := by
          simpa only [hcut] using hselected
        have hobs := ReferenceActivePhysicalStep.observeCoordinator_live_equation
          record.output.preparation r q base
          (.cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
            initializationDomainValid clockEq pendingEq noAssignment selection) hcut
        have hobsEq : record.output.preparation.observeCoordinator =
            ReferenceActivePhysicalStep.collectionPostChoice record.output.preparation r.payload
              (ReferenceActivePhysicalStep.sharedLedger newLedger) dispatched.startResult
              liveWeights := by
          simpa only [ite_eq_right hselectionNonempty] using hobs
        have hprepareEq : record.output.preparation =
            (ReferenceActivePhysicalStep.step record.input).preparation := by
          rw [← hprepareStruct]
          rfl
        have houtputEq : record.output.coordinator =
            ReferenceActivePhysicalStep.collectionPostChoice record.output.preparation r.payload
              (ReferenceActivePhysicalStep.sharedLedger newLedger) dispatched.startResult
              liveWeights := by
          rw [record.output_eq]
          rw [hprepareEq] at hobsEq
          exact hobsEq
        rw [← houtputEq]
        exact hcutoffPhase.1
      have hframes := collectionPostChoice_actual_operation_frames
        record.output.preparation r.payload
        (ReferenceActivePhysicalStep.sharedLedger newLedger) dispatched.startResult liveWeights hsuccess
      have henabledOld : cell.enabled = decide
          (record.input.time.val + 1 <
            (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt) := by
        rw [henabled, hfreezeStart]
      have hliveNone : ReferenceLaterLiveNumericalReadout.laterLiveReadout 0 record = none :=
        (ReferenceLaterLiveNumericalReadout.laterLiveReadout_eq_none_iff 0 record).2 hnotLive
      have hactualCell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate record =
          some cell := by
        simp [ReferenceFirstCollectionCurrentRetainedGate.cell0, hliveNone, hcell]
      have hstepClock := ReferenceCollectionClockPreservation.step_clockAt_live_cutoff
        r q base
        (.cutoffChosen dispatched startRoundEq newLedger initializationEq ledgerEq
          initializationDomainValid clockEq pendingEq noAssignment selection)
        hstate hclocks.1 hprepare
      have hstepClock' : ReferenceCoordinatorClockDomains.clockAt
          record.input.rows record.input.selected (record.input.time.val + 1)
          record.output.next := by
        have hstep : ReferenceCoordinatorClockDomains.clockAt record.input.rows
            record.input.selected (record.input.time.val + 1)
            (ReferenceActivePhysicalStep.step record.input).next := by
          simpa only [hprepare] using hstepClock
        rw [record.output_eq]
        exact hstep
      refine ⟨cell, hactualCell, hrate, henabledOld, hsharedCutoff, ?_⟩
      exact ⟨hstepClock', hframes⟩

/-! A LIVE input at the actual successor forces its immediate original
predecessor to be a LIVE numerical cell. The adjacent equation is taken from
the complete suffix, so the first installed LIVE successor is included. -/
theorem complete_suffix_live_successor_predecessor_enabled
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (source : BootstrapPrivateRoundStreams.SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h).length)
    (hk : 0 < k.val)
    (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
    (base : Fin (p.m - 1) → ℕ)
    (hstate : ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h)[k.val]'k.isLt).input.state.coordinator =
        .live r q base) :
    let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate source rewards C_star C_h
    ∃ cell : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionCurrentRetainedGate.cell0 rate
        (records[k.val - 1]'(by
          have hprev : k.val - 1 < k.val := by omega
          simpa only [records] using hprev.trans k.isLt)) = some cell ∧
      cell.enabled = true := by
  classical
  let records := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate source rewards C_star C_h
  have hprevBound : k.val - 1 < records.length := by
    have hprev : k.val - 1 < k.val := by omega
    simpa only [records] using hprev.trans k.isLt
  let i : Fin records.length := ⟨k.val - 1, hprevBound⟩
  let previous := records[i.val]'i.isLt
  have hindex : i.val + 1 = k.val := by
    dsimp [i]
    omega
  have hadjacent :=
    ReferenceCompleteLaterLiveComplementPrefixReplay.complete_adjacent
      rewards C_star C_h source i.val (by rw [hindex]; exact k.isLt)
  have hadjacent' :
      (records[k.val]'k.isLt).input.state = previous.output.next := by
    simpa only [records, i, previous, hindex] using hadjacent
  have hpreviousLive : previous.output.next.coordinator = .live r q base := by
    have hcoord := congrArg
      (fun state : ReferenceActivePhysicalStep.State p rate => state.coordinator) hadjacent'
    exact hcoord.symm.trans hstate
  have hphase :=
    ReferenceCompleteOriginalCalendarCellPresence.complete_original_calendar_phase_exhaustion
      rate rewards C_star C_h source i
  have hphasePrevious :
      previous.output.coordinator.failure = none ∧
        (ReferenceLaterLiveNumericalReadout.laterLiveDomain 0 previous ∨
          ∃ d, ReferenceLaterCollectionArrivalReadout.laterCollectionReadout 0 previous = some d) := by
    simpa only [previous, i, records] using hphase
  rcases hphasePrevious.2 with hlive | ⟨d, hcollection⟩
  · have hsome := (ReferenceLaterLiveNumericalReadout.laterLiveReadout_domain
      0 previous).2 hlive
    obtain ⟨cell, hreadout⟩ := Option.isSome_iff_exists.mp hsome
    have hcell : ReferenceFirstCollectionCurrentRetainedGate.cell0 rate previous =
        some cell := by
      simp only [ReferenceFirstCollectionCurrentRetainedGate.cell0, hreadout,
        Option.some_or]
    have hnumerical := ReferenceLaterLiveNumericalReadout.laterLiveReadout_numerical
      0 previous cell hreadout
    exact ⟨cell, hcell, hnumerical.1⟩
  · obtain ⟨payload, ledger, started, weights, out, hcall⟩ :=
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout_call
        0 previous d hcollection
    have hdiagnostics : previous.output.coordinator =
        ReferenceActivePhysicalStep.collectionPostChoice previous.output.preparation
          payload ledger started weights := by
      simpa only [ReferenceActivePhysicalHorizon.RoundRecord.coordinatorDiagnostics]
        using hcall.2.1
    have hsuccess :
        (ReferenceActivePhysicalStep.collectionPostChoice previous.output.preparation
          payload ledger started weights).failure = none := by
      rw [← hdiagnostics]
      exact hphasePrevious.1
    rcases collectionPostChoice_actual_operation_frames
        previous.output.preparation payload ledger started weights hsuccess with
      ⟨recording, startedLedger, decoded, finished, bank, clockFinished,
        _hrecording, _hstart, _hreceive, _hfinish, _hclock,
        _hstartedSigma, _hstartedCutoff, _hstartedFreeze,
        _hdecodedSigma, _hdecodedCutoff, _hdecodedFreeze,
        _hfinishedSigma, _hfinishedCutoff, _hfinishedFreeze, hpost⟩
    have hstepNext : previous.output.next.coordinator =
        previous.output.coordinator.configuration := by
      rw [previous.output_eq]
      exact (ReferenceActivePhysicalStep.step_next_fields previous.input).1
    have hnextCollection : previous.output.next.coordinator =
        .collection payload finished clockFinished.clock.lastProposal := by
      rw [hdiagnostics, hpost] at hstepNext
      simpa only using hstepNext
    have himpossible := hpreviousLive.symm.trans hnextCollection
    cases himpossible

end Bandits.Support.ReferenceCollectionOldEpisodeOperationPreservation

end
