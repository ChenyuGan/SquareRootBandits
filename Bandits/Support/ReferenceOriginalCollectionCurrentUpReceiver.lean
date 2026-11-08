/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceOriginalKthCollectionSourceSections

import Mathlib.Tactic

/-!
# Actual original collection current-UP receiver

Sources: `sources/zip4/manuscript/06_interruptions.tex:477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:180-191`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:151-157`.

This module joins an actual original-source collection choice to its current
UP receiver, including the live cutoff record. The choice, checked recording,
started ledger, diagnostic, offer, awaiting predicates, and matching-word
acceptance all come from the same complete-suffix record.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceOriginalCollectionCurrentUpReceiver

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := ReferenceOriginalKthCollectionSourceSections.SourceInput
abbrev Record (p : Parameters) (rate : RateInput p) :=
  ReferenceCompletePhysicalHistory.RoundRecord p rate
abbrev Choice {p : Parameters} (rate : RateInput p) :=
  ReferenceCollectionSegmentExtraction.Choice rate
abbrev UpRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceCollectionPhaseHistory.UpRecord p rate

variable {p : Parameters}
variable (rate : RateInput p)
variable (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
variable (C_star C_h : ℝ)

private theorem complete_suffix_get_time_nat
    (z : SourceInput p) (n : ℕ)
    (hn : n < (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ((ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).get ⟨n, hn⟩).input.time.val =
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + n := by
  have htimes := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
    rate z rewards C_star C_h
  have hget := congrArg (fun xs : List ℕ => xs[n]?) htimes
  have hn' : n < p.T - ReferenceCompletePhysicalHistory.physicalStart
      rate z rewards C_star C_h := by
    simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hn
  have hrange := List.getElem?_range'
    (s := ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
    (step := 1) hn'
  simpa [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
    List.getElem?_eq_getElem hn, hrange] using hget

private theorem complete_suffix_source_fields
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let r := (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h)[k.val]'k.isLt
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.rewards = rewards := by
  classical
  by_cases hnone : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate z rewards C_star C_h = none
  · have hempty : ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h = [] := by
      simp [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone]
    rw [hempty] at k
    exact Fin.elim0 k
  · let active := ReferenceCompletePhysicalHistory.correctedLaunchPayload
      rate z rewards C_star C_h hnone
    have hspan : ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h +
        (p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h) ≤ p.T := by
      have hs := ReferenceCompletePhysicalHistory.physicalStart_le_T
        rate z rewards C_star C_h
      omega
    have hmode := ReferenceCompletePhysicalHistory.activeMode_of_launch_eq_some
      rate z rewards C_star C_h active
      (ReferenceCompletePhysicalHistory.correctedLaunch_eq_some_payload
        rate z rewards C_star C_h hnone)
    let run := ReferenceActivePhysicalHorizon.run active z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards
      (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      hspan hmode
    have hlen : k.val < run.records.length := by
      simpa [run, ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone,
        ReferenceCompletePhysicalHistory.correctedSuffixRun, active] using k.isLt
    have hfields := ReferenceActivePhysicalHorizon.run_record_inputs
      active z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)
      rewards (ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      (p.T - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h)
      hspan hmode (run.records[k.val]'hlen) (List.getElem_mem hlen)
    simpa [ReferenceCompletePhysicalHistory.completeSuffixRecords, hnone,
      ReferenceCompletePhysicalHistory.correctedSuffixRun, active, run] using hfields

private theorem actual_record_at_complete_suffix
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input.time z =
      some ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt) := by
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
    rate z rewards C_star C_h
  let r := R[k.val]'k.isLt
  have htime := complete_suffix_get_time_nat rate rewards C_star C_h z k.val k.isLt
  change r.input.time.val =
    ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h + k.val at htime
  have hstart : ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h ≤
      r.input.time.val := by omega
  have hindex : r.input.time.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h = k.val := by
    omega
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord
  rw [ite_eq_left hstart, hindex]
  simp only [List.getElem?_eq_getElem k.isLt]

private theorem choice_executed_tail
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (c : Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x = some
      ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  classical
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hselection : prepared.coordinator.selection ≠ none := by
    intro hnone
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    simp [prepared, hnone] at hchoice
  have hchoiceCut : ReferenceCollectionSegmentExtraction.choiceOfCut
      prepared.coordinator = some c := by
    unfold ReferenceCollectionSegmentExtraction.choice at hchoice
    simp only [prepared, ite_eq_right hselection] at hchoice
    exact hchoice
  cases hcoord : prepared.coordinator with
  | live registers owned base outcome =>
      cases outcome with
      | cutoffChosen dispatched hstart ledger hinitialization hledger hvalid hclock
          hpending hnone selected =>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
          cases Option.some.inj hchoiceCut
          have hsel : prepared.coordinator.selection ≠ none := hselection
          rw [hcoord] at hsel
          simp [ReferenceCollectionPhaseHistory.executedTail, prepared,
            hcoord, hsel]
      | continuingChosen dispatched hstart continuation selected =>
          simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
      | clockFailure failure heq =>
          simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
      | initializerFailure dispatched hstart checked heq =>
          simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
      | localFailure dispatched hstart reason =>
          simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
  | collection payload ledger clock cutoff outcome =>
      cases outcome with
      | continuing core snapshot boundary scores =>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
          cases Option.some.inj hchoiceCut
          have hsel : prepared.coordinator.selection ≠ none := hselection
          rw [hcoord] at hsel
          simp [ReferenceCollectionPhaseHistory.executedTail, prepared,
            hcoord, hsel]
      | _ =>
          simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
  | first outcome =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
  | invalidCollectionCutoff =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut
  | dagger =>
      simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hchoiceCut

private theorem choice_collection_payload
    {x : ReferenceActivePhysicalStep.RoundInput p rate}
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (c : Choice rate)
    (hstate : x.state.coordinator = .collection payload ledger saved)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    c.payload = payload := by
  classical
  unfold ReferenceCollectionSegmentExtraction.choice at hchoice
  by_cases hselection : (ReferenceActivePhysicalStep.prepare x).coordinator.selection = none
  · simp [hselection] at hchoice
  · simp only [hselection, ↓reduceIte] at hchoice
    simp only [ReferenceActivePhysicalStep.prepare, ReferenceActivePhysicalStep.dispatch,
      hstate] at hchoice
    split at hchoice
    · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
      let clock := ReferenceActivePhysicalStep.collectionClock payload ledger saved cutoff
      change ReferenceCollectionSegmentExtraction.choiceOfCut
          (.collection payload ledger clock cutoff
            (CoordinatorRoundDispatch.dispatchCollection
              (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff))) =
            some c at hchoice
      cases hd : CoordinatorRoundDispatch.dispatchCollection
          (ReferenceActivePhysicalStep.collectionInput x payload ledger clock cutoff)
        <;> simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hd] at hchoice
      all_goals
        exact congrArg ReferenceCollectionSegmentExtraction.Choice.payload
          hchoice.symm
    · simp [ReferenceCollectionSegmentExtraction.choiceOfCut] at hchoice

private theorem started_ledger_frame
    (before started : ReferenceActivePhysicalStep.Ledger rate)
    (time : ℕ) (enabled : Bool) (raw : Option (Fin p.K × ℕ))
    (hstart : CoordinatorCollectionLedger.startRound before time enabled raw =
      .success started) :
    started.pending = before.pending ∧ started.sigma = before.sigma := by
  have hcand := CollectionCheckedExecution.startRound_success_candidate
    before started time enabled raw hstart
  rw [hcand]
  simp [CoordinatorCollectionLedger.startRoundCandidate]

private theorem actual_choice_receiver
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length)
    (c : Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).input = some c) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
      (received : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p)
      (finished : ReferenceActivePhysicalStep.Ledger rate)
      (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
      ReferenceCollectionPhaseHistory.executedTail
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input =
          some ⟨c.payload, c.preLedger, c.started, c.weights⟩ ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val]'k.isLt).input)
          c.payload c.started c.weights) = some recording ∧
      CoordinatorCollectionLedger.startRound c.preLedger
        (((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val]'k.isLt).input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success L ∧
      L.pending = c.preLedger.pending ∧ L.sigma = c.preLedger.sigma ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger?
        (x := ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val]'k.isLt).input L) = true ∧
      ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).output.coordinator.up = some d ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input L ∧
      ReferenceCollectionPhaseHistory.Tail.reception
        (⟨c.payload, c.preLedger, c.started, c.weights⟩ :
          ReferenceCollectionPhaseHistory.Tail
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val]'k.isLt).input) =
        some (L, ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val]'k.isLt).input) L) ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val]'k.isLt).input) L).result ≠ .invalid ∧
      (((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val]'k.isLt).input) L).result =
            .success (received, bank)) ∨
        ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare
            ((ReferenceCompletePhysicalHistory.completeSuffixRecords
              rate z rewards C_star C_h)[k.val]'k.isLt).input) L).result =
            .rejected (received, bank))) ∧
      CoordinatorCollectionLedger.finishRound received = .success finished ∧
      CoordinatorPhaseClock.finishRound p rate.eta.val
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input.time c.started.clock
        finished.pending
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input.row = .ok clockFinished ∧
      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare
          ((ReferenceCompletePhysicalHistory.completeSuffixRecords
            rate z rewards C_star C_h)[k.val]'k.isLt).input) ∧
      d.input.upDecoderBank =
        ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input.state.upDecoderBank ∧
      d.input.time = ((ReferenceCompletePhysicalHistory.completeSuffixRecords
        rate z rewards C_star C_h)[k.val]'k.isLt).input.time ∧
      d.input.affineSample =
        (let input := ((ReferenceCompletePhysicalHistory.completeSuffixRecords
          rate z rewards C_star C_h)[k.val]'k.isLt).input
        ((input.rows input.selected).2 input.time).2
          (1, CoordinatorUpMeasurability.selectedChannelFollower
            ((input.rows input.selected).2 input.time))) := by
  classical
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]'k.isLt
  have hordinary : r.output.next.coordinator ≠ .dagger := by
    exact (ReferenceCompleteCoordinatorPhaseExhaustion.complete_coordinator_phase_exhaustion
      rate rewards C_star C_h z).1 k |>.2.2.2.2
  have htail := choice_executed_tail rate c hchoice
  have horigin := ReferenceCollectionPhaseHistory.executedTail_origin htail
  rcases horigin with ⟨_hlater, hbranches⟩
  rcases hbranches with ⟨hcut, _htailPending⟩ | ⟨_hnotcut, payload, ledger, saved,
    hstate, _htailLedger⟩
  · obtain ⟨tailCut, recording, L, d, received, bank, finished, clockFinished,
      htailCut, hpost, hsiteTail, htailPending', htailSigma,
      htailCutoff, htailCursor, htailPhase, hstartedPending, hrecording,
      hstart, hLpending, hLsigma, hLcutoff, hLcursor, hcheck, hinput,
      hdiagnostic, htailReception, hnotInvalid, hresultCases, hfinish,
      hclock, hdecoder, hraw, hparsed, hlocal, hexpected, hrawMatches,
      hbank, htime, hsample, hobservation, hwrong⟩ :=
      ReferenceCutoffUpReceiverLocal.actual_ordinary_cutoff_up_receiver r hcut hordinary
    have htailEq : tailCut = ⟨c.payload, c.preLedger, c.started, c.weights⟩ :=
      Option.some.inj (htailCut.symm.trans htail)
    subst tailCut
    have hframe := started_ledger_frame rate c.preLedger _ _ _ _ hstart
    exact ⟨recording, L, d, received, bank, finished, clockFinished,
      htail, hrecording, hstart, hframe.1, hframe.2, hsiteTail, hcheck,
      hdiagnostic, hinput, htailReception, hnotInvalid, hresultCases,
      hfinish, hclock, hraw, hexpected, hbank, htime, hsample⟩
  · have hpayload := choice_collection_payload rate payload ledger saved c hstate hchoice
    have hchoiceFrame := ReferenceCollectionSegmentExtraction.choice_collection_pre
      r.input payload ledger saved c hstate hchoice
    have hstateC : r.input.state.coordinator =
        .collection c.payload c.preLedger saved := by
      rw [hpayload, hchoiceFrame.1]
      exact hstate
    have htailC : ReferenceCollectionPhaseHistory.executedTail r.input =
        some ⟨c.payload, c.preLedger, c.started, c.weights⟩ := htail
    have hreceiver := ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver
      r c.payload c.preLedger saved ⟨c.payload, c.preLedger, c.started, c.weights⟩
      hstateC htailC hordinary
    obtain ⟨recording, L, d, hrecording, hstart, hsite, hcheck, hdiagnostic,
      hinput, htailReception, hnotInvalid, received, bank, finished, clockFinished,
      hreceived, hfinish, hclock, hdecoder, hraw, hparsed, hlocal, hexpected,
      hrawMatches, hbank, htime, hsample, hobservation, hwrong⟩ := hreceiver
    have hframe := started_ledger_frame rate c.preLedger _ _ _ _ hstart
    exact ⟨recording, L, d, received, bank, finished, clockFinished,
      htailC, hrecording, hstart, hframe.1, hframe.2, hsite, hcheck,
      hdiagnostic, hinput, htailReception, hnotInvalid,
      hreceived, hfinish, hclock, hraw, hexpected, hbank, htime, hsample⟩

private theorem offered_word_eq_source_encoding
    (U : OrdinaryMessageCodec.UpRecord
      (ReferencePrelaunchFollower.codecParams p rate.eta)) :
    ReferenceCollectionUpFailureReadoutV2.enc rate U =
      ActiveFollowerArmChoice.offeredUpWord rate.eta U := by
  unfold ReferenceCollectionUpFailureReadoutV2.enc
    ReferenceFirstCollectionFormedUpOfferReceiver.encodedUpOfferWord
    ActiveFollowerArmChoice.offeredUpWord
  have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
  cases hcodec
  rfl

/-- At every actual original complete-suffix index, inspect its own choice.
When that choice is present, the result retains the exact recorded start and
receiver call. In the literal selected, ordinary, unoccupied current-DOWN
branch, it derives the current UP awaiting predicates and matching-raw
acceptance, including the cutoff choice made from a LIVE input.
-/
theorem actual_collection_current_up_receiver
    (z : SourceInput p)
    (k : Fin (ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h).length) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords
      rate z rewards C_star C_h
    let r := R[k.val]'k.isLt
    ReferenceCollectionSegmentExtraction.choice r.input = none ∨
      ∃ c : Choice rate,
        ReferenceCollectionSegmentExtraction.choice r.input = some c ∧
        ∃ birthIndex : Fin R.length,
          birthIndex.val < k.val ∧
          ReferenceAssignmentPayloadPersistence.InstallationBirth
            (R[birthIndex.val]'birthIndex.isLt) c.payload ∧
          c.preLedger.sigma = c.payload.sigma.val + 1 ∧
          r.input.rows = z.1.2 ∧
          r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
          r.input.rewards = rewards ∧
          ∃ (recording : CoordinatorRecordingOperation.Output p)
            (L : ReferenceActivePhysicalStep.Ledger rate)
            (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
            (received : ReferenceActivePhysicalStep.Ledger rate)
            (bank : CoordinatorUpReception.UpDecoderBank p)
            (finished : ReferenceActivePhysicalStep.Ledger rate)
            (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
            ReferenceCollectionPhaseHistory.executedTail r.input =
              some ⟨c.payload, c.preLedger, c.started, c.weights⟩ ∧
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare r.input)
                c.payload c.started c.weights) = some recording ∧
            CoordinatorCollectionLedger.startRound c.preLedger (r.input.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                .success L ∧
            L.pending = c.preLedger.pending ∧ L.sigma = c.preLedger.sigma ∧
            ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
            CoordinatorUpReception.receptionInputCheck
              (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
            r.output.coordinator.up = some d ∧
            d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
            ReferenceCollectionPhaseHistory.Tail.reception
              (⟨c.payload, c.preLedger, c.started, c.weights⟩ :
                ReferenceCollectionPhaseHistory.Tail r.input) =
              some (L, ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare r.input) L) ∧
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result ≠ .invalid ∧
            (((ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare r.input) L).result =
                  .success (received, bank)) ∨
              ((ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare r.input) L).result =
                  .rejected (received, bank))) ∧
            CoordinatorCollectionLedger.finishRound received = .success finished ∧
            CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time c.started.clock
              finished.pending r.input.row = .ok clockFinished ∧
            d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
            d.expected = ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare r.input) ∧
            d.input.upDecoderBank = r.input.state.upDecoderBank ∧
            d.input.time = r.input.time ∧
            d.input.affineSample =
              ((r.input.rows r.input.selected).2 r.input.time).2
                (1, CoordinatorUpMeasurability.selectedChannelFollower
                  ((r.input.rows r.input.selected).2 r.input.time)) ∧
            ∀ (i : Fin (p.m - 1)) (state : ReferencePrelaunchFollower.State p rate.eta)
              (memory : ActiveFollowerLifecycle.LocalMemory p),
              ReferenceActivePhysicalStep.upSenderIndex r.input = i →
              (ReferenceFollowerFixedReply.actualChoice r i).configuration =
                .ordinary state memory →
              state.status = ActiveRoundActions.FollowerStatus.unoccupied →
              state.lastDown = some (c.payload.downRecord i) →
              PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
                PublicDiscreteDraws.upSlot →
              i ∈ c.preLedger.pending →
              ∃ U : OrdinaryMessageCodec.UpRecord
                  (ReferencePrelaunchFollower.codecParams p rate.eta),
                ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
                  (r.input.state.activations i) r.input.time state = .offer U ∧
                U.val = ActiveFollowerQueueOperation.upOfferFields state ∧
                U.val.sigma = (c.payload.downRecord i).val.sigma ∧
                0 < U.val.sigma ∧
                ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare r.input) =
                    some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                d.input.selectedFollower = i ∧
                CoordinatorUpReception.receptionGate d.input ∧
                ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i U ∧
                ReferenceCompleteAwaitedBatchSourceCoverage.originalUpAwaitedCallAt
                  rate r i U ∧
                ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt
                  rate rewards C_star C_h z i U r.input.time ∧
                CoordinatorCollectionLedger.acceptUpCheck L i U = true ∧
                (d.raw = some (ReferenceCollectionUpFailureReadoutV2.enc rate U) →
                  ReferenceCollectionPhaseHistory.AcceptedUp r.input i U ∧
                  ∃ saved : Option (Fin p.T × Bool),
                    r.output.next.coordinator = .collection c.payload finished saved ∧
                    i ∉ finished.pending) := by
  classical
  dsimp only
  let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate z rewards C_star C_h
  let r := R[k.val]'k.isLt
  by_cases hchoiceNone : ReferenceCollectionSegmentExtraction.choice r.input = none
  · exact Or.inl hchoiceNone
  · obtain ⟨c, hchoiceEq⟩ := Option.ne_none_iff_exists.mp hchoiceNone
    have hchoice : ReferenceCollectionSegmentExtraction.choice r.input = some c :=
      hchoiceEq.symm
    obtain ⟨birthIndex, hbirthIndex, hbirth, hassignment, hbirthSigma,
      hbirthCutoff, hbase⟩ :=
      ReferenceAssignmentRetainedBirthProvenance.complete_collection_choice_birth_provenance
        rate rewards C_star C_h z k c (by simpa [R, r] using hchoice)
    have hsourceFields := complete_suffix_source_fields rate rewards C_star C_h z k
    obtain ⟨recording, L, d, received, bank, finished, clockFinished,
      htail, hrecording, hstart, hLpending, hLsigma, hsite, hcheck, hdiagnostic,
      hinput, htailReception, hnotInvalid, hresultCases, hfinish, hclock,
      hraw, hexpected, hbank, htime, hsample⟩ :=
      actual_choice_receiver rate rewards C_star C_h z k c (by simpa [R, r] using hchoice)
    refine Or.inr ⟨c, ?_, ?_⟩
    · simpa [r] using hchoice
    · refine ⟨birthIndex, ?_, ?_, hbirthSigma, ?_, ?_, ?_, ?_⟩
      · simpa [R] using hbirthIndex
      · simpa [R, r] using hbirth
      · exact hsourceFields.1
      · exact hsourceFields.2.1
      · exact hsourceFields.2.2
      · refine ⟨recording, L, d, received, bank, finished, clockFinished,
          htail, hrecording, hstart, hLpending, hLsigma, hsite, hcheck,
          hdiagnostic, hinput, htailReception, hnotInvalid, hresultCases,
          hfinish, hclock, hraw, hexpected, hbank, htime, ?_, ?_⟩
        · simpa only [hsourceFields.1, hsourceFields.2.1] using hsample
        · intro i state memory hindex hconfiguration hstatus hcurrent hslot hincoming
          obtain ⟨inputState, inputMemory, choiceState, hactualInput, hinputDomain,
            hlocalStart, hactualChoice, hchoiceDomain, hoperationDomain⟩ :=
            (ReferenceCompleteSuffixFollowerPreservation.complete_suffix_follower_choice
              rewards C_star C_h z) k i
          have hchoiceState : choiceState = state := by
            have hcfg := hactualChoice.symm.trans hconfiguration
            exact (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hcfg).1
          subst choiceState
          have hcurrentDomain : ActiveFollowerLifecycle.localStateDomainValid state :=
            hchoiceDomain
          have hcodec : CoordinatorCollectionLedger.codecParams p rate.eta.val =
              ReferencePrelaunchFollower.codecParams p rate.eta :=
            ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
          obtain ⟨U, hcheckedOffer, hfields, hOfferSigma, hpositive, hword⟩ :=
            ReferenceFirstReplacementCollectionUpOfferCut.actual_current_choice_up_offer
              r i state memory (c.payload.downRecord i) hindex hconfiguration
              hstatus hcurrentDomain hcurrent hslot
          let decodedMessage : ReferenceCollectionPhaseHistory.UpRecord p rate :=
            ⟨U.val, by
              rw [hcodec]
              exact U.property⟩
          have hinputCheck : CoordinatorUpReception.receptionInputCheck d.input = true := by
            rw [hinput]
            exact hcheck
          have hdomain : CoordinatorUpReception.receptionInputDomain d.input :=
            (CoordinatorUpReception.receptionInputCheck_eq_true_iff d.input).mp hinputCheck
          rcases CoordinatorUpReception.receptionInputDomain_parts d.input hdomain with
            ⟨hvalidLedger, hpositiveSigma, hphase, hcutoffPositive, hcutoffCursor,
              hcursorT, hcursorTime, hbankDomain⟩
          have hledgerInput : d.input.ledger = L := by
            simpa [ReferenceCoordinatorUpPhysicalCall.actualUpInput,
              ReferenceActivePhysicalStep.upInputs,
              ReferenceUpReception.receptionInputAtRow,
              CoordinatorUpMeasurability.receptionInputAtRow] using
              congrArg CoordinatorUpReception.ReceptionInput.ledger hinput
          have hselectedInput : d.input.selectedFollower = i := by
            have hselected := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
              r d hdiagnostic
            rcases hselected with
              ⟨_, _, _, _, _, _, hselected, _, _, _, _, _, _, _⟩
            calc
              d.input.selectedFollower =
                  CoordinatorUpMeasurability.selectedFollowerIndex
                    ((r.input.rows r.input.selected).2 r.input.time) := hselected
              _ = ReferenceActivePhysicalStep.upSenderIndex r.input := rfl
              _ = i := hindex
          have hslotInput : d.input.slot = PublicDiscreteDraws.upSlot := by
            have hslotFields := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
              r d hdiagnostic
            rcases hslotFields with
              ⟨_, _, _, _, _, _, _, _, hslotField, _, _, _, _, _⟩
            rw [hslotField]
            simpa only [ReferenceActivePhysicalStep.RoundInput.row] using hslot
          have hcutoffAtTime :
              d.input.ledger.cutoff ≤ CoordinatorCollectionLedger.sourceRound d.input.time := by
            calc
              d.input.ledger.cutoff ≤ d.input.ledger.cursor := hcutoffCursor
              _ = CoordinatorCollectionLedger.sourceRound d.input.time := hcursorTime
          have hpendingL : i ∈ L.pending := by
            rw [hLpending]
            exact hincoming
          have hpendingInput : i ∈ d.input.ledger.pending := by
            rw [hledgerInput]
            exact hpendingL
          have hgate : CoordinatorUpReception.receptionGate d.input :=
            ⟨hcutoffAtTime, hslotInput, by simpa [hselectedInput] using hpendingInput⟩
          have hcutoffLedger : L.cutoff ≤ L.cursor := by
            simpa [hledgerInput] using hcutoffCursor
          have hOfferLedgerSigma : U.val.sigma = L.sigma := by
            calc
              U.val.sigma = (c.payload.downRecord i).val.sigma := hOfferSigma
              _ = c.payload.sigma.val + 1 := by
                exact congrArg OrdinaryMessageCodec.DownFields.sigma
                  (c.payload.downRecord_fields i)
              _ = c.preLedger.sigma := hbirthSigma.symm
              _ = L.sigma := hLsigma.symm
          have haccept : CoordinatorCollectionLedger.acceptUpCheck L i U = true := by
            apply (CoordinatorCollectionLedger.acceptUpCheck_iff L i U).2
            simp only [OrdinaryMessageCodec.acceptUp,
              CoordinatorCollectionLedger.pendingNaturalLabels_mem_iff]
            exact ⟨hcutoffLedger, hpendingL, hOfferLedgerSigma⟩
          have hwordEncoding := offered_word_eq_source_encoding rate U
          have hexpectedEncoded : d.expected =
              some (ReferenceCollectionUpFailureReadoutV2.enc rate U) := by
            rw [hexpected, hword]
            exact congrArg some hwordEncoding.symm
          have hacceptInput : CoordinatorCollectionLedger.acceptUpCheck
              d.input.ledger i U = true := by
            rw [hledgerInput]
            exact haccept
          have hawaited : ReferenceCollectionUpFailureReadoutV2.awaitedUpAt rate r i U :=
            ⟨d, hdiagnostic, hselectedInput, hinputCheck, hgate,
              hexpectedEncoded, hacceptInput⟩
          have hphysical :=
            ReferenceLiteralSourceDecoderCoverage.physicalAwaitedUpAt_of_awaitedUpAt
              r i U hawaited
          have horiginal :=
            ReferenceCompleteAwaitedBatchSourceCoverage.originalUpAwaitedCallAt_of_physical
              rate r i U hphysical
          have hactual := actual_record_at_complete_suffix rate rewards C_star C_h z k
          have hsourceAwaited :
              ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt
                rate rewards C_star C_h z i U r.input.time := by
            have hactualR : ReferenceSourcePrefixHistoryFiltration.actualRecord
                rate rewards C_star C_h r.input.time z = some r := by
              simpa [R, r] using hactual
            simp only [ReferenceCompleteAwaitedBatchSourceCoverage.sourceUpAwaitedAt,
              hactualR]
            exact horiginal
          refine ⟨U, hcheckedOffer, hfields, hOfferSigma, hpositive, hword,
            hselectedInput, hgate, hawaited, horiginal, hsourceAwaited, haccept, ?_⟩
          intro hmatchingRaw
          have hmatchingRawOffer : d.raw =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
            rw [hwordEncoding] at hmatchingRaw
            exact hmatchingRaw
          have hrawInput : (CoordinatorUpReception.decoderTransition d.input).2 =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) :=
            hraw.symm.trans hmatchingRawOffer
          let receiverInput := ReferenceUpReception.receptionInputAtRow rate
            r.input.row (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare r.input) L) r.input.time
          have hrawAtRow : (CoordinatorUpReception.decoderTransition receiverInput).2 =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
            simpa [receiverInput, hinput,
              ReferenceCoordinatorUpPhysicalCall.actualUpInput,
              ReferenceActivePhysicalStep.upInputs,
              ReferenceUpReception.receptionInputAtRow,
              CoordinatorUpMeasurability.receptionInputAtRow] using hrawInput
          have hexpectedOffer : ReferenceActivePhysicalStep.upExpected
              (ReferenceActivePhysicalStep.prepare r.input) =
                some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := hword
          have hfilter : ReferenceUpReception.filterRawByExpected
              (CoordinatorUpReception.decoderTransition receiverInput).2
              (ReferenceActivePhysicalStep.upExpected
                (ReferenceActivePhysicalStep.prepare r.input)) =
                  some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
            rw [hrawAtRow, hexpectedOffer]
            exact ReferenceUpReception.filterRawByExpected_eq_raw_of_eq _ _ rfl
          have hparsedWord : CoordinatorUpReception.parseDecoderOutput
              (some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) =
                some decodedMessage := by
            rw [← hwordEncoding]
            cases hcodec
            have hdecoded : decodedMessage = U := by
              apply Subtype.ext
              rfl
            rw [hdecoded]
            exact ReferenceLiteralSourceDecoderCoverage.parseUp_encoded U
          have hfilteredParsed :
              ReferenceCollectionPhaseHistory.filteredParsed r.input L =
                some decodedMessage := by
            change CoordinatorUpReception.parseDecoderOutput
              (ReferenceUpReception.filterRawByExpected
                (CoordinatorUpReception.decoderTransition receiverInput).2
                (ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare r.input))) =
                    some decodedMessage
            rw [hfilter]
            exact hparsedWord
          have hreceiverCheck : CoordinatorUpReception.receptionInputCheck receiverInput = true := by
            simpa [receiverInput, hinput,
              ReferenceCoordinatorUpPhysicalCall.actualUpInput,
              ReferenceActivePhysicalStep.upInputs,
              ReferenceUpReception.receptionInputAtRow,
              CoordinatorUpMeasurability.receptionInputAtRow] using hcheck
          have heffectiveParse : ReferenceCollectionSegmentExtraction.effectiveParse
              r.input L = some decodedMessage := by
            change ReferenceCollectionPhaseHistory.filteredParsed r.input L =
              some decodedMessage
            exact hfilteredParsed
          have hreceiveFiltered :=
            ReferenceCollectionSegmentExtraction.receiveUp_filtered r.input L hreceiverCheck
          rw [heffectiveParse] at hreceiveFiltered
          have hdecodeInput : CoordinatorCollectionLedger.validLedgerCheck L = true ∧
              L.phase = CoordinatorCollectionLedger.Phase.started ∧
              1 ≤ L.cutoff ∧ L.cutoff ≤ L.cursor ∧ L.cursor ≤ p.T := by
            simpa [hledgerInput] using
              (show CoordinatorCollectionLedger.validLedgerCheck d.input.ledger = true ∧
                d.input.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
                1 ≤ d.input.ledger.cutoff ∧
                d.input.ledger.cutoff ≤ d.input.ledger.cursor ∧
                d.input.ledger.cursor ≤ p.T from
                ⟨hvalidLedger, hphase, hcutoffPositive, hcutoffCursor, hcursorT⟩)
          have hdecodeNoReject : ∀ out,
              CoordinatorCollectionLedger.decodeUp L i (some decodedMessage) ≠
                .rejected out := by
            have hacceptDecoded : CoordinatorCollectionLedger.acceptUpCheck
                L i decodedMessage = true := by
              apply (CoordinatorCollectionLedger.acceptUpCheck_iff
                L i decodedMessage).2
              simp only [OrdinaryMessageCodec.acceptUp,
                CoordinatorCollectionLedger.pendingNaturalLabels_mem_iff]
              exact ⟨hcutoffLedger, hpendingL, by
                simpa [decodedMessage] using hOfferLedgerSigma⟩
            intro out hdecode
            unfold CoordinatorCollectionLedger.decodeUp at hdecode
            rw [dite_eq_left hdecodeInput] at hdecode
            dsimp only at hdecode
            rw [ite_eq_left hacceptDecoded] at hdecode
            repeat' (first | split at hdecode)
            all_goals
              have hdifferent := congrArg
                (fun result : CoordinatorCollectionLedger.Checked
                    (ReferenceActivePhysicalStep.Ledger rate) =>
                  match result with
                  | .success _ => 0
                  | .rejected _ => 1
                  | .invalid => 2) hdecode
              norm_num at hdifferent
          have hresultNoReject :
              (ReferenceActivePhysicalStep.receiveUp
                (ReferenceActivePhysicalStep.prepare r.input) L).result ≠
                  .rejected (received, bank) := by
            intro hreject
            rw [hindex] at hreceiveFiltered
            rw [hreceiveFiltered] at hreject
            cases hdecode : CoordinatorCollectionLedger.decodeUp L i
                (some decodedMessage) with
            | success out =>
                rw [hdecode] at hreject
                simp [CoordinatorUpReception.packDecodeResult] at hreject
            | rejected out => exact (hdecodeNoReject out) hdecode
            | invalid =>
                rw [hdecode] at hreject
                simp [CoordinatorUpReception.packDecodeResult] at hreject
          have hsuccess : (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L).result =
                .success (received, bank) := by
            rcases hresultCases with hsuccess | hreject
            · exact hsuccess
            · exact False.elim (hresultNoReject hreject)
          have haccepted : ReferenceCollectionPhaseHistory.AcceptedUp r.input i U := by
            cases hcodec
            have hdecoded : decodedMessage = U := by
              apply Subtype.ext
              rfl
            rw [hdecoded] at hfilteredParsed
            exact ⟨⟨c.payload, c.preLedger, c.started, c.weights⟩, recording, L,
              received, bank, htail, hrecording, hstart, hsuccess,
              hfilteredParsed, hindex.symm⟩
          have hpost : r.output.coordinator =
              ReferenceActivePhysicalStep.collectionPostChoice
                (ReferenceActivePhysicalStep.prepare r.input)
                c.payload c.preLedger c.started c.weights := by
            calc
              r.output.coordinator =
                  (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator := by
                    rw [r.output_eq]
                    rfl
              _ = ReferenceActivePhysicalStep.collectionPostChoice
                    (ReferenceActivePhysicalStep.prepare r.input)
                    c.payload c.preLedger c.started c.weights :=
                  ReferenceCollectionSegmentExtraction.choice_tail r.input c hchoice
          have hpostStarted := ReferenceActivePhysicalStep.collectionPostChoice_after_start
            (ReferenceActivePhysicalStep.prepare r.input) c.payload c.preLedger c.started
            c.weights recording L hrecording hstart
          have hfinishOutput := ReferenceActivePhysicalStep.collectionFinish_success
            c.payload c.started recording
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare r.input) L)
            received finished bank clockFinished (Or.inl hsuccess) hfinish hclock
          have houtput : r.output.coordinator =
              ⟨.collection c.payload finished clockFinished.clock.lastProposal,
                bank, none, some recording,
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare r.input) L).diagnostic⟩ := by
            calc
              r.output.coordinator =
                  ReferenceActivePhysicalStep.collectionPostChoice
                    (ReferenceActivePhysicalStep.prepare r.input)
                    c.payload c.preLedger c.started c.weights := hpost
              _ = ReferenceActivePhysicalStep.collectionFinish
                    (x := r.input) c.payload c.started recording
                    (ReferenceActivePhysicalStep.receiveUp
                      (ReferenceActivePhysicalStep.prepare r.input) L) := hpostStarted
              _ = _ := hfinishOutput
          have hstepNext : (ReferenceActivePhysicalStep.step r.input).next.coordinator =
              .collection c.payload finished clockFinished.clock.lastProposal := by
            calc
              _ = (ReferenceActivePhysicalStep.step r.input).coordinator.configuration :=
                (ReferenceActivePhysicalStep.step_next_fields r.input).1
              _ = r.output.coordinator.configuration := by rw [r.output_eq]
              _ = .collection c.payload finished clockFinished.clock.lastProposal :=
                congrArg ReferenceActivePhysicalStep.CoordinatorObservation.configuration houtput
          have hnext : r.output.next.coordinator =
              .collection c.payload finished clockFinished.clock.lastProposal := by
            rw [r.output_eq]
            exact hstepNext
          have hlabel : ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i := by
            unfold ReferenceCollectionPhaseHistory.acceptedLabel
            rw [htail]
            simp only [Option.bind_some]
            rw [htailReception]
            simp only [Option.bind_some]
            rw [hsuccess, hindex]
          obtain ⟨tailFrame, htailFrame, hpendingFrame, _hsigmaFrame⟩ :=
            ReferenceCollectionPhaseHistory.step_collection_frame r.input c.payload
              finished clockFinished.clock.lastProposal hstepNext
          have htailFrameEq : tailFrame =
              (⟨c.payload, c.preLedger, c.started, c.weights⟩ :
                ReferenceCollectionPhaseHistory.Tail r.input) :=
            Option.some.inj (htailFrame.symm.trans htail)
          rw [htailFrameEq, hlabel] at hpendingFrame
          simp only [ReferenceCollectionPhaseHistory.eraseEvent] at hpendingFrame
          have hnotPending : i ∉ finished.pending := by
            rw [hpendingFrame]
            simp
          refine ⟨haccepted, ?_⟩
          exact ⟨clockFinished.clock.lastProposal, hnext, hnotPending⟩

end Bandits.Support.ReferenceOriginalCollectionCurrentUpReceiver

end
