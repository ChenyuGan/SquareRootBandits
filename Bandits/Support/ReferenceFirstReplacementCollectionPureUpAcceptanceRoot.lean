/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstReplacementCollectionPureUpDecisionLocation
public import Bandits.Support.ReferenceFirstReplacementCollectionUpStartedFields

import Lean.Elab.Tactic.Omega

/-!
# Actual second pure UP acceptance in the first replacement collection

Sources: `sources/zip4/manuscript/06_interruptions.tex:110-177,246-299,477-481`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:141-157`, and
`sources/zip4/manuscript/05_binary_transport.tex:27-55`.

The actual pure-window cut supplies the origin and both completed batches.
Its least threshold locates a continuing physical record. At that record the
actual recorder and started ledger discharge the literal UP acceptance test.
The matching branch succeeds and erases the selected ledger label, while the
decoder bank retains both completions and an empty pending equation list.
The other alternative is a distinct solution of every pure-window equation.

First obstruction, surviving shortage, absent-current, and terminal/next-birth
cases remain explicit. The result is deterministic reference-execution
infrastructure for replacement decoding-time/quota and ambiguity-event
assembly; it asserts no probability law or regret theorem closure.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceFirstReplacementCollectionPureUpWindowCut (physicalPositives)

namespace Bandits.Support.ReferenceFirstReplacementCollectionPureUpAcceptanceRoot

variable {p : Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The successful branch of the literal checked decoder removes precisely its
selected pending follower. A successful result cannot be used to assume that
any parser, domain, or replay guard passed; those guards are discharged by the
actual success equation. -/
private theorem successful_decodeUp_erases_selected_pending
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (i : Fin (p.m - 1))
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (out : ReferenceActivePhysicalStep.Ledger rate)
    (haccept : CoordinatorCollectionLedger.acceptUpCheck l i M = true)
    (hdecode : CoordinatorCollectionLedger.decodeUp l i (some M) = .success out) :
    out.pending = l.pending.erase i := by
  unfold CoordinatorCollectionLedger.decodeUp at hdecode
  by_cases hinput : CoordinatorCollectionLedger.validLedgerCheck l = true ∧
      l.phase = CoordinatorCollectionLedger.Phase.started ∧
      1 ≤ l.cutoff ∧ l.cutoff ≤ l.cursor ∧ l.cursor ≤ p.T
  · rw [dite_eq_left hinput] at hdecode
    simp only [haccept] at hdecode
    repeat' (first | split at hdecode)
    all_goals
      cases hdecode
      all_goals simp [CoordinatorCollectionLedger.acceptUpCandidate]
  · rw [dite_eq_right hinput] at hdecode
    cases hdecode

/-- At one actual continuing-collection record, the local receiver's three
conditions force the literal filtered parser and checked receive operation to
succeed for that same offered word. The start ledger and diagnostic remain
the ones produced by the record's own recorder and receiver stages. -/
private theorem actual_replacement_collection_up_receiver_matching_word
    (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (hstate : r.input.state.coordinator = .collection payload ledger saved)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (hordinary : r.output.next.coordinator ≠ .dagger)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hdiagnostic : r.output.coordinator.up = some d)
    (U : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hraw : d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hexpected : d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hstartedFields : ∀ (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input)
          tail.payload tail.started tail.weights) = some recording →
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success L →
      L.cutoff ≤ L.cursor ∧
        ReferenceActivePhysicalStep.upSenderIndex r.input ∈ L.pending ∧
        U.val.sigma = L.sigma) :
    ∃ (recording : CoordinatorRecordingOperation.Output p)
      (L : ReferenceActivePhysicalStep.Ledger rate)
      (decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p),
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare r.input)
          tail.payload tail.started tail.weights) = some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (r.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger r.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
          .success L ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some L ∧
      CoordinatorUpReception.receptionInputCheck
        (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L) = true ∧
      d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input L ∧
      CoordinatorCollectionLedger.acceptUpCheck L
        (ReferenceActivePhysicalStep.upSenderIndex r.input) U = true ∧
      ReferenceCollectionPhaseHistory.filteredParsed r.input L = some U ∧
      d.parsed = some U ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
      d.wrongUniqueAccepted = false ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) L).result = .success (decoded, bank) ∧
      decoded.pending = L.pending.erase (ReferenceActivePhysicalStep.upSenderIndex r.input) ∧
      tail.reception = some (L,
        ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) L) ∧
      ReferenceCollectionPhaseHistory.AcceptedUp r.input
        (ReferenceActivePhysicalStep.upSenderIndex r.input) U := by
  obtain ⟨recording, L, diagnostic, hrecording, hstart, hsite, hcheck,
      hup, hinput, htailReception, hnotInvalid, hfinish, hdecoder, hraw',
      hparsed', hlocal', hexpected', hmatches', hbank, htime, hsample,
      hobservation, hwrong, hmatching⟩ :=
    ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
      r payload ledger saved tail hstate htail hordinary
  obtain ⟨hcutoffCursor, hiPending, hSigma⟩ :=
    hstartedFields recording L hrecording hstart
  have haccept' : CoordinatorCollectionLedger.acceptUpCheck L
      (ReferenceActivePhysicalStep.upSenderIndex r.input) U = true := by
    simp [CoordinatorCollectionLedger.acceptUpCheck, hcutoffCursor, hiPending, hSigma]
  have hdiagnosticEq : diagnostic = d := Option.some.inj (hup.symm.trans hdiagnostic)
  subst diagnostic
  obtain ⟨hfiltered, hparsed, hlocal, hmatchesWord, hwrongFalse,
      decoded, bank, hsuccess, haccepted⟩ :=
    hmatching U hraw hexpected haccept'
  let prepared := ReferenceActivePhysicalStep.prepare r.input
  let inputs := ReferenceActivePhysicalStep.upInputs prepared L
  let receiverInput := ReferenceUpReception.receptionInputAtRow rate r.input.row
    inputs r.input.time
  have hreceiverCheck : CoordinatorUpReception.receptionInputCheck receiverInput = true := by
    simpa [receiverInput, inputs, prepared, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hcheck
  have hrawAtReceiver : (CoordinatorUpReception.decoderTransition receiverInput).2 =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    simpa [receiverInput, inputs, prepared, hinput,
      ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hraw'.symm.trans hraw
  have hexpectedAtPrepared : ReferenceActivePhysicalStep.upExpected prepared =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    simpa [prepared] using hexpected'.symm.trans hexpected
  have hfilteredAtReceiver : CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected
        (CoordinatorUpReception.decoderTransition receiverInput).2
        (ReferenceActivePhysicalStep.upExpected prepared)) = some U := by
    simpa [receiverInput, inputs, prepared, ReferenceCollectionPhaseHistory.filteredParsed,
      ReferenceCoordinatorUpPhysicalCall.actualUpInput, ReferenceActivePhysicalStep.upInputs,
      ReferenceUpReception.receptionInputAtRow, CoordinatorUpMeasurability.receptionInputAtRow]
      using hfiltered
  have hfilterIdentity : ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition receiverInput).2
      (ReferenceActivePhysicalStep.upExpected prepared) =
        (CoordinatorUpReception.decoderTransition receiverInput).2 := by
    rw [hrawAtReceiver, hexpectedAtPrepared]
    exact ReferenceUpReception.filterRawByExpected_eq_raw_of_eq _ _ rfl
  have hparsedReceiver : CoordinatorUpReception.parsedDecoderOutput receiverInput = some U := by
    change CoordinatorUpReception.parseDecoderOutput
      (CoordinatorUpReception.decoderTransition receiverInput).2 = some U
    rw [← hfilterIdentity]
    exact hfilteredAtReceiver
  have hordinaryMatch : (CoordinatorUpReception.decoderTransition receiverInput).2 =
      ReferenceActivePhysicalStep.upExpected prepared :=
    hrawAtReceiver.trans hexpectedAtPrepared.symm
  have hactualOrdinary :
      (ReferenceActivePhysicalStep.receiveUp prepared L).result =
        CoordinatorUpReception.receiveUp receiverInput := by
    simpa [prepared, inputs, receiverInput] using
      ReferenceActivePhysicalStep.receiveUp_eq_ordinary_of_no_mismatch prepared L hordinaryMatch
  have hsuccessReceiver : CoordinatorUpReception.receiveUp receiverInput =
      .success (decoded, bank) := hactualOrdinary.symm.trans hsuccess
  have hparsedRaw : OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      ((CoordinatorUpReception.decoderTransition receiverInput).2.map
        (OrdinaryMessageCodec.wordEquivFlat
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm) = some U := by
    change CoordinatorUpReception.parsedDecoderOutput receiverInput = some U
    exact hparsedReceiver
  have hdecode : CoordinatorCollectionLedger.decodeUp L
      (ReferenceActivePhysicalStep.upSenderIndex r.input) (some U) = .success decoded := by
    have hreceiveDecode :=
      CoordinatorUpReception.receiveUp_eq_existing_decodeUp receiverInput hreceiverCheck
    rw [hparsedRaw] at hreceiveDecode
    have hpack := hreceiveDecode.symm.trans hsuccessReceiver
    have hdecodeReceiver : CoordinatorCollectionLedger.decodeUp receiverInput.ledger
        receiverInput.selectedFollower (some U) = .success decoded := by
      cases hresult : CoordinatorCollectionLedger.decodeUp receiverInput.ledger
          receiverInput.selectedFollower (some U) with
      | success out =>
          simp [CoordinatorUpReception.packDecodeResult, hresult] at hpack
          exact congrArg CoordinatorCollectionLedger.Checked.success hpack.1
      | rejected out => simp [CoordinatorUpReception.packDecodeResult, hresult] at hpack
      | invalid => simp [CoordinatorUpReception.packDecodeResult, hresult] at hpack
    have hledger : receiverInput.ledger = L := rfl
    have hselected : receiverInput.selectedFollower =
        ReferenceActivePhysicalStep.upSenderIndex r.input := by
      change CoordinatorUpMeasurability.selectedFollowerIndex (r.input.row.2 r.input.time) =
        CoordinatorUpMeasurability.selectedFollowerIndex (r.input.row.2 r.input.time)
      rfl
    rw [hledger, hselected] at hdecodeReceiver
    exact hdecodeReceiver
  have hdecodedPending := successful_decodeUp_erases_selected_pending
    L (ReferenceActivePhysicalStep.upSenderIndex r.input) U decoded haccept' hdecode
  exact ⟨recording, L, decoded, bank, hrecording, hstart, hsite, hcheck,
    hinput, haccept', hfiltered, hparsed, hlocal, hmatchesWord, hwrongFalse,
    hsuccess, hdecodedPending, htailReception, haccepted⟩


/-- Compose the actual first-replacement cut with physical decision location
and the same record's started receiver. There are no produced-word, pending,
acceptance, or success assumptions in the original-source telescope. -/
theorem complete_first_replacement_collection_pure_up_acceptance
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) :
    let R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
    let s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
    let v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
    let tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
    let c := v + 1 + tail.length
    match R[v]? with
    | none => True
    | some birth =>
      match birth.output.preparation.coordinator with
      | .collection _ _ _ _ (.laterChosen _ _ _ _ _ _ _ _ _ installed _) =>
        let payload := installed.registers.payload
        let X := (R.drop v).take (1 + tail.length)
        let C := X.filterMap (ReferenceLaterLiveNumericalReadout.laterLiveReadout s)
        let L0 := X.length
        C.length = L0 ∧ X = birth :: tail ∧
        match R[c]? with
        | none => True
        | some cut =>
          match cut.output.preparation.coordinator with
          | .live _ _ _ (.cutoffChosen _ _ _ _ _ _ _ _ _ _) =>
            let u := cut.input.time.val + 1
            let W := (R.drop (c + 1)).takeWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
            let K := cut :: W
            let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.output.next (W.take j)
            let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
              cut.input.state (K.take j)
            let M := fun i => payload.downRecord i
            (∀ q : Fin K.length, (K.get q).input.time.val + 1 = u + q.val) ∧
            (Z 0 = cut.input.state ∧
              (∀ j : ℕ, j ≤ W.length → Z (j + 1) = E j) ∧
              (∀ q : Fin K.length, (K.get q).input.state = Z q.val ∧
                (K.get q).output.next = Z (q.val + 1))) ∧
            (∀ i : Fin (p.m - 1),
              (∃ (b : ℕ) (anchor : ReferencePrelaunchFollower.State p rate.eta)
                  (memory : ActiveFollowerLifecycle.LocalMemory p),
                ((b = 0 ∧
                  (cut.output.preparation.followers.followers i).configuration =
                    .ordinary anchor memory ∧
                  ∃! x : Fin X.length,
                    ReferenceAcceptedUpFollowerHistory.RetainedDown (X.get x) i (M i)) ∨
                 (∃ q : Fin K.length, b = q.val + 1 ∧
                  ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i) ∧
                  (∀ j : Fin K.length, j.val < q.val →
                    ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get j) i (M i)) ∧
                  (K.get q).output.next.followers i = .ordinary anchor memory ∧
                  (Z (q.val + 1)).followers i = .ordinary anchor memory ∧
                  ∀ state mem, (cut.output.preparation.followers.followers i).configuration =
                    .ordinary state mem → state.lastDown ≠ some (M i))) ∧
                b ≤ K.length ∧ anchor.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid anchor ∧
                anchor.lastDown = some (M i) ∧
                (∃ last lastMemory, (E W.length).followers i = .ordinary last lastMemory ∧
                  last.status = .unoccupied ∧ last.lastDown = some (M i) ∧
                  ReferenceFollowerReplyChronology.reply last =
                    ReferenceFollowerReplyChronology.reply anchor) ∧
                ∃ U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta),
                U.val = ActiveFollowerQueueOperation.upOfferFields anchor ∧
                U.val.sigma = (M i).val.sigma ∧ 0 < U.val.sigma ∧
                (∀ j : Fin K.length, b ≤ j.val → ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown = some (M i) ∧
                  ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply anchor ∧
                  (ReferenceActivePhysicalStep.upSenderIndex (K.get j).input = i →
                    PublicDiscreteDraws.slotDraw ((K.get j).input.row.2
                      (K.get j).input.time).1 = PublicDiscreteDraws.upSlot →
                    ActiveFollowerQueueOperation.checkedUpOffer rate.eta i (K.get j).input.row
                      ((K.get j).input.state.activations i) (K.get j).input.time state = .offer U ∧
                    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare
                      (K.get j).input) = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                  (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    (K.get j).output.coordinator.up = some d → d.input.selectedFollower = i →
                    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
                    d.input.time = (K.get j).input.time ∧ d.input.selectedFollower = i ∧
                    d.input.slot = PublicDiscreteDraws.slotDraw
                      ((K.get j).input.row.2 (K.get j).input.time).1 ∧
                    d.input.affineSample = ((K.get j).input.row.2 (K.get j).input.time).2 (1, i) ∧
                    AffineChannelLaw.affineHash d.input.affineSample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1)) ∧
                (∀ entry ∈ ReferenceCoordinatorUpDecoderReplay.retainedUpPositiveEntries (K.drop b) i,
                  ∃ r ∈ K.drop b, ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                    r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                    AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
                    entry.time = r.input.time ∧
                    d.input.slot = PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 ∧
                    entry.sample = d.input.affineSample ∧
                    d.input.affineSample = (r.input.row.2 r.input.time).2 (1, i) ∧
                    AffineChannelLaw.affineHash entry.sample
                      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) = 1) ∧
                let H := K.drop b
                let channel := (Z b).upDecoderBank i
                let Q := AffineBatchDecoder.quota p
                let need := Q - channel.pending.length + Q
                (∀ e ∈ physicalPositives H i,
                  AffineBatchDecoder.equation e.sample
                    (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                ((∃ (q : Fin K.length) (reason : ReferenceActivePhysicalStep.CoordinatorFailure),
                    b ≤ q.val + 1 ∧ (Z q.val).coordinator ≠ .dagger ∧
                    (K.get q).output.next.coordinator = .dagger ∧
                    (K.get q).output.coordinator.failure = some reason ∧
                    (∀ j : Fin K.length, j.val < q.val →
                      (K.get j).output.next.coordinator ≠ .dagger) ∧
                    (Z q.val).upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
                      (Z 0).upDecoderBank
                      (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (K.take q.val)) ∧
                    AffineBatchDecoder.run p
                      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (K.take q.val) i)
                      ((K.take q.val).map (fun r => r.input.time)) ((Z 0).upDecoderBank i) =
                        (Z q.val).upDecoderBank i ∧
                    (b ≤ q.val → AffineBatchDecoder.run p
                      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace (H.take (q.val - b)) i)
                      ((H.take (q.val - b)).map (fun r => r.input.time)) channel = (Z q.val).upDecoderBank i ∧
                      (physicalPositives (H.take (q.val + 1 - b)) i).length =
                        (physicalPositives (H.take (q.val - b)) i).length +
                          (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length) ∧
                    (physicalPositives (K.take (q.val + 1)) i).length =
                      (physicalPositives (K.take q.val) i).length +
                        (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length ∧
                    (ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries (K.get q) i).length ≤ 1 ∧
                    (match ReferenceCollectionPhaseHistory.executedTail (K.get q).input with
                    | none => ReferenceCollectionPhaseHistory.executedTail (K.get q).input = none
                    | some t =>
                      match t.reception with
                      | none =>
                        CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare (K.get q).input)
                            t.payload t.started t.weights) = none ∨
                        ∃ recording : CoordinatorRecordingOperation.Output p,
                          CoordinatorRecorderComplementBridge.run
                            (ReferenceActivePhysicalStep.collectionRecordingInput
                              (ReferenceActivePhysicalStep.prepare (K.get q).input)
                              t.payload t.started t.weights) = some recording ∧
                          (CoordinatorCollectionLedger.startRound t.ledger ((K.get q).input.time.val + 1)
                            (ReferenceActivePhysicalStep.collectionEnabled t.ledger (K.get q).input.time)
                            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .invalid ∨
                           ∃ rejected, CoordinatorCollectionLedger.startRound t.ledger
                            ((K.get q).input.time.val + 1)
                            (ReferenceActivePhysicalStep.collectionEnabled t.ledger (K.get q).input.time)
                            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .rejected rejected)
                      | some (started, received) =>
                        let rin := ReferenceUpReception.receptionInputAtRow rate (K.get q).input.row
                          (ReferenceActivePhysicalStep.upInputs
                            (ReferenceActivePhysicalStep.prepare (K.get q).input) started) (K.get q).input.time
                        match received.diagnostic with
                        | none => CoordinatorUpReception.receptionInputCheck rin = false ∧
                            received.result = .invalid ∧ (K.get q).output.coordinator.up = none
                        | some d => d.input = rin ∧
                            d.expected = ReferenceActivePhysicalStep.upExpected
                              (ReferenceActivePhysicalStep.prepare (K.get q).input) ∧
                            d.raw = (CoordinatorUpReception.decoderTransition rin).2 ∧
                            d.parsed = ReferenceUpReception.rawParsedOutput rate rin ∧
                            (K.get q).output.coordinator.up = some d) ∧
                    (∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
                      (K.get q).output.coordinator.up = some d →
                      d.input.upDecoderBank = (Z q.val).upDecoderBank ∧
                      d.expected = ReferenceActivePhysicalStep.upExpected
                        (ReferenceActivePhysicalStep.prepare (K.get q).input) ∧
                      d.raw = (CoordinatorUpReception.decoderTransition d.input).2 ∧
                      ∃ ledger,
                        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := (K.get q).input) = some ledger ∧
                        CoordinatorUpReception.receptionInputCheck
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput (K.get q).input ledger) = true ∧
                        d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput (K.get q).input ledger ∧
                        d.decoderAfter = (CoordinatorUpReception.decoderTransition
                          (ReferenceCoordinatorUpPhysicalCall.actualUpInput (K.get q).input ledger)).1 ∧
                        (((ReferenceActivePhysicalStep.receiveUp
                            (ReferenceActivePhysicalStep.prepare (K.get q).input) ledger).result = .invalid ∧
                            (K.get q).output.next.upDecoderBank = (K.get q).input.state.upDecoderBank) ∨
                          ∃ out,
                            ((ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare (K.get q).input) ledger).result = .success out ∨
                             (ReferenceActivePhysicalStep.receiveUp
                              (ReferenceActivePhysicalStep.prepare (K.get q).input) ledger).result = .rejected out) ∧
                            out.2 = CoordinatorUpReception.decoderBankAfter d.input ∧
                            (K.get q).output.next.upDecoderBank = out.2))) ∨
                  ((∀ q : Fin K.length, (K.get q).output.next.coordinator ≠ .dagger) ∧
                    (((physicalPositives H i).length < need ∧
                        ((∀ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input ≠ some i) ∨
                         ∃ r ∈ H, ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i ∧
                           ∃ message, ReferenceCollectionPhaseHistory.AcceptedUp r.input i message ∧
                             ∃ ledger saved, (E W.length).coordinator = .collection payload ledger saved ∧
                               i ∉ ledger.pending ∧ ((E W.length).upDecoderBank i).pending = [])) ∨
                      ∃ m : ℕ, 0 < m ∧ m ≤ H.length ∧
                        (physicalPositives (H.take m) i).length = need ∧
                        (∀ n : ℕ, n < m → (physicalPositives (H.take n) i).length < need) ∧
                        let positive := physicalPositives (H.take m) i
                        let window := positive.drop (Q - channel.pending.length)
                        ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                          (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                          (index : Fin (H.take m).length)
                          (r : ReferenceCompletePhysicalHistory.RoundRecord p rate)
                          (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                          first = channel.pending ++ positive.take (Q - channel.pending.length) ∧
                          first.length = Q ∧ window.length = Q ∧
                          window.Pairwise (fun earlier later => earlier.time.val < later.time.val) ∧
                          (∀ e ∈ window, AffineBatchDecoder.equation e.sample
                            (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                          last ∈ window ∧ AffineBatchDecoder.decisionTime window = some last.time ∧
                          r ∈ H.take m ∧ r.input.time = last.time ∧
                          r.output.coordinator.up = some d ∧ d.input.selectedFollower = i ∧
                          d.input.time = r.input.time ∧ last.sample = d.input.affineSample ∧
                          d.input.upDecoderBank = r.input.state.upDecoderBank ∧
                          r.input.state.upDecoderBank = ReferenceCoordinatorUpDecoderReplay.replay
                            (Z b).upDecoderBank
                            (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics ((H.take m).take index.val)) ∧
                          (d.input.upDecoderBank i).pending ++ [last] = window ∧
                          d.decoderAfter = ⟨[], channel.completed ++ [first, window]⟩ ∧
                          d.raw = AffineBatchDecoder.batchOutput window ∧
                          d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                          (Z (b + m)).upDecoderBank i = ⟨[], channel.completed ++ [first, window]⟩ ∧
                          2 ≤ m ∧ ∃ k : Fin K.length,
                            k.val = b + m - 1 ∧ 0 < k.val ∧ K.get k = r ∧
                            R[c + k.val]? = some r ∧
                            r.input.time.val + 1 = u + k.val ∧
                            r.input.rows = source.1.2 ∧
                            r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                            r.input.rewards = rewards ∧ r.input.state = E (k.val - 1) ∧
                            ReferenceCoordinatorUpDecoderReplay.recordUpPositiveEntries r i = [last] ∧
                            ReferenceActivePhysicalStep.upSenderIndex r.input = i ∧
                            AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
                            ((d.raw = none ∧ ∃ other,
                              other ≠ ActiveFollowerArmChoice.offeredUpWord rate.eta U ∧
                              ∀ e ∈ window, AffineBatchDecoder.equation e.sample other) ∨
                              (d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                                (∀ other, (∀ e ∈ window, AffineBatchDecoder.equation e.sample other) →
                                  other = ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                                ∃ (ledger : ReferenceActivePhysicalStep.Ledger rate)
                                  (saved : Option (Fin p.T × Bool))
                                  (t : ReferenceCollectionPhaseHistory.Tail r.input)
                                  (recording : CoordinatorRecordingOperation.Output p)
                                  (started decoded : ReferenceActivePhysicalStep.Ledger rate)
                                  (bank : CoordinatorUpReception.UpDecoderBank p)
                                  (finished : ReferenceActivePhysicalStep.Ledger rate)
                                  (clockFinished : CoordinatorPhaseClock.FinishRoundResult p),
                                  r.input.state.coordinator = .collection payload ledger saved ∧
                                  ReferenceCollectionPhaseHistory.executedTail r.input = some t ∧
                                  CoordinatorRecorderComplementBridge.run
                                    (ReferenceActivePhysicalStep.collectionRecordingInput
                                      (ReferenceActivePhysicalStep.prepare r.input)
                                      t.payload t.started t.weights) = some recording ∧
                                  CoordinatorCollectionLedger.startRound t.ledger (r.input.time.val + 1)
                                    (ReferenceActivePhysicalStep.collectionEnabled t.ledger r.input.time)
                                    (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                                      .success started ∧
                                  ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some started ∧
                                  CoordinatorUpReception.receptionInputCheck
                                    (ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started) = true ∧
                                  d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input started ∧
                                  t.reception = some (started, ReferenceActivePhysicalStep.receiveUp
                                    (ReferenceActivePhysicalStep.prepare r.input) started) ∧
                                  started.sigma = payload.sigma.val + 1 ∧ started.cutoff = u ∧
                                  started.cursor = r.input.time.val + 1 ∧ started.cutoff ≤ started.cursor ∧
                                  started.pending = Finset.univ \
                                    (ReferenceCollectionPhaseHistory.acceptedLabels (K.take k.val)).toFinset ∧
                                  i ∈ started.pending ∧ i ∉
                                    (ReferenceCollectionPhaseHistory.acceptedLabels (K.take k.val)).toFinset ∧
                                  U.val.sigma = started.sigma ∧
                                  CoordinatorCollectionLedger.acceptUpCheck started i U = true ∧
                                  ReferenceCollectionPhaseHistory.filteredParsed r.input started = some U ∧
                                  d.parsed = some U ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
                                  d.wrongUniqueAccepted = false ∧
                                  (ReferenceActivePhysicalStep.receiveUp
                                    (ReferenceActivePhysicalStep.prepare r.input) started).result =
                                      .success (decoded, bank) ∧
                                  decoded.pending = started.pending.erase i ∧
                                  bank = CoordinatorUpReception.decoderBankAfter d.input ∧
                                  r.output.next.upDecoderBank = bank ∧
                                  (Z (b + m)).upDecoderBank = bank ∧
                                  bank i = ⟨[], channel.completed ++ [first, window]⟩ ∧
                                  CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                                  CoordinatorPhaseClock.finishRound p rate.eta.val r.input.time t.started.clock
                                    finished.pending r.input.row = .ok clockFinished ∧
                                  ReferenceCollectionPhaseHistory.AcceptedUp r.input i U)))))) ∨
              ((∀ j : Fin K.length, ∃ state memory,
                  (ReferenceFollowerFixedReply.actualChoice (K.get j) i).configuration =
                    .ordinary state memory ∧ state.status = .unoccupied ∧
                  state.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart state < (M i).val.sigma ∧
                  ((state.lastDown = none ∧ state.S = 0 ∧ state.delta = 0 ∧ state.backlog = 0) ∨
                    ∃ old, state.lastDown = some old ∧ 0 < old.val.sigma ∧
                      old.val.sigma < (M i).val.sigma)) ∧
               (∃ last memory, (E W.length).followers i = .ordinary last memory ∧
                  last.status = .unoccupied ∧ last.lastDown ≠ some (M i) ∧
                  ReferencePrelaunchFollower.acceptedStart last < (M i).val.sigma ∧
                  ((last.lastDown = none ∧ last.S = 0 ∧ last.delta = 0 ∧ last.backlog = 0) ∨
                    ∃ old, last.lastDown = some old ∧ 0 < old.val.sigma ∧
                      old.val.sigma < (M i).val.sigma)) ∧
               (∀ q : Fin K.length,
                 ¬ ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i (M i)) ∧
               (∀ q : Fin K.length, ∀ old,
                 ReferenceAcceptedUpFollowerHistory.RetainedDown (K.get q) i old →
                 old.val.sigma < (M i).val.sigma) ∧
               R[c + 1 + W.length]? = none)) ∧
            match R[c + 1 + W.length]? with
            | none => c + 1 + W.length = R.length ∧
                ReferenceCompletePhysicalHistory.completeTerminalState
                  rate source rewards C_star C_h = some (E W.length)
            | some next => next.input.state = E W.length ∧
                ReferenceCollectionPhaseHistory.laterChosen next.input = true ∧
                ∃ ledger saved,
                  (E W.length).coordinator = .collection payload ledger saved ∧
                  next.input.state.coordinator = .collection payload ledger saved ∧
                  ledger.pending = ∅ ∧
                  ∀ i : Fin (p.m - 1), ∃ r ∈ K,
                    ∃ U, ReferenceCollectionPhaseHistory.AcceptedUp r.input i U
          | _ => True
      | _ => True := by
  classical
  have hP :=
    ReferenceFirstReplacementCollectionPureUpWindowCut.complete_first_replacement_collection_pure_up_window_cut
      rate source rewards C_star C_h
  have hA :=
    ReferenceFirstReplacementCollectionPureUpDecisionLocation.complete_first_replacement_collection_pure_up_decision_location
      rate source rewards C_star C_h
  have hB :=
    ReferenceFirstReplacementCollectionUpStartedFields.complete_first_replacement_collection_up_started_fields
      rate source rewards C_star C_h
  have hR :=
    ReferenceFirstReplacementCollectionUpReceiverProvenance.complete_first_replacement_collection_up_receiver_provenance
      rate source rewards C_star C_h
  dsimp only at hP hA hB hR ⊢
  set R := ReferenceCompletePhysicalHistory.completeSuffixRecords rate source rewards C_star C_h
  set s := ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h
  set w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow R).length
  set v := w + (ReferenceCollectionPhaseHistory.collectionWindow R w).length
  set tail := ReferenceFirstReplacementLiveFollowerPrefix.continuingTail R v
  set c := v + 1 + tail.length
  cases hb : R[v]? with
  | none => trivial
  | some birth =>
    simp only [hb] at hP hA hB hR ⊢
    cases hbirth : birth.output.preparation.coordinator with
    | first _ => trivial
    | live _ _ _ _ => trivial
    | dagger => trivial
    | invalidCollectionCutoff => trivial
    | collection _ _ _ _ outcome =>
      simp only [hbirth] at hP hA hB hR ⊢
      cases outcome <;> try trivial
      rename_i core consistent birthStarted hstart instruction hinstruction output hconsistent
        clockData installed selectedBirth
      dsimp only [ReferenceActivePhysicalStep.collectionInput] at hP hA hB hR ⊢
      let payload : ReferenceActivePhysicalStep.Payload rate := installed.registers.payload
      rcases hP with ⟨hC, hX, hP⟩
      rcases hR with ⟨_, _, hR⟩
      refine ⟨hC, hX, ?_⟩
      cases hc : R[c]? with
      | none => trivial
      | some cut =>
        simp only [hc] at hP hA hB hR ⊢
        cases hcut : cut.output.preparation.coordinator with
        | first _ => trivial
        | collection _ _ _ _ _ => trivial
        | dagger => trivial
        | invalidCollectionCutoff => trivial
        | live registers owned base outcome =>
          simp only [hcut] at hP hA hB hR ⊢
          cases outcome <;> try trivial
          rename_i dispatched hs ledger hi hledger hdata hclock hpending hnone selectedCut
          dsimp only at hP hA hB hR ⊢
          let u := cut.input.time.val + 1
          let W := (R.drop (c + 1)).takeWhile
            (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)
          let K := cut :: W
          let E := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.output.next (W.take j)
          let Z := fun j => ReferenceCollectionSegmentExtraction.endpointState
            cut.input.state (K.take j)
          let M := fun i => payload.downRecord i
          rcases hP with ⟨hcalendar, hZ, hfollowers, hboundary⟩
          rcases hR with ⟨_, hreceptions, _⟩
          refine ⟨hcalendar, hZ, ?_, hboundary⟩
          have hKprefix : K <+: R.drop c := by
            obtain ⟨hci, hce⟩ := List.getElem?_eq_some_iff.mp hc
            rw [List.drop_eq_getElem_cons hci, hce]
            refine ⟨(R.drop (c + 1)).dropWhile
              (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input), ?_⟩
            simp only [K, W, List.cons_append, List.takeWhile_append_dropWhile]
          obtain ⟨initial, active, _, _, _, hInvInitial, _, _, hRuns⟩ :=
            ReferenceFirstReplacementCollectionPureUpWindowCut.source_interval_runs
              rate source rewards C_star C_h c cut hc K hKprefix
          have hInv : ∀ j, j ≤ K.length →
              ReferenceUpDecoderBankInvariant.upBankInvariant (Z j) := by
            intro j hj
            obtain ⟨span, _, hend⟩ := hRuns j hj
            change (ReferenceActivePhysicalHorizon.run initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + j) span active).finalState = Z j at hend
            rw [← hend]
            exact ReferenceUpDecoderBankInvariant.run_upBankInvariant initial source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
              (c + j) span active hInvInitial
          intro i
          rcases hfollowers i with hcurrent | habsent
          · rcases hcurrent with ⟨b, anchor, memory, horigin, hbK, hstatus, hdomain,
                hcurrent, hend, U, hfields, hsigma, hpositive, hchoices, hentries,
                hpure, hcases⟩
            refine Or.inl ⟨b, anchor, memory, horigin, hbK, hstatus, hdomain,
              hcurrent, hend, U, hfields, hsigma, hpositive, hchoices, hentries, hpure, ?_⟩
            let H := K.drop b
            let channel := (Z b).upDecoderBank i
            let Q := AffineBatchDecoder.quota p
            let need := Q - channel.pending.length + Q
            rcases hcases with hfailed | ⟨hsurvive, hsurviving⟩
            · rcases hfailed with ⟨q, reason, hbq, hbefore, hafter, hreason, hprevious,
                  hreplay, hrun, hsuffix, hcount, hsingle, hstage, hdiagnostics⟩
              exact Or.inl ⟨q, reason, hbq, hbefore, hafter, hreason, hprevious,
                hreplay, hrun, hsuffix, hcount, hsingle, hstage, hdiagnostics⟩
            · refine Or.inr ⟨hsurvive, ?_⟩
              rcases hsurviving with hshort | hthreshold
              · exact Or.inl hshort
              · rcases hthreshold with ⟨m, hm, hmH, hcount, hleast, first, last, index,
                    r, d, hfirst, hfirstLength, hwindowLength, hchronological, hequations,
                    hlast, hdecisionTime, hr, hrtime, hd, hselected, hdtime, hsample,
                    hbank, hreplay, hwindow, hafter, hraw, hexpected, hendpoint, hrawCases⟩
                let positive := physicalPositives (H.take m) i
                let window := positive.drop (Q - channel.pending.length)
                obtain ⟨hmTwo, k, hk, hkpos, hget, _hdrop, hlookup, htime,
                    hrows, hselectedRow, hrewards, hinputZ, hinputE, hsingle,
                    _hselected, hsender, _hdtime, _hsample, _hbank, _hphysicalSample,
                    heligible, _hgate, _hslot, hphysicalSlot, _hpendingCall⟩ :=
                  hA i b m last r d hbK hm hmH hcount hleast hlast hdecisionTime hr hrtime hd
                refine Or.inr ⟨m, hm, hmH, hcount, hleast, first, last, index, r, d,
                  hfirst, hfirstLength, hwindowLength, hchronological, hequations,
                  hlast, hdecisionTime, hr, hrtime, hd, hselected, hdtime, hsample,
                  hbank, hreplay, hwindow, hafter, hraw, hexpected, hendpoint,
                  hmTwo, k, hk, hkpos, hget, hlookup, htime, hrows, hselectedRow,
                  hrewards, hinputE, hsingle, hsender, heligible, ?_⟩
                rcases hrawCases with hambiguous | ⟨hrawWord, hunique⟩
                · exact Or.inl hambiguous
                · right
                  refine ⟨hrawWord, hunique, ?_⟩
                  have hnonD : r.output.next.coordinator ≠ .dagger := by
                    have hsurviveK : ∀ q : Fin K.length,
                        (K.get q).output.next.coordinator ≠ .dagger := hsurvive
                    rw [← hget]
                    exact hsurviveK k
                  have hjbound : k.val - 1 < W.length := by
                    have hki := k.isLt
                    change k.val < W.length + 1 at hki
                    omega
                  let j : Fin W.length := ⟨k.val - 1, hjbound⟩
                  have hjplus : j.val + 1 = k.val := by dsimp only [j]; omega
                  have hrW : W.get j = r := by
                    have hget' := hget
                    have hk' : k.val = j.val + 1 := hjplus.symm
                    simpa only [K, List.get_eq_getElem, hk', List.getElem_cons_succ]
                      using hget'
                  have hBrecord := hB j
                  rw [hrW] at hBrecord
                  split at hBrecord
                  · exact (hnonD (by assumption)).elim
                  · rcases hBrecord with ⟨incoming, saved, t, recording, started, diagnostic,
                        hstate, htail, hrecording, hstart, hsite, hcheck, hdiagnostic,
                        hinput, hexpectedActual, htailReception, _hnotInvalid, hstartedSigma,
                        hcutoff, hcursor, hcutCursor, hstartedPending, hmembership,
                        receivedLedger, receivedBank, finished, clockFinished,
                        hreceived, hfinish, hclock⟩
                    have hdiagnosticEq : diagnostic = d :=
                      Option.some.inj (hdiagnostic.symm.trans hd)
                    subst diagnostic
                    have hpendingPrefix : started.pending = Finset.univ \
                        (ReferenceCollectionPhaseHistory.acceptedLabels (K.take k.val)).toFinset := by
                      simpa only [hjplus] using hstartedPending
                    have hmember := hmembership heligible
                    rw [hsender, hjplus] at hmember
                    have hsigmaStarted : U.val.sigma = started.sigma := by
                      calc
                        U.val.sigma = (M i).val.sigma := hsigma
                        _ = payload.sigma.val + 1 := rfl
                        _ = started.sigma := hstartedSigma.symm
                    have haccept : CoordinatorCollectionLedger.acceptUpCheck started i U = true := by
                      simp only [CoordinatorCollectionLedger.acceptUpCheck, hcutCursor,
                        hmember.1, hsigmaStarted, decide_true, Bool.and_self]
                    -- The provenance offer and the persistent current offer are the
                    -- same function call at the same physical choice configuration.
                    have hrecordR := hreceptions k
                    rw [hget, htail] at hrecordR
                    simp only [htailReception] at hrecordR
                    rcases hrecordR with ⟨_, _, _, _, _, hofferR, _⟩
                    rw [hsender] at hofferR
                    obtain ⟨stateR, memoryR, replyR, hconfigurationR, hcheckedR,
                        _hfieldsR, hexpectedR, _hcurrentR⟩ := hofferR hphysicalSlot
                    have hbk : b ≤ k.val := by omega
                    obtain ⟨stateP, memoryP, hconfigurationP, _hstatusP, _hdownP,
                        _hreplyP, hofferP, _hpositiveP⟩ := hchoices k hbk
                    rw [hget] at hconfigurationP hofferP
                    have hconfiguration : DeclaredFollowerLocalRound.LocalConfiguration.ordinary
                        stateR memoryR = .ordinary stateP memoryP :=
                      hconfigurationR.symm.trans hconfigurationP
                    have hstateEq : stateR = stateP :=
                      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj hconfiguration).1
                    rw [hstateEq] at hcheckedR
                    have hcheckedP := (hofferP hsender hphysicalSlot).1
                    have hreplyEq : replyR = U :=
                      ActiveFollowerQueueOperation.UpOfferResult.offer.inj
                        (hcheckedR.symm.trans hcheckedP)
                    subst replyR
                    have hexpectedAligned : d.expected =
                        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) :=
                      hexpectedActual.trans hexpectedR
                    have hstartedFields : ∀ (otherRecording : CoordinatorRecordingOperation.Output p)
                        (otherStarted : ReferenceActivePhysicalStep.Ledger rate),
                        CoordinatorRecorderComplementBridge.run
                          (ReferenceActivePhysicalStep.collectionRecordingInput
                            (ReferenceActivePhysicalStep.prepare r.input)
                            t.payload t.started t.weights) = some otherRecording →
                        CoordinatorCollectionLedger.startRound t.ledger (r.input.time.val + 1)
                          (ReferenceActivePhysicalStep.collectionEnabled t.ledger r.input.time)
                          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder otherRecording) =
                            .success otherStarted →
                        otherStarted.cutoff ≤ otherStarted.cursor ∧
                          ReferenceActivePhysicalStep.upSenderIndex r.input ∈ otherStarted.pending ∧
                          U.val.sigma = otherStarted.sigma := by
                      intro otherRecording otherStarted hotherRecording hotherStart
                      have hrecordingEq : otherRecording = recording :=
                        Option.some.inj (hotherRecording.symm.trans hrecording)
                      subst otherRecording
                      have hstartedEq : otherStarted = started :=
                        CoordinatorCollectionLedger.Checked.success.inj
                          (hotherStart.symm.trans hstart)
                      subst otherStarted
                      exact ⟨hcutCursor, by rw [hsender]; exact hmember.1, hsigmaStarted⟩
                    obtain ⟨sameRecording, sameStarted, decoded, bank, hsameRecording,
                        hsameStart, hsameSite, hsameCheck, hsameInput, _haccept,
                        hfiltered, hparsed, hlocal, hmatches, hwrong, hsuccess,
                        herased, _hsameReception, haccepted⟩ :=
                      actual_replacement_collection_up_receiver_matching_word r payload incoming
                        saved t hstate htail hnonD d hd U hrawWord hexpectedAligned hstartedFields
                    have hsameRecordingEq : sameRecording = recording :=
                      Option.some.inj (hsameRecording.symm.trans hrecording)
                    subst sameRecording
                    have hsameStartedEq : sameStarted = started :=
                      Option.some.inj (hsameSite.symm.trans hsite)
                    subst sameStarted
                    rw [hsender] at herased haccepted
                    have hpair : (receivedLedger, receivedBank) = (decoded, bank) := by
                      rcases hreceived with hs | hr
                      · exact CoordinatorCollectionLedger.Checked.success.inj
                          (hs.symm.trans hsuccess)
                      · rw [hsuccess] at hr
                        cases hr
                    rcases Prod.mk.inj hpair with ⟨hreceivedLedger, hreceivedBank⟩
                    subst receivedLedger
                    subst receivedBank
                    have hrecordInv : ReferenceUpDecoderBankInvariant.upBankInvariant
                        r.input.state := by
                      rw [hinputZ]
                      exact hInv k.val (Nat.le_of_lt k.isLt)
                    obtain ⟨commitLedger, hcommitSite, _hcommitCheck, _hcommitInput,
                        _hcommitAfter, hcommitCases⟩ :=
                      ReferenceCoordinatorUpPhysicalCall.record_up_commit_cases r d hd hrecordInv
                    have hcommitLedger : commitLedger = started :=
                      Option.some.inj (hcommitSite.symm.trans hsite)
                    subst commitLedger
                    rcases hcommitCases with ⟨hinvalid, _⟩ | ⟨out, hout, hbankOut, hnextBank⟩
                    · rw [hsuccess] at hinvalid
                      cases hinvalid
                    · have houtEq : out = (decoded, bank) := by
                        rcases hout with hs | hr
                        · exact CoordinatorCollectionLedger.Checked.success.inj
                            (hs.symm.trans hsuccess)
                        · rw [hsuccess] at hr
                          cases hr
                      subst out
                      have hnextState : r.output.next = Z (k.val + 1) := by
                        have hlink : (K.get k).output.next = Z (k.val + 1) := (hZ.2.2 k).2
                        rw [hget] at hlink
                        exact hlink
                      have hkEnd : k.val + 1 = b + m := by omega
                      have hendpointBank : (Z (b + m)).upDecoderBank = bank := by
                        rw [← hkEnd, ← hnextState]
                        exact hnextBank
                      have hchannel : bank i = ⟨[], channel.completed ++ [first, window]⟩ := by
                        rw [← hendpointBank]
                        exact hendpoint
                      exact ⟨incoming, saved, t, recording, started, decoded, bank, finished,
                        clockFinished, hstate, htail, hrecording, hstart, hsite, hcheck,
                        hinput, htailReception, hstartedSigma, hcutoff, hcursor, hcutCursor,
                        hpendingPrefix, hmember.1, hmember.2, hsigmaStarted, haccept,
                        hfiltered, hparsed, hlocal, hmatches, hwrong, hsuccess, herased,
                        hbankOut, hnextBank, hendpointBank, hchannel, hfinish, hclock, haccepted⟩
          · exact Or.inr habsent

end Bandits.Support.ReferenceFirstReplacementCollectionPureUpAcceptanceRoot

end
