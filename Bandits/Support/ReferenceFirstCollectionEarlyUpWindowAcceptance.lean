/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionEarlyUpSenderReceiver
public import Bandits.Support.ReferenceFirstCollectionLateUpWindowAcceptance

/-!
# Actual early-retained-DOWN second UP window and acceptance join

Sources: `sources/zip4/manuscript/05_binary_transport.tex:20-53,70-124`,
`sources/zip4/manuscript/06_interruptions.tex:164-177,246-295,327-348`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:92-109,139-157`.

This consumer starts with the actual early UP sender/receiver telescope. It
keeps its produced message and actual collection history, then asks for a local
completed-window count and uniqueness condition at an ordinary endpoint. The
second interval starts at the cutoff record and carries its actual UP bank,
including the carried pending entries and completed history. Every physical
round remains in the replay, including zero observations and closed gates.

The conditional private lemmas expose their inputs literally. The public root
produces those inputs from E and the actual launch-bank invariant; only the
local positive-count and whole-window uniqueness events remain conditional.
No service attainment, source numerical register identity, original-execution
probability statement, or manuscript closure is asserted.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionEarlyUpWindowAcceptance

local instance earlyWindowPropDecidable (q : Prop) : Decidable q :=
  Classical.propDecidable q

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem connected_endpoint_unique
    {initial left right : ReferenceActivePhysicalStep.State p rate}
    {records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))}
    (hl : ReferenceActivePhysicalHorizon.Connected initial records left)
    (hr : ReferenceActivePhysicalHorizon.Connected initial records right) :
    left = right := by
  induction records generalizing initial left right with
  | nil =>
      change left = initial at hl
      change right = initial at hr
      exact hl.trans hr.symm
  | cons record rest ih =>
      simp only [ReferenceActivePhysicalHorizon.Connected] at hl hr
      exact ih hl.2 hr.2

private theorem run_prefix_records
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
      hspan active).records.take n =
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
        (by omega) active).records := by
  obtain ⟨suffix, heq⟩ := ReferenceCollectionPhaseHistory.run_records_prefix
    initial rows selected rewards start n (total - n) (by omega) active
  have hcount : n + (total - n) = total := Nat.add_sub_of_le hn
  simp only [hcount] at heq
  rw [heq, List.take_append_of_le_length (by
    rw [ReferenceActivePhysicalHorizon.run_record_count])]
  apply List.take_of_length_le
  rw [ReferenceActivePhysicalHorizon.run_record_count]

private theorem run_prefix_endpoints
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (n : ℕ) (hn : n < total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start n
      (by omega) active).finalState =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
          hspan active).records[n]'(by
            rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hn)).input.state ∧
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1)
      (by omega) active).finalState =
        ((ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
          hspan active).records[n]'(by
            rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hn)).output.next := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  let prefixRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start n (by omega) active
  let nextPrefix := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (n + 1) (by omega) active
  have hconnected := ReferenceActivePhysicalHorizon.run_connected initial rows selected rewards
    start total hspan active
  have hnFull : n < full.records.length := by
    dsimp [full]
    rw [ReferenceActivePhysicalHorizon.run_record_count]
    exact hn
  have htake := ReferenceFollowerReplyChronology.connected_take_to_input hconnected n hnFull
  have hprefix := run_prefix_records initial rows selected rewards start total hspan active n (by omega)
  have hprefixEq : full.records.take n = prefixRun.records := by
    simpa [full, prefixRun] using hprefix
  have hinput := connected_endpoint_unique prefixRun.connected (by
    rw [← hprefixEq]
    exact htake)
  have htakeSucc : full.records.take (n + 1) = full.records.take n ++ [full.records[n]] := by
    rw [List.take_add_one]
    simp [hnFull]
  have hchainNext : ReferenceActivePhysicalHorizon.Connected initial
      (full.records.take (n + 1)) (full.records[n].output.next) := by
    rw [htakeSucc]
    exact ReferenceActivePhysicalHorizon.Connected.append_one
      (full.records.take n) full.records[n] htake rfl
  have hprefixNext := run_prefix_records initial rows selected rewards start total hspan active
    (n + 1) (by omega)
  have hprefixNextEq : full.records.take (n + 1) = nextPrefix.records := by
    simpa [full, nextPrefix] using hprefixNext
  have hnext := connected_endpoint_unique nextPrefix.connected (by
    rw [← hprefixNextEq]
    exact hchainNext)
  exact ⟨hinput, hnext⟩

private theorem positive_entry_details
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (i : Fin (p.m - 1))
    (hchronological : records.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val))
    (entry : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
    (hentry : entry ∈ AffineBatchDecoder.positives p
      (ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i)
      (records.map fun r => r.input.time)) :
    ∃ (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
      record ∈ records ∧ record.input.time = entry.time ∧
      record.output.coordinator.up = some diagnostic ∧
      diagnostic.input.selectedFollower = i ∧
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput diagnostic.input) ∧
      PublicDiscreteDraws.slotDraw (record.input.row.2 record.input.time).1 =
        PublicDiscreteDraws.upSlot ∧
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (record.input.row.2 record.input.time).1 = i ∧
      entry.sample = (record.input.row.2 record.input.time).2 (1, i) ∧
      ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
  classical
  let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace records i
  obtain ⟨htime, heligible, hsample⟩ :=
    (AffineBatchDecoder.mem_positives_iff p trace (records.map fun r => r.input.time) entry).mp hentry
  obtain ⟨record, hrecord, htime⟩ := List.mem_map.mp htime
  obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hrecord
  have htrace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace_at_record
    records i hchronological record hrecord
  have hfocal : AffineBatchDecoder.eligible
      (ReferenceCoordinatorUpIntervalWindow.recordFocalInput record i) := by
    rw [← htrace, htime]
    exact heligible
  obtain ⟨diagnostic, hdiagnostic, hselected⟩ :
      ∃ diagnostic, record.output.coordinator.up = some diagnostic ∧
        diagnostic.input.selectedFollower = i := by
    cases hcall : record.output.coordinator.up with
    | none =>
        simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall,
          ReferenceCoordinatorUpIntervalWindow.administrativeNoCallInput,
          AffineBatchDecoder.eligible] at hfocal
    | some diagnostic =>
        by_cases hi : diagnostic.input.selectedFollower = i
        · exact ⟨diagnostic, rfl, hi⟩
        · simp [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hcall, hi,
            ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput,
            AffineBatchDecoder.eligible] at hfocal
  have htraceInput : trace record.input.time =
      CoordinatorUpReception.roundInput diagnostic.input := by
    change trace record.input.time = _ at htrace
    rw [htrace]
    simp only [ReferenceCoordinatorUpIntervalWindow.recordFocalInput, hdiagnostic,
      hselected, ReferenceCoordinatorUpDecoderReplay.retainedUpRoundInput, ite_true]
  have hround : AffineBatchDecoder.eligible
      (CoordinatorUpReception.roundInput diagnostic.input) := by
    rw [← htraceInput, htime]
    exact heligible
  obtain ⟨ledger, _hsite, _hledger, _hbank, _htime, _hobs, hselectedIndex,
      hactualSample, hslot, _henabled, hselectedFlag, hroundSample, _hreward,
      _hfeedback⟩ := ReferenceCoordinatorUpPhysicalCall.record_retained_up_input_fields
    record diagnostic hdiagnostic
  have hgate : ledger.cutoff ≤ record.input.time.val + 1 ∧
      diagnostic.input.slot = PublicDiscreteDraws.upSlot ∧
      diagnostic.input.selectedFollower ∈ ledger.pending := by
    have hs := hround.1
    rw [hselectedFlag] at hs
    exact of_decide_eq_true hs
  have hslotDraw : PublicDiscreteDraws.slotDraw
      (record.input.row.2 record.input.time).1 = PublicDiscreteDraws.upSlot :=
    hslot.symm.trans hgate.2.1
  have hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (record.input.row.2 record.input.time).1 = i := by
    rw [← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    exact hselectedIndex.symm.trans hselected
  have hchannel : CoordinatorUpMeasurability.selectedChannelFollower
      ((record.input.rows record.input.selected).2 record.input.time) = i := by
    apply Fin.ext
    rw [CoordinatorUpMeasurability.selectedChannelFollower_val,
      ← CoordinatorUpMeasurability.selectedFollowerIndex_eq_draw]
    simpa only [ContinuousLearningRows.d] using congrArg Fin.val
      (hselectedIndex.symm.trans hselected)
  have hsampleEq : entry.sample =
      (record.input.row.2 record.input.time).2 (1, i) := by
    rw [hsample, ← htime, htraceInput, hroundSample, hactualSample, hchannel]
    rfl
  have hpositive : ReferenceActiveAffinePositiveTest.upPositive record.input = true := by
    rw [ReferenceActiveAffinePositiveTest.record_upPositive, hdiagnostic]
    simpa only [ReferenceActiveAffinePositiveTest.upDiagnosticPositive] using
      (decide_eq_true hround)
  exact ⟨record, diagnostic, hrecord, htime, hdiagnostic, hselected,
    hround, hslotDraw, hdraw, hsampleEq, hpositive⟩

private theorem cutoff_matching_word
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hcut : ReferenceCollectionPhaseHistory.cutoffChosen record.input = true)
    (hordinary : record.output.next.coordinator ≠ .dagger)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hindex : ReferenceActivePhysicalStep.upSenderIndex record.input = i)
    (L : ReferenceActivePhysicalStep.Ledger rate)
    (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some L)
    (hdiagnostic : record.output.coordinator.up = some diagnostic)
    (hinput : diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L)
    (hraw : diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hexpected : diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (haccept : CoordinatorCollectionLedger.acceptUpCheck L i U = true) :
    ∃ (tail : ReferenceCollectionPhaseHistory.Tail record.input)
      (recording : CoordinatorRecordingOperation.Output p)
      (decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p),
      ReferenceCollectionPhaseHistory.executedTail record.input = some tail ∧
      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare record.input) tail.payload tail.started tail.weights) =
        some recording ∧
      CoordinatorCollectionLedger.startRound tail.ledger (record.input.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled tail.ledger record.input.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) = .success L ∧
      ReferenceCollectionPhaseHistory.filteredParsed record.input L = some U ∧
      diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
      diagnostic.rawMatches = true ∧
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare record.input) L).result = .success (decoded, bank) ∧
      ReferenceCollectionPhaseHistory.AcceptedUp record.input i U := by
  classical
  have hcodec : CoordinatorCollectionLedger.codecParams p rate.eta.val =
      ReferencePrelaunchFollower.codecParams p rate.eta := rfl
  cases hcodec
  obtain ⟨tail, recordingCut, Lcut, dcut, _received, _bank, _finished, _clock,
      htail, _hpost, hsiteCut, _htailPending, _htailSigma, _htailCutoff, _htailCursor,
      _htailPhase, _hstartedPending, hrecordingCut, hstartCut, _hLpending, _hLsigma,
      _hLcutoff, _hLcursor, hcheckCut, hinputCut, hdiagnosticCut,
      _htailReception, hnotInvalid, _hresultCases, _hfinish, _hclock, _hdecoderCut,
      hrawCut, hparsedCut, hlocalCut, hexpectedCut, hrawMatchesCut, _hbankCut,
      _htimeCut, _hsampleCut, _hobservationCut, _hwrongCut⟩ :=
    ReferenceCutoffUpReceiverLocal.actual_ordinary_cutoff_up_receiver record hcut hordinary
  have hL : Lcut = L := Option.some.inj (hsiteCut.symm.trans hsite)
  have hd : dcut = diagnostic := Option.some.inj (hdiagnosticCut.symm.trans hdiagnostic)
  subst Lcut
  subst dcut
  have hcheck : CoordinatorUpReception.receptionInputCheck
      (ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input L) = true := hcheckCut
  have hrawDiagnostic :
      (CoordinatorUpReception.decoderTransition diagnostic.input).2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    rw [← hrawCut, hraw]
  have hexpectedAtPrepared : ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    rw [← hexpectedCut, hexpected]
  have hflatWord : ActiveFollowerArmChoice.offeredUpWord rate.eta U =
      OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)
        (OrdinaryMessageCodec.encodeUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val) U) := by
    unfold ActiveFollowerArmChoice.offeredUpWord
    have hcodec := ReferenceUpReception.ledgerCodecParams_eq_followerCodecParams rate
    cases hcodec
    rfl
  have hparsedWord : CoordinatorUpReception.parseDecoderOutput
      (some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) = some U := by
    rw [CoordinatorUpReception.parseDecoderOutput, hflatWord]
    change OrdinaryMessageCodec.parseUp
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)
      (some ((OrdinaryMessageCodec.wordEquivFlat
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)).symm
          ((OrdinaryMessageCodec.wordEquivFlat
            (CoordinatorCollectionLedger.codecParams p rate.eta.val))
            (OrdinaryMessageCodec.encodeUp
              (CoordinatorCollectionLedger.codecParams p rate.eta.val) U)))) = some U
    rw [Equiv.symm_apply_apply]
    exact OrdinaryMessageCodec.parseUp_encode
      (CoordinatorCollectionLedger.codecParams p rate.eta.val) U
  have hrawParsed : ReferenceUpReception.rawParsedOutput rate diagnostic.input = some U := by
    change CoordinatorUpReception.parseDecoderOutput
      (CoordinatorUpReception.decoderTransition diagnostic.input).2 = some U
    rw [hrawDiagnostic]
    exact hparsedWord
  have hrawAtRow :
      (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate record.input.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare record.input) L) record.input.time)).2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    simpa [hinput, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hrawDiagnostic
  have hrawEqExpected : diagnostic.raw = diagnostic.expected := hraw.trans hexpected.symm
  have hrawMatches : diagnostic.rawMatches = true := by
    rw [hrawMatchesCut]
    simp [hrawEqExpected]
  have hlocal : diagnostic.locallyAccepted = true := by
    rw [hlocalCut]
    have hlocalRaw : ReferenceUpReception.rawParsedLocalAcceptance rate diagnostic.input = true := by
      rw [ReferenceUpReception.rawParsedLocalAcceptance, hrawParsed, hinput]
      change CoordinatorCollectionLedger.acceptUpCheck L
        (ReferenceActivePhysicalStep.upSenderIndex record.input) U = true
      rw [hindex]
      exact haccept
    exact hlocalRaw
  have hfiltered : ReferenceUpReception.filterRawByExpected
      (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate record.input.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare record.input) L) record.input.time)).2
      (ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare record.input)) =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    rw [hrawAtRow]
    rw [hexpectedAtPrepared]
    exact ReferenceUpReception.filterRawByExpected_eq_raw_of_eq _ _ rfl
  have hfilteredParsed : ReferenceCollectionPhaseHistory.filteredParsed record.input L = some U := by
    change CoordinatorUpReception.parseDecoderOutput
      (ReferenceUpReception.filterRawByExpected
        (CoordinatorUpReception.decoderTransition
          (ReferenceUpReception.receptionInputAtRow rate record.input.row
            (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare record.input) L) record.input.time)).2
        (ReferenceActivePhysicalStep.upExpected
          (ReferenceActivePhysicalStep.prepare record.input))) = some U
    rw [hfiltered]
    exact hparsedWord
  let prepared := ReferenceActivePhysicalStep.prepare record.input
  let inputs := ReferenceActivePhysicalStep.upInputs prepared L
  let receiverInput := ReferenceUpReception.receptionInputAtRow rate record.input.row inputs record.input.time
  have hreceiverCheck : CoordinatorUpReception.receptionInputCheck receiverInput = true := by
    simpa [receiverInput, inputs, prepared, ReferenceCoordinatorUpPhysicalCall.actualUpInput,
      ReferenceActivePhysicalStep.upInputs, ReferenceUpReception.receptionInputAtRow,
      CoordinatorUpMeasurability.receptionInputAtRow] using hcheck
  have hdomain : CoordinatorUpReception.receptionInputDomain receiverInput :=
    (CoordinatorUpReception.receptionInputCheck_eq_true_iff receiverInput).mp hreceiverCheck
  have hordinaryMatch : (CoordinatorUpReception.decoderTransition receiverInput).2 =
      ReferenceActivePhysicalStep.upExpected prepared := by
    have hrawActual : (CoordinatorUpReception.decoderTransition receiverInput).2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
      simpa [receiverInput, inputs, prepared] using hrawAtRow
    have hexpectedActual : ReferenceActivePhysicalStep.upExpected prepared =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
      simpa [prepared] using hexpectedAtPrepared
    exact hrawActual.trans hexpectedActual.symm
  have hactualOrdinary :
      (ReferenceActivePhysicalStep.receiveUp prepared L).result =
        CoordinatorUpReception.receiveUp receiverInput := by
    simpa [prepared, inputs, receiverInput] using
      ReferenceActivePhysicalStep.receiveUp_eq_ordinary_of_no_mismatch prepared L hordinaryMatch
  have hparsedReceiver : CoordinatorUpReception.parsedDecoderOutput receiverInput = some U := by
    unfold CoordinatorUpReception.parsedDecoderOutput
    have hrawReceiver : (CoordinatorUpReception.decoderTransition receiverInput).2 =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
      simpa [receiverInput, inputs, prepared] using hrawAtRow
    rw [hrawReceiver]
    exact hparsedWord
  have hacceptReceiver : CoordinatorCollectionLedger.acceptUpCheck receiverInput.ledger
      receiverInput.selectedFollower U = true := by
    change CoordinatorCollectionLedger.acceptUpCheck L
      (ReferenceActivePhysicalStep.upSenderIndex record.input) U = true
    rw [hindex]
    exact haccept
  rcases CoordinatorUpReception.receptionInputDomain_parts receiverInput hdomain with
    ⟨hledgerValid, _, hphase, hcutoff, hcutoffCursor, hcursorT, _, _⟩
  have hdecodeInput :
      CoordinatorCollectionLedger.validLedgerCheck receiverInput.ledger = true ∧
        receiverInput.ledger.phase = CoordinatorCollectionLedger.Phase.started ∧
        1 ≤ receiverInput.ledger.cutoff ∧ receiverInput.ledger.cutoff ≤ receiverInput.ledger.cursor ∧
        receiverInput.ledger.cursor ≤ p.T :=
    ⟨hledgerValid, hphase, hcutoff, hcutoffCursor, hcursorT⟩
  have hdecodeNotRejected : ∀ out,
      CoordinatorCollectionLedger.decodeUp receiverInput.ledger receiverInput.selectedFollower
        (CoordinatorUpReception.parsedDecoderOutput receiverInput) ≠ .rejected out := by
    intro out hdecode
    rw [hparsedReceiver] at hdecode
    unfold CoordinatorCollectionLedger.decodeUp at hdecode
    rw [dite_eq_left hdecodeInput] at hdecode
    dsimp only at hdecode
    rw [ite_eq_left hacceptReceiver] at hdecode
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
  have hreceiveDecode : CoordinatorUpReception.receiveUp receiverInput =
      CoordinatorUpReception.packDecodeResult
        (CoordinatorCollectionLedger.decodeUp receiverInput.ledger
          receiverInput.selectedFollower
          (CoordinatorUpReception.parsedDecoderOutput receiverInput))
        (CoordinatorUpReception.decoderBankAfter receiverInput) := by
    rw [CoordinatorUpReception.receiveUp_eq_existing_decodeUp receiverInput hreceiverCheck]
    rfl
  have hsuccess : ∃ decoded bank,
      (ReferenceActivePhysicalStep.receiveUp prepared L).result = .success (decoded, bank) := by
    cases hdecode : CoordinatorCollectionLedger.decodeUp receiverInput.ledger
        receiverInput.selectedFollower
          (CoordinatorUpReception.parsedDecoderOutput receiverInput) with
    | success decoded =>
        refine ⟨decoded, CoordinatorUpReception.decoderBankAfter receiverInput, ?_⟩
        have hordinarySuccess : CoordinatorUpReception.receiveUp receiverInput =
            .success (decoded, CoordinatorUpReception.decoderBankAfter receiverInput) := by
          rw [hreceiveDecode, hdecode]
          rfl
        exact hactualOrdinary.trans hordinarySuccess
    | rejected out => exact (hdecodeNotRejected out hdecode).elim
    | invalid =>
        have hordinaryInvalid : CoordinatorUpReception.receiveUp receiverInput = .invalid := by
          rw [hreceiveDecode, hdecode]
          rfl
        have hactualInvalid : (ReferenceActivePhysicalStep.receiveUp prepared L).result = .invalid :=
          hactualOrdinary.trans hordinaryInvalid
        exact (hnotInvalid hactualInvalid).elim
  rcases hsuccess with ⟨decoded, bank, hsuccess⟩
  have haccepted : ReferenceCollectionPhaseHistory.AcceptedUp record.input i U := by
    refine ⟨tail, recordingCut, L, decoded, bank, htail, hrecordingCut, hstartCut,
      hsuccess, hfilteredParsed, ?_⟩
    change i = ReferenceActivePhysicalStep.upSenderIndex record.input
    exact hindex.symm
  refine ⟨tail, recordingCut, decoded, bank, htail, hrecordingCut, hstartCut,
    hfilteredParsed, ?_, hlocal, hrawMatches, hsuccess, haccepted⟩
  rw [hparsedCut]
  exact hrawParsed

private theorem run_count_eq
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hl : start + left ≤ p.T) (hr : start + right ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (heq : left = right) :
    ReferenceActivePhysicalHorizon.run initial rows selected rewards start left hl active =
      ReferenceActivePhysicalHorizon.run initial rows selected rewards start right hr active := by
  subst right
  rfl

private theorem interval_eq_collection_take
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start total : ℕ) (hspan : start + total ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (front : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (suffix B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hsplit : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start total
      hspan active).records = front ++ cut :: suffix)
    (hBsplit : B = cut :: ((ReferenceActivePhysicalHorizon.run initial rows selected rewards
      start total hspan active).records.drop (front.length + 1)).takeWhile
        (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input))
    (n : ℕ) (hn : n ≤ B.length) (hbound : front.length + n ≤ total) :
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (front.length + n)
      (by omega) active).records.drop front.length = B.take n := by
  let full := ReferenceActivePhysicalHorizon.run initial rows selected rewards start total hspan active
  have hdrop : full.records.drop front.length = cut :: suffix := by
    rw [hsplit, List.drop_append_length]
  have hdropSuffix : full.records.drop (front.length + 1) = suffix := by
    rw [List.drop_add_one_eq_tail_drop, hdrop]
    rfl
  have hBprefix : B <+: full.records.drop front.length := by
    rw [hBsplit, hdropSuffix, hdrop]
    exact List.cons_prefix_cons.mpr ⟨rfl, List.takeWhile_prefix _⟩
  have hrecords := run_prefix_records initial rows selected rewards start total hspan active
    (front.length + n) hbound
  rw [← hrecords, List.drop_take, Nat.add_sub_cancel_left]
  have hBtake := List.prefix_iff_eq_take.mp hBprefix
  rw [hBtake, List.take_take, Nat.min_eq_left hn]

private theorem positive_count_rounds_nonempty
    (trace : AffineBatchDecoder.Trace p) (rounds : List (Fin p.T))
    (channel : AffineBatchDecoder.State p.T (AffineBatchDecoder.width p))
    (hCount : (AffineBatchDecoder.positives p trace rounds).length =
      AffineBatchDecoder.quota p - channel.pending.length + AffineBatchDecoder.quota p) :
    0 < rounds.length := by
  cases rounds with
  | nil =>
      simp only [AffineBatchDecoder.positives_nil, List.length_nil] at hCount
      have hquota := AffineBatchDecoder.quota_pos p
      omega
  | cons time rest => exact Nat.zero_lt_succ _

/-- A pointwise sender family supplies equations only at the actual positive
calls. The root below produces the whole family from E and endpoint absorption. -/
private theorem saved_window_of_senders
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a n : ℕ) (hspanA : start + a ≤ p.T) (hspan : start + (a + n) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hOrd : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n)
      hspan active).finalState.coordinator ≠ .dagger)
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hn : n ≤ B.length)
    (hintervalEq : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n)
      hspan active).records.drop a = B.take n)
    (originalRecords : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hlookup : ∀ k : Fin B.length, originalRecords[a + k.val]? = some B[k.val])
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hseed : AffineBatchDecoder.collected (initial.upDecoderBank i) = [])
    (hsender : ∀ k : Fin B.length, k.val < n →
      PublicDiscreteDraws.slotDraw (B[k.val].input.row.2 B[k.val].input.time).1 =
        PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (B[k.val].input.row.2 B[k.val].input.time).1 = i →
      ReferenceActiveAffinePositiveTest.upSent B[k.val].input =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare B[k.val].input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hreceiver : ∀ k : Fin B.length,
      let r := B[k.val]
      r.output.next.coordinator ≠ .dagger →
      ∀ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      r.output.coordinator.up = some d →
      AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) →
      PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i →
      ∃ (Lsite received : ReferenceActivePhysicalStep.Ledger rate)
        (bank : CoordinatorUpReception.UpDecoderBank p),
        ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some Lsite ∧
        d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input Lsite ∧
        Lsite.pending = Finset.univ \
          (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset ∧
        ((ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) Lsite).result =
            .success (received, bank) ∨
          (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) Lsite).result =
            .rejected (received, bank)) ∧
        d.expected = ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) ∧
        CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
        (d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) →
          d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) →
          ReferenceCollectionPhaseHistory.filteredParsed r.input Lsite = some U ∧
          d.parsed = some U ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
          ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
            (acceptedBank : CoordinatorUpReception.UpDecoderBank p),
            (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) Lsite).result =
              .success (decoded, acceptedBank) ∧
            ReferenceCollectionPhaseHistory.AcceptedUp r.input i U ∧
            ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i)) :
    let Cn := ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n) hspan active
    let preRun := ReferenceActivePhysicalHorizon.run initial rows selected rewards start a hspanA active
    let interval := Cn.records.drop a
    let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
    let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
      initial rows selected rewards start a (a + n) hspan active
    let positive := AffineBatchDecoder.positives p trace rounds
    let channel := preRun.finalState.upDecoderBank i
    let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
    positive.length = AffineBatchDecoder.quota p - channel.pending.length + AffineBatchDecoder.quota p →
    ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
      (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
      (index : Fin rounds.length)
      (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
    let decoderBefore := AffineBatchDecoder.run p trace (rounds.take index.val) channel
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
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
    ReferenceActivePhysicalHorizon.Connected preRun.finalState
      (interval.take index.val) record.input.state ∧
    record.input.state.upDecoderBank =
      ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
        (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (interval.take index.val)) ∧
    diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
    decoderBefore = diagnostic.input.upDecoderBank i ∧
    decoderBefore.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
    (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
    (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
      channel.completed ++ [first, window] ∧
    diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
    diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
    diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
    CoordinatorUpReception.decoderTransition diagnostic.input =
      (⟨[], channel.completed ++ [first, window]⟩, AffineBatchDecoder.batchOutput window) ∧
    AffineBatchDecoder.run p trace rounds channel = ⟨[], channel.completed ++ [first, window]⟩ ∧
    AffineBatchDecoder.run p trace rounds channel = Cn.finalState.upDecoderBank i ∧
    (∀ entry, entry ∈ window →
      AffineBatchDecoder.equation entry.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
    AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    ∃ (k : Fin B.length) (Lsite : ReferenceActivePhysicalStep.Ledger rate)
      (received : ReferenceActivePhysicalStep.Ledger rate)
      (receivedBank : CoordinatorUpReception.UpDecoderBank p),
      record = B[k.val] ∧
      originalRecords[a + k.val]? = some record ∧
      ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some Lsite ∧
      diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input Lsite ∧
      Lsite.pending = Finset.univ \
        (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset ∧
      ((ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
            .success (received, receivedBank) ∨
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
            .rejected (received, receivedBank)) ∧
      ((∃! word, AffineBatchDecoder.satisfies
          (AffineBatchDecoder.samples window) word) →
        diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
        diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
        CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
        OrdinaryMessageCodec.acceptUp
          (CoordinatorCollectionLedger.codecParams p rate.eta.val)
          Lsite.cutoff Lsite.cursor i.val
          (CoordinatorCollectionLedger.pendingNaturalLabels Lsite) Lsite.sigma U ∧
        ReferenceCollectionPhaseHistory.filteredParsed record.input Lsite = some U ∧
        diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
        diagnostic.rawMatches = true ∧
        ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
          (bank : CoordinatorUpReception.UpDecoderBank p),
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
              .success (decoded, bank) ∧
          ReferenceCollectionPhaseHistory.AcceptedUp record.input i U ∧
          ReferenceCollectionPhaseHistory.acceptedLabel record.input = some i) := by
  intro Cn preRun interval trace rounds positive channel window hCount
  obtain ⟨first, last, index, record, diagnostic, hfirst, hfirstLen, hwindowLen,
    hwindowPairwise, hlast, hdecision, hindexRound, hrecordMem, hrecordTime,
    hdiagnostic, hselected, hdiagnosticTime, hlastEntry, hsample, hledgerFacts,
    hconnectedCut, hbankReplay, hdiagnosticBank, hbefore, hbeforePending,
    htransitionPending, htransitionCompleted, hdecoderAfter, hrawTransition,
    hrawBatch, htransitionPair, hrunReplay, hfinalBank⟩ :=
      ReferenceFirstCollectionLateUpSecondWindow.run_interval_saved_cut_exact
        rate initial rows selected rewards start a (a + n) (Nat.le_add_right a n)
        hspan hspanA active hinitial hOrd i hseed hCount
  obtain ⟨callLedger, hcallSite, hcallCheck, hcallInput, _hcallFields⟩ := hledgerFacts
  have hrounds := ReferenceCoordinatorUpIntervalWindow.run_interval_rounds_chronological
    initial rows selected rewards start a (a + n) (Nat.le_add_right a n) hspan active hinitial hOrd
  have hchronological : interval.Pairwise
      (fun earlier later => earlier.input.time.val < later.input.time.val) := by
    have hvalues := List.pairwise_map.mpr hrounds
    have htimeValues : (interval.map fun r => r.input.time.val).Pairwise LT.lt := by
      simpa only [ReferenceCoordinatorUpIntervalWindow.intervalRounds,
        ReferenceCoordinatorUpIntervalWindow.intervalRecords, List.map_map,
        Function.comp_def] using hvalues
    exact List.pairwise_map.mp htimeValues
  have hdetails : ∀ entry, entry ∈ window →
      ∃ (k : Fin B.length)
        (original : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
        (d : ReferenceActivePhysicalStep.UpDiagnostic p rate),
        original = B[k.val] ∧ original ∈ interval ∧ original.input.time = entry.time ∧
        AffineBatchDecoder.equation entry.sample (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
        ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare original.input) =
          some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
        original.output.coordinator.up = some d ∧
        AffineBatchDecoder.eligible (CoordinatorUpReception.roundInput d.input) ∧
        PublicDiscreteDraws.slotDraw (original.input.row.2 original.input.time).1 = PublicDiscreteDraws.upSlot ∧
        PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (original.input.row.2 original.input.time).1 = i := by
    intro entry hentry
    obtain ⟨original, d, hmem, htime, hup, _hselected, heligible, hslot, hdraw, hsampleEntry, hpositive⟩ :=
      positive_entry_details interval i hchronological entry (List.mem_of_mem_drop hentry)
    have hmemTake : original ∈ B.take n := by rw [← hintervalEq]; exact hmem
    obtain ⟨kval, hkTake, hgetTake⟩ := List.mem_iff_getElem.mp hmemTake
    have hkN : kval < n := lt_of_lt_of_le hkTake (List.length_take_le _ _)
    let k : Fin B.length := ⟨kval, hkN.trans_le hn⟩
    have hBget : B[k.val] = original := by simpa only [List.getElem_take] using hgetTake
    have hsentPair := hsender k hkN (by rw [hBget]; exact hslot) (by rw [hBget]; exact hdraw)
    rw [hBget] at hsentPair
    have hhash := ReferenceUpPhysicalHashRule.upPositive_hash_one original.input
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) hsentPair.1 hpositive
    have hsenderIndex : ReferenceActivePhysicalStep.upSenderIndex original.input = i := by
      rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw]
    have hequation : AffineBatchDecoder.equation entry.sample
        (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
      rw [hsampleEntry]
      exact (AffineBatchDecoder.equation_iff_affineHash _ _).2 (by rw [hsenderIndex] at hhash; exact hhash)
    exact ⟨k, original, d, hBget.symm, hmem, htime, hequation, hsentPair.2, hup, heligible, hslot, hdraw⟩
  have hequations : ∀ entry, entry ∈ window → AffineBatchDecoder.equation entry.sample
      (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    intro entry hentry
    obtain ⟨_k, _r, _d, _hk, _hm, _ht, heq, _rest⟩ := hdetails entry hentry
    exact heq
  have hsolves := (AffineBatchDecoder.satisfies_samples_iff window _).2 hequations
  obtain ⟨k, original, d, hBrecord, hmem, htime, _heq, hexpected, hup, heligible, hslot, hdraw⟩ :=
    hdetails last hlast
  have hrecordEq : original = record :=
    ReferenceAssignmentPayloadChronology.run_records_time_injective initial rows selected rewards
      start (a + n) hspan active (List.mem_of_mem_drop hmem) (List.mem_of_mem_drop hrecordMem)
      (congrArg Fin.val (htime.trans hrecordTime.symm))
  rw [hrecordEq] at hBrecord hexpected hup hslot hdraw
  have hdiagEq : d = diagnostic := Option.some.inj (hup.symm.trans hdiagnostic)
  subst d
  have hcut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut initial rows selected rewards start a (a + n)
    (Nat.le_add_right a n) hspan active hinitial hOrd
  have hrecordOrd := hcut.2.2.2.2.2.2 record (List.mem_of_mem_drop hrecordMem)
  have hreceiverAt := hreceiver k
  rw [← hBrecord] at hreceiverAt
  obtain ⟨Lsite, received, receivedBank, hsite, hinput, hpending, hcases,
    hexpectedReceiver, haccept, hmatching⟩ :=
      hreceiverAt hrecordOrd diagnostic hdiagnostic heligible hslot hdraw
  refine ⟨first, last, index, record, diagnostic, hfirst, hfirstLen, hwindowLen,
    hwindowPairwise, hlast, hdecision, hindexRound, hrecordMem, hrecordTime,
    hdiagnostic, hselected, hdiagnosticTime, hlastEntry, hsample,
    ⟨callLedger, hcallSite, hcallCheck, hcallInput⟩, hconnectedCut, hbankReplay,
    hdiagnosticBank, hbefore, hbeforePending, htransitionPending, htransitionCompleted,
    hdecoderAfter, hrawTransition, hrawBatch, htransitionPair, hrunReplay, hfinalBank,
    hequations, hsolves, k, Lsite, received, receivedBank, hBrecord,
    (hlookup k).trans (congrArg some hBrecord.symm), hsite, hinput, hpending, hcases, ?_⟩
  intro hunique
  obtain ⟨word, _hword, hwordUnique⟩ := hunique
  have hbatchWord : AffineBatchDecoder.batchOutput window =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
    apply (AffineBatchDecoder.batchOutput_eq_some_iff window _).2
    refine ⟨hequations, ?_⟩
    intro candidate hc
    exact (hwordUnique candidate ((AffineBatchDecoder.satisfies_samples_iff window candidate).2 hc)).trans
      (hwordUnique _ hsolves).symm
  have hrawWord := hrawBatch.trans hbatchWord
  have hexpectedWord := hexpectedReceiver.trans hexpected
  exact ⟨hrawWord, hexpectedWord, haccept,
    (CoordinatorCollectionLedger.acceptUpCheck_iff Lsite i U).mp haccept,
    hmatching hrawWord hexpectedWord⟩

private theorem selected_sender_pair
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (i : Fin (p.m - 1)) (choice : ReferencePrelaunchFollower.State p rate.eta)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hselected : ∀ (_hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 =
        PublicDiscreteDraws.upSlot)
      (_hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (r.input.row.2 r.input.time).1 = i),
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
        (r.input.state.activations i) r.input.time choice = .offer U ∧
      ActiveFollowerQueueOperation.checkedUpOffer rate.eta
        (ReferenceFollowerFixedReply.actualChoice r i).follower
        (ReferenceFollowerFixedReply.actualChoice r i).row
        (ReferenceFollowerFixedReply.actualChoice r i).activation
        (ReferenceFollowerFixedReply.actualChoice r i).time choice = .offer U ∧
      ReferenceActiveAffinePositiveTest.upSent r.input =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hslot : PublicDiscreteDraws.slotDraw (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
    (hdraw : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 r.input.time).1 = i) :
    ReferenceActiveAffinePositiveTest.upSent r.input =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
    ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
      some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) :=
  (hselected hslot hdraw).2.2

private theorem matching_word_at_origin
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (P0 : ReferenceActivePhysicalStep.Payload rate)
    (horigin : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∨
      ∃ pre preSaved, r.input.state.coordinator = .collection P0 pre preSaved)
    (hOrd : r.output.next.coordinator ≠ .dagger)
    (tail : ReferenceCollectionPhaseHistory.Tail r.input)
    (htail : ReferenceCollectionPhaseHistory.executedTail r.input = some tail)
    (i : Fin (p.m - 1))
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hindex : ReferenceActivePhysicalStep.upSenderIndex r.input = i)
    (Lsite : ReferenceActivePhysicalStep.Ledger rate)
    (d : ReferenceActivePhysicalStep.UpDiagnostic p rate)
    (hsite : ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := r.input) = some Lsite)
    (hup : r.output.coordinator.up = some d)
    (hinput : d.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput r.input Lsite)
    (hraw : d.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (hexpected : d.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))
    (haccept : CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true) :
    ReferenceCollectionPhaseHistory.filteredParsed r.input Lsite = some U ∧
    d.parsed = some U ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
    ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
      (bank : CoordinatorUpReception.UpDecoderBank p),
      (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) Lsite).result =
        .success (decoded, bank) ∧
      ReferenceCollectionPhaseHistory.AcceptedUp r.input i U ∧
      ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i := by
  have haccepted :
      ReferenceCollectionPhaseHistory.filteredParsed r.input Lsite = some U ∧
      d.parsed = some U ∧ d.locallyAccepted = true ∧ d.rawMatches = true ∧
      ∃ decoded bank,
        (ReferenceActivePhysicalStep.receiveUp (ReferenceActivePhysicalStep.prepare r.input) Lsite).result =
          .success (decoded, bank) ∧ ReferenceCollectionPhaseHistory.AcceptedUp r.input i U := by
    rcases horigin with hcut | ⟨pre, preSaved, hstate⟩
    · obtain ⟨_cutTail, _cutRecorder, decoded, bank, _ht, _hr, _hs,
        hfiltered, hparsed, hlocal, hmatches, hsuccess, hevent⟩ :=
        cutoff_matching_word r hcut hOrd i U hindex Lsite d hsite hup hinput hraw hexpected haccept
      exact ⟨hfiltered, hparsed, hlocal, hmatches, decoded, bank, hsuccess, hevent⟩
    · obtain ⟨_recording, ledger, diagnostic, _hrecording, _hstart, hsite', _hcheck,
        hup', _hinput, _htailReception, _hnotInvalid, _hcases, _hdecoder, _hraw,
        _hparsed, _hlocal, _hexpected, _hmatches, _hbank, _htime, _hsample,
        _hobservation, _hwrong, hmatching⟩ :=
        ReferenceCollectionUpReceiverLocal.actual_collection_up_receiver_matching_word
          r P0 pre preSaved tail hstate htail hOrd
      have hledger : ledger = Lsite := Option.some.inj (hsite'.symm.trans hsite)
      subst ledger
      have hdiagnostic : diagnostic = d := Option.some.inj (hup'.symm.trans hup)
      subst diagnostic
      have hmatched := hmatching U hraw hexpected (by rw [hindex]; exact haccept)
      rw [hindex] at hmatched
      obtain ⟨hfiltered, hparsed, hlocal, hmatches, _hwrong, decoded, bank, hsuccess, hevent⟩ := hmatched
      exact ⟨hfiltered, hparsed, hlocal, hmatches, decoded, bank, hsuccess, hevent⟩
  obtain ⟨hfiltered, hparsed, hlocal, hmatches, decoded, bank, hsuccess, hevent⟩ := haccepted
  have hlabel : ReferenceCollectionPhaseHistory.acceptedLabel r.input = some i := by
    rcases hevent with ⟨eventTail, eventRecorder, eventL, eventDecoded, eventBank,
      heventTail, heventRecorder, heventStart, heventSuccess, _heventParsed, heventIndex⟩
    simp only [ReferenceCollectionPhaseHistory.acceptedLabel, heventTail, Option.bind_some,
      ReferenceCollectionPhaseHistory.Tail.reception, heventRecorder, heventStart, heventSuccess]
    exact congrArg some heventIndex.symm
  exact ⟨hfiltered, hparsed, hlocal, hmatches, decoded, bank, hsuccess, hevent, hlabel⟩

private theorem cutoff_ordinary_from_endpoint
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start a n : ℕ) (hspan : start + (a + n) ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant initial)
    (hOrd : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n)
      hspan active).finalState.coordinator ≠ .dagger)
    (B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (rest : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hBsplit : B = cut :: rest) (hn : n ≤ B.length) (hnPos : 0 < n)
    (hintervalEq : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n)
      hspan active).records.drop a = B.take n)
    (i : Fin (p.m - 1)) (endpoint : ReferencePrelaunchFollower.State p rate.eta)
    (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hEndpoint : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n)
      hspan active).finalState.followers i = .ordinary endpoint endpointMemory) :
    cut.output.next.coordinator ≠ .dagger ∧ cut.output.next.followers i ≠ .dagger := by
  have hcutMem : cut ∈ (ReferenceActivePhysicalHorizon.run initial rows selected rewards start (a + n)
      hspan active).records.drop a := by
    rw [hintervalEq, hBsplit]
    cases n with
    | zero => omega
    | succ n => simp only [List.take_succ_cons, List.mem_cons, true_or]
  have hcut := ReferenceCoordinatorUpIntervalWindow.run_interval_cut initial rows selected rewards start a (a + n)
    (Nat.le_add_right a n) hspan active hinitial hOrd
  refine ⟨hcut.2.2.2.2.2.2 cut (List.mem_of_mem_drop hcutMem), ?_⟩
  intro hd
  obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hcutMem
  obtain ⟨next, nextMemory, hf, _⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hcut.2.2.1 i endpoint endpointMemory hEndpoint q hq
  rw [hget, hd] at hf
  cases hf

private theorem follower_fields_of_equal_run
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start left right : ℕ) (hl : start + left ≤ p.T) (hr : start + right ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start) (heq : left = right)
    (i : Fin (p.m - 1)) (before : ReferencePrelaunchFollower.State p rate.eta)
    (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate))
    (hleft : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left hl active).finalState.followers i =
        .dagger ∨
      ∃ state memory,
        (ReferenceActivePhysicalHorizon.run initial rows selected rewards start left hl active).finalState.followers i =
          .ordinary state memory ∧ state.status = .unoccupied ∧
        ReferenceFollowerReplyChronology.reply state = ReferenceFollowerReplyChronology.reply before ∧
        state.lastDown = some M)
    (endpoint : ReferencePrelaunchFollower.State p rate.eta)
    (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hEndpoint : (ReferenceActivePhysicalHorizon.run initial rows selected rewards start right hr active).finalState.followers i =
      .ordinary endpoint endpointMemory) :
    endpoint.status = .unoccupied ∧
    ReferenceFollowerReplyChronology.reply endpoint = ReferenceFollowerReplyChronology.reply before := by
  rw [run_count_eq initial rows selected rewards start left right hl hr active heq] at hleft
  rcases hleft with hd | ⟨state, memory, hf, hs, hreply, _⟩
  · rw [hEndpoint] at hd
    cases hd
  · have hstate : state = endpoint :=
      (DeclaredFollowerLocalRound.LocalConfiguration.ordinary.inj (hf.symm.trans hEndpoint)).1
    subst state
    exact ⟨hs, hreply⟩

private theorem ordinary_sender_family
    {initial final : ReferenceActivePhysicalStep.State p rate}
    (records B : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (n : ℕ) (hn : n ≤ B.length) (hrecords : records = B.take n)
    (hchain : ReferenceActivePhysicalHorizon.Connected initial records final)
    (i : Fin (p.m - 1)) (before endpoint : ReferencePrelaunchFollower.State p rate.eta)
    (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
    (hEndpoint : final.followers i = .ordinary endpoint endpointMemory)
    (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta))
    (hchoices : ∀ k : Fin B.length, let r := B[k.val]
      ((ReferenceFollowerFixedReply.actualChoice r i).configuration = .dagger ∨
        ∃ choice choiceMemory,
          (ReferenceFollowerFixedReply.actualChoice r i).configuration = .ordinary choice choiceMemory ∧
          choice.status = .unoccupied ∧
          ReferenceFollowerReplyChronology.reply choice =
            ReferenceFollowerReplyChronology.reply before ∧
          (∀ offered : OrdinaryMessageCodec.UpRecord
              (ReferencePrelaunchFollower.codecParams p rate.eta),
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta
              (ReferenceFollowerFixedReply.actualChoice r i).follower (ReferenceFollowerFixedReply.actualChoice r i).row
              (ReferenceFollowerFixedReply.actualChoice r i).activation (ReferenceFollowerFixedReply.actualChoice r i).time choice = .offer offered →
            offered = U ∧ ReferenceUpReception.currentOfferWord rate r.input.row i r.input.time
              (ReferenceFollowerFixedReply.actualChoice r i) (ReferenceFollowerFixedReply.actualChoice_alignment r i).1
              (ReferenceFollowerFixedReply.actualChoice_alignment r i).2.1 (ReferenceFollowerFixedReply.actualChoice_alignment r i).2.2 =
                some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
          ∀ (_hslot : PublicDiscreteDraws.slotDraw
              (r.input.row.2 r.input.time).1 = PublicDiscreteDraws.upSlot)
            (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (r.input.row.2 r.input.time).1 = i),
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i r.input.row
              (r.input.state.activations i) r.input.time choice = .offer U ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta
              (ReferenceFollowerFixedReply.actualChoice r i).follower (ReferenceFollowerFixedReply.actualChoice r i).row
              (ReferenceFollowerFixedReply.actualChoice r i).activation (ReferenceFollowerFixedReply.actualChoice r i).time choice = .offer U ∧
            ReferenceActiveAffinePositiveTest.upSent r.input =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare r.input) =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U))) :
    ∀ k : Fin B.length, k.val < n →
      PublicDiscreteDraws.slotDraw (B[k.val].input.row.2 B[k.val].input.time).1 = PublicDiscreteDraws.upSlot →
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
        (B[k.val].input.row.2 B[k.val].input.time).1 = i →
      ReferenceActiveAffinePositiveTest.upSent B[k.val].input =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare B[k.val].input) =
        some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) := by
  intro k hkN hslot hdraw
  have hmem : B[k.val] ∈ records := by
    rw [hrecords]
    have htake : k.val < (B.take n).length := by rw [List.length_take, Nat.min_eq_left hn]; exact hkN
    have hget : (B.take n)[k.val]'htake = B[k.val] := List.getElem_take
    rw [← hget]
    exact List.getElem_mem htake
  obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hmem
  obtain ⟨next, nextMemory, hnext, _⟩ :=
    ReferenceFollowerReplyChronology.connected_output_chronology hchain i endpoint endpointMemory hEndpoint q hq
  rw [hget] at hnext
  obtain ⟨choice, memory, hc, _hs, _hf, _hd⟩ :=
    ReferenceFollowerReplyChronology.record_choice_chronology B[k.val] i next nextMemory hnext
  rcases hchoices k with hd | ⟨choiceB, memoryB, _hcB, _hsB, _hrB, _hoffer, hselected⟩
  · have hfalse := hd.symm.trans hc
    cases hfalse
  · exact selected_sender_pair B[k.val] i choiceB U hselected hslot hdraw

/-- The actual early retained DOWN produces one fixed UP reply before prefix
queries. A cutoff-inclusive original prefix with the exact local positive
count supplies the saved second window. Its full-window uniqueness implies
actual checked acceptance at the saved record. No delivery is asserted. -/
theorem actual_first_collection_early_up_window_acceptance :
    ∀
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count),
    let x0 := ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate
    let b0 := ReferenceInitializationRun.output x0
    let s := ReferenceInitializationRun.elapsed p b0.completed
    let I := ReferenceFirstCollectionEpochAlignment.actualLaunchState
      rate source rewards C_star C_h hcross
    let Erun := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let W := ReferenceFirstLiveConfirmationHistory.firstLiveWindow Erun.records
    let w := W.length
    let B := ReferenceCollectionPhaseHistory.collectionWindow Erun.records w
    let u := s + w + 1
    let rows := source.1.2
    let J := ActualInitializationPhysicalStep.selectedRowIndex p source
    let active := (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ)
      (P0 : ReferenceActivePhysicalStep.Payload rate)
      (birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)),
      Erun.records = W ++ cut :: suffix ∧
      ReferenceActivePhysicalHorizon.Connected I W cut.input.state ∧
      (∃ hindex : w < Erun.records.length, cut = Erun.records[w]'hindex) ∧
      cut.input.time.val = s + w ∧
      cut.input.state.coordinator = .live registers owned base ∧
      ReferenceCollectionPhaseHistory.cutoffChosen cut.input = true ∧
      P0 = registers.payload ∧ P0.sigma.val = s ∧
      (∀ arm, P0.queues arm = 0) ∧
      FollowerCutoffScan.firstCutoff p rate.eta.val P0.sigma
        (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
          (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) = u ∧
      birth ∈ Erun.records ∧
      ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0 ∧
      birth.input.time.val = s ∧
      (∃ installed birthSelection,
        birth.output.preparation.coordinator = .first (.chosen installed birthSelection) ∧
          installed.registers.payload = P0) ∧
      Erun.records.length = count ∧
      B = cut :: (Erun.records.drop (w + 1)).takeWhile
        (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
      (∀ k : Fin B.length,
        Erun.records[w + k.val]? = some B[k.val] ∧
          B[k.val].input.time.val + 1 = u + k.val) ∧
      (cut.output.next.coordinator = .dagger ∨
        ∃ nextLedger saved, cut.output.next.coordinator = .collection P0 nextLedger saved) ∧
      ∀ (i : Fin (p.m - 1)) (j : Fin Erun.records.length)
        (M : ReferenceAcceptedUpFollowerHistory.DownRecord (p := p) (rate := rate)),
        j.val < w → ReferenceAcceptedUpFollowerHistory.RetainedDown Erun.records[j.val] i M →
        ∃ (before : ReferencePrelaunchFollower.State p rate.eta)
          (memory : ActiveFollowerLifecycle.LocalMemory p)
          (token : ActiveFollowerLifecycle.ProposalRead p)
          (U : OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)),
          cut.input.state.followers i = .ordinary before memory ∧
          before.lastDown = some M ∧ M = P0.downRecord i ∧
          before.status ≠ .unoccupied ∧
          ReferencePrelaunchFollower.acceptedStart before = s + 1 ∧
          M.val.sigma = s + 1 ∧
          ActiveFollowerLifecycle.localStateDomainValid before ∧
          memory.lastProposalRead = some token ∧
          token.timestamp.val + 1 = cut.input.time.val ∧
          token.bit = FollowerCutoffScan.completeRowProposalBit p rate.eta.val
            (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)) token.timestamp ∧
          ActiveFollowerLifecycle.startRound rate.eta cut.input.time before memory =
            .ok ({before with status := .unoccupied}, memory) ∧
          ((ReferenceFollowerFixedReply.actualChoice cut i).configuration = .dagger ∨
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ∀ arrival,
              ActiveFollowerQueueOperation.serviceOutput rate.n
                {before with status := .unoccupied} arrival =
                  {before with status := .unoccupied}) ∧
          U.val = OrdinaryMessageCodec.UpFields.mk (s + 1) before.S before.delta before.backlog ∧
          0 < U.val.sigma ∧
          (∀ (_hslot : PublicDiscreteDraws.slotDraw
              (cut.input.row.2 cut.input.time).1 = PublicDiscreteDraws.upSlot)
            (_hselected : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              (cut.input.row.2 cut.input.time).1 = i),
            (ReferenceFollowerFixedReply.actualChoice cut i).configuration =
              .ordinary {before with status := .unoccupied} memory ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta i cut.input.row
              (cut.input.state.activations i) cut.input.time
                {before with status := .unoccupied} = .offer U ∧
            ActiveFollowerQueueOperation.checkedUpOffer rate.eta
              (ReferenceFollowerFixedReply.actualChoice cut i).follower (ReferenceFollowerFixedReply.actualChoice cut i).row
              (ReferenceFollowerFixedReply.actualChoice cut i).activation (ReferenceFollowerFixedReply.actualChoice cut i).time
                {before with status := .unoccupied} = .offer U ∧
            ReferenceActiveAffinePositiveTest.upSent cut.input =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
            ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare cut.input) =
              some (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
          (cut.output.next.followers i = .dagger ∨
            ∃ out outMemory,
              cut.output.next.followers i = .ordinary out outMemory ∧
              out.status = .unoccupied ∧
              ReferenceFollowerReplyChronology.reply out =
                ReferenceFollowerReplyChronology.reply before ∧
              out.lastDown = some M ∧
              ReferencePrelaunchFollower.acceptedStart out = P0.sigma.val + 1) ∧
          (∀ sigma, ¬ ReferenceFollowerReplyChronology.appliedDown cut i sigma) ∧
          ∀ (n : ℕ) (hn : n ≤ B.length),
            ∃ hspanN : s + (w + n) ≤ p.T,
            let Cn := ReferenceActivePhysicalHorizon.run I rows J rewards s (w + n) hspanN active
            Cn.finalState.coordinator = .dagger ∨
            Cn.finalState.followers i = .dagger ∨
            (let preRun := ReferenceActivePhysicalHorizon.run I rows J rewards s w
               ((Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN) active
             let interval := Cn.records.drop w
             let trace := ReferenceCoordinatorUpIntervalWindow.actualUpCallTrace interval i
             let rounds := ReferenceCoordinatorUpIntervalWindow.intervalRounds
               I rows J rewards s w (w + n) hspanN active
             let positive := AffineBatchDecoder.positives p trace rounds
             let channel := preRun.finalState.upDecoderBank i
             let window := positive.drop (AffineBatchDecoder.quota p - channel.pending.length)
             positive.length = AffineBatchDecoder.quota p - channel.pending.length +
               AffineBatchDecoder.quota p →
             ∃ (endpoint : ReferencePrelaunchFollower.State p rate.eta)
               (endpointMemory : ActiveFollowerLifecycle.LocalMemory p)
               (moving : ReferenceActivePhysicalStep.Ledger rate)
               (movingSaved : Option (Fin p.T × Bool)),
               Cn.finalState.followers i = .ordinary endpoint endpointMemory ∧
               endpoint.status = .unoccupied ∧
               ReferenceFollowerReplyChronology.reply endpoint =
                 ReferenceFollowerReplyChronology.reply before ∧
               Cn.finalState.coordinator = .collection P0 moving movingSaved ∧
               moving.sigma = s + 1 ∧
               moving.pending = Finset.univ \
                 (ReferenceCollectionPhaseHistory.acceptedLabels (B.take n)).toFinset ∧
               interval = B.take n ∧
               ∃ (first : List (AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p)))
                 (last : AffineBatchDecoder.Entry p.T (AffineBatchDecoder.width p))
                 (index : Fin rounds.length)
                 (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                 (diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate),
                 let decoderBefore := AffineBatchDecoder.run p trace (rounds.take index.val) channel
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
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input ledger) ∧
                 ReferenceActivePhysicalHorizon.Connected preRun.finalState
                   (interval.take index.val) record.input.state ∧
                 record.input.state.upDecoderBank =
                   ReferenceCoordinatorUpDecoderReplay.replay preRun.finalState.upDecoderBank
                     (ReferenceCoordinatorUpDecoderReplay.retainedUpDiagnostics (interval.take index.val)) ∧
                 diagnostic.input.upDecoderBank = record.input.state.upDecoderBank ∧
                 decoderBefore = diagnostic.input.upDecoderBank i ∧
                 decoderBefore.pending ++ [AffineBatchDecoder.entry p trace last.time] = window ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.pending = [] ∧
                 (CoordinatorUpReception.decoderTransition diagnostic.input).1.completed =
                   channel.completed ++ [first, window] ∧
                 diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition diagnostic.input).1 ∧
                 diagnostic.raw = (CoordinatorUpReception.decoderTransition diagnostic.input).2 ∧
                 diagnostic.raw = AffineBatchDecoder.batchOutput window ∧
                 CoordinatorUpReception.decoderTransition diagnostic.input =
                   (⟨[], channel.completed ++ [first, window]⟩, AffineBatchDecoder.batchOutput window) ∧
                 AffineBatchDecoder.run p trace rounds channel = ⟨[], channel.completed ++ [first, window]⟩ ∧
                 AffineBatchDecoder.run p trace rounds channel = Cn.finalState.upDecoderBank i ∧
                 (∀ entry, entry ∈ window →
                   AffineBatchDecoder.equation entry.sample
                     (ActiveFollowerArmChoice.offeredUpWord rate.eta U)) ∧
                 AffineBatchDecoder.satisfies (AffineBatchDecoder.samples window)
                   (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                 ∃ (k : Fin B.length) (Lsite : ReferenceActivePhysicalStep.Ledger rate)
                   (received : ReferenceActivePhysicalStep.Ledger rate)
                   (receivedBank : CoordinatorUpReception.UpDecoderBank p),
                   record = B[k.val] ∧
                   Erun.records[w + k.val]? = some record ∧
                   ReferenceCoordinatorUpPhysicalCall.siteLedger? (x := record.input) = some Lsite ∧
                   diagnostic.input = ReferenceCoordinatorUpPhysicalCall.actualUpInput record.input Lsite ∧
                   Lsite.pending = Finset.univ \
                     (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset ∧
                   ((ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .success (received, receivedBank) ∨
                     (ReferenceActivePhysicalStep.receiveUp
                       (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                         .rejected (received, receivedBank)) ∧
                   ((∃! word, AffineBatchDecoder.satisfies
                       (AffineBatchDecoder.samples window) word) →
                     diagnostic.raw = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     diagnostic.expected = some (ActiveFollowerArmChoice.offeredUpWord rate.eta U) ∧
                     CoordinatorCollectionLedger.acceptUpCheck Lsite i U = true ∧
                     OrdinaryMessageCodec.acceptUp
                       (CoordinatorCollectionLedger.codecParams p rate.eta.val)
                       Lsite.cutoff Lsite.cursor i.val
                       (CoordinatorCollectionLedger.pendingNaturalLabels Lsite) Lsite.sigma U ∧
                     ReferenceCollectionPhaseHistory.filteredParsed record.input Lsite = some U ∧
                     diagnostic.parsed = some U ∧ diagnostic.locallyAccepted = true ∧
                     diagnostic.rawMatches = true ∧
                     ∃ (decoded : ReferenceActivePhysicalStep.Ledger rate)
                       (bank : CoordinatorUpReception.UpDecoderBank p),
                       (ReferenceActivePhysicalStep.receiveUp
                         (ReferenceActivePhysicalStep.prepare record.input) Lsite).result =
                           .success (decoded, bank) ∧
                       ReferenceCollectionPhaseHistory.AcceptedUp record.input i U ∧
                       ReferenceCollectionPhaseHistory.acceptedLabel record.input = some i)) := by
  classical
  intro rate source rewards C_star C_h count hcross hspan hshort x0 b0 s I Erun W w B u rows J active
  have hE := ReferenceFirstCollectionEarlyUpSenderReceiver.actual_first_collection_early_up_sender_receiver
    rate source rewards C_star C_h count hcross hspan hshort
  rcases hE with ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hrecordsSender, hb, hBsplitSender, hwindowEnd, hWearlyBound,
    hphysicalEnd, hterminal, hEarly, hwindow, hdispatch, hcoordNext, hqueries⟩
  have hBsplit : B = cut :: (Erun.records.drop (w + 1)).takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    exact hBsplitSender
  have hrecords : Erun.records.length = count := by
    exact hrecordsSender
  have hBend : w + B.length ≤ count := hwindowEnd.le.trans hWearlyBound
  have hEspan : s + count ≤ p.T := by
    dsimp only [s, b0, x0]
    exact hspan
  have hlaunch := ReferenceFirstCollectionLateUpSecondWindow.actual_launch_up_bank_seed
    rate source rewards C_star C_h count hcross hspan
  have hinitial : ReferenceUpDecoderBankInvariant.upBankInvariant I := hlaunch.1
  refine ⟨cut, suffix, registers, owned, base, P0, birth,
    hsplit, hconnected, hcutIndex, hcutTime, hcutState, hcutoff, hpayload,
    hsigma, hqueues, hfirstCutoff, hbirthMem, hbirthInstall, hbirthTime,
    hbirthFirst, hrecords, hBsplit, hwindow, hcoordNext, ?_⟩
  intro i j M hj hretained
  rcases hqueries i j M hj hretained with
    ⟨before, memory, token, U, hbefore, hlast, hMpayload, hoccupied, hstart,
      hMstart, hdomain, htoken, htokenTime, htokenBit, hstartRound, hcutChoice,
      hUfields, hUpositive, hcutSender, hcutFollower, hcutNoDown, hcutCollection⟩
  refine ⟨before, memory, token, U, hbefore, hlast, hMpayload, hoccupied,
    hstart, hMstart, hdomain, htoken, htokenTime, htokenBit, hstartRound,
    hcutChoice, hUfields, hUpositive, hcutSender, hcutFollower, hcutNoDown, ?_⟩
  intro n hn
  have hbound : w + n ≤ count := by
    exact (Nat.add_le_add_left hn w).trans hBend
  have hspanN : s + (w + n) ≤ p.T := (Nat.add_le_add_left hbound s).trans hEspan
  refine ⟨hspanN, ?_⟩
  intro Cn
  by_cases hOrd : Cn.finalState.coordinator = .dagger
  · exact Or.inl hOrd
  refine Or.inr ?_
  have hspanW : s + w ≤ p.T :=
    (Nat.add_le_add_left (Nat.le_add_right w n) s).trans hspanN
  by_cases hFollowerDagger : Cn.finalState.followers i = .dagger
  · exact Or.inl hFollowerDagger
  refine Or.inr ?_
  intro preRun interval trace rounds positive channel window hCount
  obtain ⟨endpoint, endpointMemory, hEndpoint⟩ :
      ∃ endpoint endpointMemory, Cn.finalState.followers i = .ordinary endpoint endpointMemory := by
    cases hf : Cn.finalState.followers i with
    | dagger => exact (hFollowerDagger hf).elim
    | ordinary endpoint endpointMemory => exact ⟨endpoint, endpointMemory, rfl⟩
  have hintervalEq : interval = B.take n :=
    interval_eq_collection_take I rows J rewards s count hspan active W cut suffix B
      hsplit hBsplit n hn hbound
  have hintervalLen : interval.length = n := by
    rw [hintervalEq, List.length_take, Nat.min_eq_left hn]
  have hnPos : 0 < n := by
    have hroundsPos := positive_count_rounds_nonempty trace rounds channel hCount
    change 0 < (interval.map fun r => r.input.time).length at hroundsPos
    rw [List.length_map, hintervalLen] at hroundsPos
    exact hroundsPos
  obtain ⟨hcutNextOrdinary, hcutFollowerNotDagger⟩ :=
    cutoff_ordinary_from_endpoint I rows J rewards s w n hspanN active hinitial hOrd B cut _
      hBsplit hn hnPos hintervalEq i endpoint endpointMemory hEndpoint
  rcases hcutCollection.resolve_left hcutNextOrdinary with
    ⟨nextLedger, nextSaved, hcutCollection, hcutFollowers⟩
  rcases hcutFollowers.resolve_left hcutFollowerNotDagger with
    ⟨out, outMemory, hout, houtStatus, houtReply, hlastOut, hstartOut, hrest⟩
  rcases hrest with ⟨hprefixStart, _hnextSigma, _hnextPending, hmovement, hBqueries⟩
  obtain ⟨hprefixSeed, _hnoDown, _htimeChoice, _hboundary⟩ := hprefixStart
  obtain ⟨_hfinalSeed, _hcoordSeed, _hfollowerSeed, _hseedStart, hprefixFacts⟩ := hprefixSeed
  have hnEarly : n - 1 ≤ ((Erun.records.drop (w + 1)).takeWhile
      (fun r => !ReferenceCollectionPhaseHistory.laterChosen r.input)).length := by
    rw [hBsplit, List.length_cons] at hn
    omega
  have hendpointFacts := follower_fields_of_equal_run I rows J rewards s (w + 1 + (n - 1)) (w + n)
    (by omega) hspanN active (by omega) i before M (hprefixFacts (n - 1) hnEarly).2
    endpoint endpointMemory hEndpoint
  have hcutInterval := ReferenceCoordinatorUpIntervalWindow.run_interval_cut I rows J rewards s w (w + n)
    (Nat.le_add_right w n) hspanN active hinitial hOrd
  have hsenders := ordinary_sender_family interval B n hn hintervalEq hcutInterval.2.2.1 i before
    endpoint endpointMemory hEndpoint U (fun k => (hBqueries k).1)
  obtain ⟨moving, movingSaved, hmoving, hmovingSigma, hmovingPending⟩ :=
    (hmovement n hn hnPos).resolve_left hOrd
  refine ⟨endpoint, endpointMemory, moving, movingSaved, hEndpoint,
    hendpointFacts.1, hendpointFacts.2, hmoving, hmovingSigma, hmovingPending,
    hintervalEq, ?_⟩
  have hseed : AffineBatchDecoder.collected (I.upDecoderBank i) = [] := hlaunch.2.1 i
  refine saved_window_of_senders I rows J rewards s w n hspanW hspanN active hinitial hOrd B hn
    hintervalEq Erun.records (fun k => (hwindow k).1) i U hseed hsenders ?_ hCount
  intro k r hintervalOrd diagnostic hdiagnostic heligible hslot hdraw
  have hselectedSenderIndex : ReferenceActivePhysicalStep.upSenderIndex r.input = i := by
    rw [ReferenceActiveAffinePositiveTest.upSenderIndex_eq_draw, hdraw]
  have hgate : CoordinatorUpReception.receptionGate diagnostic.input :=
    (CoordinatorUpReception.roundInput_selected_iff_gate diagnostic.input).mp heligible.1
  obtain ⟨tail, recording, Lsite, receiverDiagnostic, receivedLedger, bank, finished, clockFinished,
    htail, _htailPending, _htailSigma, hsite, _hrecording, _hstart, _hcheck, hinput, hup,
    _htailReception, _hnotInvalid, hreceiveAlternatives, _hfinish, _hclock, _hdecoder, _hraw,
    _hparsed, _hlocal, hexpectedReceiver, _hrawMatches, _hbank, _htime, _hsample,
    _hobservation, _hwrong, hLpending, _hLsigma, _hcursorLower, _hcursor, _hcutFields, hlocalQueries⟩ :=
      (hBqueries k).2.1 hintervalOrd
  have hdiag : receiverDiagnostic = diagnostic := Option.some.inj (hup.symm.trans hdiagnostic)
  subst receiverDiagnostic
  have hnotAccepted : i ∉ (ReferenceCollectionPhaseHistory.acceptedLabels (B.take k.val)).toFinset := by
    intro haccepted
    exact ((hlocalQueries hslot hdraw).2 haccepted).2.1 hgate
  have haccept := ((hlocalQueries hslot hdraw).1 hnotAccepted).2.2.2.2.1
  have horigin : ReferenceCollectionPhaseHistory.cutoffChosen r.input = true ∨
      ∃ pre preSaved, r.input.state.coordinator = .collection P0 pre preSaved := by
    by_cases hkzero : k.val = 0
    · left
      have hr : r = cut := by simp only [r, hkzero, hBsplit, List.getElem_cons_zero]
      rw [hr]
      exact hcutoff
    · right
      have hmove := hmovement k.val (Nat.le_of_lt k.isLt) (Nat.one_le_iff_ne_zero.mpr hkzero)
      have hlookup := hwindow k
      obtain ⟨hlookupIndex, hlookupGet⟩ := List.getElem?_eq_some_iff.mp hlookup.1
      change w + k.val < Erun.records.length at hlookupIndex
      have hglobalIndex : w + k.val < count := by rw [hrecords] at hlookupIndex; exact hlookupIndex
      have hboundary := run_prefix_endpoints I rows J rewards s count hspan active (w + k.val) hglobalIndex
      have hrecordIdentity :
          (ReferenceActivePhysicalHorizon.run I rows J rewards s count hspan active).records[
            w + k.val]'(by rw [ReferenceActivePhysicalHorizon.run_record_count]; exact hglobalIndex) = r :=
        hlookupGet
      have hboundaryRecord := hboundary.1.trans
        (congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
          record.input.state) hrecordIdentity)
      rcases hmove with hdagger | ⟨pre, preSaved, hstate, _hsigma, _hpending⟩
      · have hinputDagger : r.input.state.coordinator = .dagger := by
          rw [← hboundaryRecord]
          exact hdagger
        have hnextDagger : r.output.next.coordinator = .dagger := by
          rw [r.output_eq]
          exact (ReferenceActivePhysicalStep.step_coordinator_dagger r.input hinputDagger).1
        exact False.elim (hintervalOrd hnextDagger)
      · exact ⟨pre, preSaved, by rw [← hboundaryRecord]; exact hstate⟩
  refine ⟨Lsite, receivedLedger, bank, hsite, hinput, hLpending, hreceiveAlternatives,
    hexpectedReceiver, haccept, ?_⟩
  intro hraw hexpected
  exact matching_word_at_origin r P0 horigin hintervalOrd tail htail i U hselectedSenderIndex
    Lsite diagnostic hsite hup hinput hraw hexpected haccept

end Bandits.Support.ReferenceFirstCollectionEarlyUpWindowAcceptance

end
