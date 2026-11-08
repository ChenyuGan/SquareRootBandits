/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCutoffSurvival

import Lean.Elab.Tactic.Omega

/-!
# The generated first-cutoff coordinator endpoint

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/06_interruptions.tex:9-14,41-70,246-297`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This internal join follows the original launch run through its first cutoff.
The actual rejected UP reception advances its decoder bank, and the successful
ledger and clock finishes commit that returned bank. The same retained round
extracts to one checked, rejected collection round. No continuing collection
invariant, source queue identity, or manuscript closure is asserted here.

The named consumers are first-collection follower phase initialization and the
continuing collection ready-domain initializer. Continuing start, accepted-UP
pre-receiver replay, queue/score correctness, and source exceptional-event laws
remain separate producers.
-/

@[expose] public section

noncomputable section

open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceFirstLiveConfirmationHistory
open Bandits.Support.ReferenceGeneratedFirstCutoffSurvival

open scoped Classical

namespace Bandits.Support.ReferenceGeneratedFirstCutoffCoordinatorEndpoint

variable {p : ConstructorDimensions.Parameters}

private theorem round_input_ext {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : RoundInput p rate}
    (hstate : left.state = right.state) (hrows : left.rows = right.rows)
    (hselected : left.selected = right.selected) (htime : left.time = right.time)
    (hrewards : left.rewards = right.rewards) : left = right := by
  cases left
  cases right
  cases hstate
  cases hrows
  cases hselected
  cases htime
  cases hrewards
  rfl

private theorem run_records_of_state_eq {rate : ReferenceActivePhysicalStep.RateInput p}
    {left right : ReferenceActivePhysicalStep.State p rate}
    (hstate : left = right) (rows : CompletePublicTable.CompleteRows p)
    (J : Fin (M p)) (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (s count : ℕ) (hspan : s + count ≤ p.T)
    (leftActive : allActiveAtStart left s) (rightActive : allActiveAtStart right s) :
    (ReferenceActivePhysicalHorizon.run left rows J rewards s count hspan leftActive).records =
      (ReferenceActivePhysicalHorizon.run right rows J rewards s count hspan rightActive).records := by
  cases hstate
  rfl

/-- On the actual generated launch branch, a first cutoff has a successful
coordinator endpoint, an advanced rejected-reception bank, and an extracted
checked round. All operational witnesses are outputs of the original run.
The successor is the original prefix of length `window.length + 1`, including
when that prefix reaches the physical horizon. -/
theorem actual_first_cutoff_coordinator_endpoint
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (z : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput z rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (firstLiveWindow
      (generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
    let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
    let window := firstLiveWindow execution.records
    let k := window.length
    let hprefixSpan : s + k ≤ p.T := by
      have hk : k < count := by simpa [window, execution] using hshort
      exact le_trans (Nat.add_le_add_left (Nat.le_of_lt hk) s) hspan
    let hsuccessorSpan : s + (k + 1) ≤ p.T := by
      have hk : k < count := by simpa [window, execution] using hshort
      omega
    let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan
      (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
    let successorRun := ReferenceActivePhysicalHorizon.run initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1) hsuccessorSpan
      (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
    s < p.T ∧
    ∃ cut suffix,
      execution.records = window ++ cut :: suffix ∧
      cut = execution.records[k]'(by
        have hlen : execution.records.length = count :=
          ReferenceActivePhysicalHorizon.run_record_count initial z.1.2
            (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
            (generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed)
        have hk : k < count := by simpa [window, execution] using hshort
        omega) ∧
      cut.input.time.val = s + k ∧
      cut.input.state = prefixRun.finalState ∧
      cut.input.rows = z.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      cut.input.rewards = rewards ∧
      ∃ r q base,
        cut.input.state.coordinator = .live r q base ∧
        r.payload.sigma.val = s ∧
        ∃ dispatched hstart ledger hinit hledger hdomain hclock hpending hnoAssignment selected,
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          let u := s + k + 1
          u = cut.input.time.val + 1 ∧
          u ≤ p.T ∧
          u ≤ r.gridBoundary ∧
          ledger.sigma = r.payload.sigma.val + 1 ∧
          ledger.cutoff = u ∧
          ∃ recording,
            ReferenceCoordinatorRecorderCallTrace.actualBranchInput cut =
              some (CoordinatorRecorderComplementBridge.recorderInput
                (collectionRecordingInput cut.output.preparation r.payload
                  dispatched.startResult (liveRegistersAt r cut.input.time).complementWeights)) ∧
            ReferenceCoordinatorRecorderCallTrace.recording
              (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some recording ∧
            cut.coordinatorDiagnostics.recording = some recording ∧
            CoordinatorRecordingOperation.run
              (CoordinatorRecorderComplementBridge.recorderInput
                (collectionRecordingInput cut.output.preparation r.payload
                  dispatched.startResult (liveRegistersAt r cut.input.time).complementWeights)) =
              some recording ∧
            ∃ ledgerStarted,
              CoordinatorCollectionLedger.startRound (sharedLedger ledger) (cut.input.time.val + 1)
                (collectionEnabled (sharedLedger ledger) cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                  .success ledgerStarted ∧
              ledgerStarted = CoordinatorCollectionLedger.startRoundCandidate (sharedLedger ledger)
                cut.input.time (collectionEnabled (sharedLedger ledger) cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) ∧
              ∃ input decoded bank diagnostic finished,
                input = ReferenceUpReception.receptionInputAtRow rate cut.input.row
                  (upInputs cut.output.preparation ledgerStarted) cut.input.time ∧
                CoordinatorUpReception.receptionInputDomain input ∧
                CoordinatorUpReception.receptionInputCheck input = true ∧
                CoordinatorUpReception.decoderTransition input =
                  (⟨if CoordinatorUpReception.receptionGate input ∧
                      0 < input.ownObservation.val then
                        [AffineBatchDecoder.entry p (CoordinatorUpReception.traceAt input) input.time]
                      else [], []⟩, none) ∧
                AffineBatchDecoder.quota p > 1 ∧
                decoded = { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
                (receiveUp cut.output.preparation ledgerStarted).result = .rejected (decoded, bank) ∧
                bank = CoordinatorUpReception.decoderBankAfter input ∧
                bank = Function.update input.upDecoderBank input.selectedFollower
                  (CoordinatorUpReception.decoderTransition input).1 ∧
                (∀ i, i ≠ input.selectedFollower → bank i = input.upDecoderBank i) ∧
                ReferenceUpReception.rawParsedOutput rate input = none ∧
                (receiveUp cut.output.preparation ledgerStarted).diagnostic = some diagnostic ∧
                diagnostic.input = input ∧
                diagnostic.expected = upExpected cut.output.preparation ∧
                diagnostic.decoderAfter = (CoordinatorUpReception.decoderTransition input).1 ∧
                diagnostic.raw = none ∧ diagnostic.parsed = none ∧
                diagnostic.locallyAccepted = false ∧
                diagnostic.wrongUniqueAccepted = false ∧
                CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                CoordinatorCollectionLedger.validLedgerCheck finished = true ∧
                (∀ pending : Finset (Fin (p.m - 1)),
                  ∃ clockFinished,
                    CoordinatorPhaseClock.finishRound p rate.eta.val cut.input.time
                      dispatched.startResult.clock pending cut.input.row = .ok clockFinished ∧
                    clockFinished.clock = dispatched.startResult.clock ∧
                    clockFinished.pending = pending ∧
                    clockFinished.ledgerCommand =
                      some (.accumulateLocalServiceAt cut.input.time)) ∧
                cut.output.coordinator.configuration =
                  .collection r.payload finished dispatched.startResult.clock.lastProposal ∧
                cut.output.coordinator.failure = none ∧
                cut.output.coordinator.upDecoderBank = bank ∧
                cut.output.coordinator.recording = some recording ∧
                cut.output.coordinator.up = some diagnostic ∧
                cut.output.next.coordinator =
                  .collection r.payload finished dispatched.startResult.clock.lastProposal ∧
                cut.output.next.upDecoderBank = bank ∧
                successorRun.finalState = cut.output.next ∧
                successorRun.finalState.coordinator =
                  .collection r.payload finished dispatched.startResult.clock.lastProposal ∧
                successorRun.finalState.upDecoderBank = bank ∧
                let choice : ReferenceCollectionSegmentExtraction.Choice rate :=
                  ⟨r.payload, sharedLedger ledger, dispatched.startResult,
                    (liveRegistersAt r cut.input.time).complementWeights,
                    some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                      (liveRegistersAt r cut.input.time) (liveOwnedAt r q cut.input.time)
                      base cut.input.time)⟩
                ReferenceCollectionSegmentExtraction.choice cut.input = some choice ∧
                ∃ completed,
                  ReferenceCollectionSegmentExtraction.extractRound cut = some completed ∧
                  completed.context = choice ∧
                  completed.input = ReferenceCollectionSegmentExtraction.inputOf cut.input
                    (sharedLedger ledger) recording ledgerStarted ∧
                  completed.input.round = cut.input.time ∧
                  completed.accepted = false ∧
                  completed.final = finished ∧
                  CollectionCheckedExecution.checkedRounds (sharedLedger ledger) [completed.input] =
                    some ([false], finished) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate z rewards C_star C_h hc
  let active := generatedLaunchActive rate z rewards C_star C_h hc s hsElapsed
  let execution := generatedFirstCutoffRun rate z rewards C_star C_h hc s hsElapsed count hspan
  let window := firstLiveWindow execution.records
  let k := window.length
  have hk : k < count := hshort
  have hsT : s < p.T := by omega
  have hprefixSpan : s + k ≤ p.T := by omega
  have hsuccessorSpan : s + (k + 1) ≤ p.T := by omega
  let prefixRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s k hprefixSpan active
  let successorRun := ReferenceActivePhysicalHorizon.run initial z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s (k + 1) hsuccessorSpan active
  -- The survival producer fixes the retained cut and its original incoming prefix.
  have hC := run_generated_first_cutoff_survival rate z rewards C_star C_h hc s hsElapsed
    count hspan hshort
  dsimp only at hC
  rcases hC with ⟨_, hfirst, _, _, _, _, cut, suffix, hsplit, hindex, htime,
    hstate, hrows, hselected, hrewards, r, q, base, hlive, hsigma, _,
    dispatched, hstart, ledger, hinit, hledger, hdomain, hclock, hpending,
    hnoAssignment, selected, hbranch, _, huT, huGrid, hledgerSigma, hledgerCut, _⟩
  have hR := ReferenceFirstCutoffReceiverDomain.run_generated_first_cutoff_receiver_domain
    rate z rewards C_star C_h hc s hsElapsed hsT count hspan ⟨s, hsT⟩ rfl
  dsimp only at hR
  rcases hR with ⟨_, _, _, _, _, hreceiver⟩
  -- Transport every retained record using the original source's fixed-control fibre.
  have hseed := generatedLaunchSeed_eq_launchState rate z rewards C_star C_h hc s hsElapsed hsT
  have hrecords := run_records_of_state_eq hseed z.1.2
    (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count hspan
    (by rw [hseed]; exact active) active
  rw [hrecords] at hreceiver
  obtain ⟨receiverCut, receiverSuffix, hRsplit, _, rR, qR, baseR, hRlive,
    dispatchedR, hstartR, ledgerR, hinitR, hledgerR, hdomainR, hclockR, hpendingR,
    hnoAssignmentR, selectedR, hRbranch, recording, hactualInput, htrace, hdiagnostic,
    hrecorder, ledgerStarted, hstartSuccess, hstartCandidate, input, hinput,
    hinputDomain, hinputCheck, htransition, hquota, hrawParsed, _, _,
    hreceive, hbankUpdate, _, _, diagnostic, hreceiveDiagnostic,
    hdiagnosticInput, hdiagnosticExpected, hdiagnosticAfter, hdiagnosticRaw,
    hdiagnosticParsed, hdiagnosticAccepted, _, hdiagnosticWrong,
    hbankFrame, _⟩ := hreceiver hshort
  have hindexBound : k < execution.records.length := by
    simpa only [execution, generatedFirstCutoffRun,
      ReferenceActivePhysicalHorizon.run_record_count] using hk
  have hRindex : receiverCut = execution.records[k]'hindexBound := by
    have hget := List.getElem_of_eq hRsplit (i := k) (by
      simpa only [ReferenceActivePhysicalHorizon.run_record_count] using hk)
    symm
    calc
      execution.records[k]'hindexBound = (window ++ receiverCut :: receiverSuffix)[k]'(by
          simp only [List.length_append, List.length_cons]
          omega) := hget
      _ = receiverCut := by
        rw [List.getElem_append_right (show window.length ≤ k from le_rfl)]
        simp only [k, Nat.sub_self, List.getElem_cons_zero]
  have hRcut : receiverCut = cut := hRindex.trans hindex.symm
  clear hRindex
  subst receiverCut
  -- Inject the actual constructors, including their dependent operation witnesses.
  have hRtags := hlive.symm.trans hRlive
  cases hRtags
  have hRoutcome := hbranch.symm.trans hRbranch
  cases hRoutcome
  have hD := ReferenceFirstCutoffFinishSafety.run_first_cutoff_finish_domains
    initial z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s count
    hspan active hfirst hshort
  dsimp only at hD
  rcases hD with ⟨finishCut, finishSuffix, _, hDindex, _, rD, qD, baseD,
    hDstate, hDprefix, dispatchedD, hstartD, ledgerD, hinitD, hledgerD, hdomainD,
    hclockD, hpendingD, hnoAssignmentD, selectedD, hDbranch, recordingD,
    _, _, hDdiagnostic, _, ledgerStartedD,
    hDstart, hDcandidate, _, _, _, _, _, hfinish⟩
  have hDcut : finishCut = cut := hDindex.trans hindex.symm
  clear hDindex
  subst finishCut
  have hDlive : cut.input.state.coordinator = .live rD qD baseD := by
    rw [hDstate]
    exact hDprefix
  have hDtags := hlive.symm.trans hDlive
  cases hDtags
  have hDoutcome := hbranch.symm.trans hDbranch
  cases hDoutcome
  have hrecording : recordingD = recording :=
    Option.some.inj (hDdiagnostic.symm.trans hdiagnostic)
  subst recordingD
  have hstarted : ledgerStartedD = ledgerStarted := by
    exact CoordinatorCollectionLedger.Checked.success.inj (hDstart.symm.trans hstartSuccess)
  clear hDcandidate
  subst ledgerStartedD
  -- Keep the returned bank separate until the actual finish commits it.
  let decoded : ReferenceActivePhysicalStep.Ledger rate :=
    { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded }
  let bank := CoordinatorUpReception.decoderBankAfter input
  obtain ⟨finished, hfinishSuccess, hfinishedValid, hclockFinish, hconfiguration,
    hcommittedBank, hfailure, hrecordingOutput, hupOutput⟩ :=
    hfinish decoded bank (Or.inr hreceive)
  have hprepared : cut.output.preparation = prepare cut.input := by
    rw [cut.output_eq]
    rfl
  have hnextCoordinator : cut.output.next.coordinator =
      .collection r.payload finished dispatched.startResult.clock.lastProposal := by
    rw [cut.output_eq] at hconfiguration ⊢
    exact hconfiguration
  have hnextBank : cut.output.next.upDecoderBank = bank := by
    rw [cut.output_eq] at hcommittedBank ⊢
    exact hcommittedBank
  have hsuccessor : successorRun.finalState = cut.output.next := by
    -- This prefix may end at T; its construction needs no further Fin T action.
    dsimp only [successorRun]
    rw [ReferenceActivePhysicalHorizon.run_successor_step]
    change (step (roundInputAt initial z.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active prefixRun
      ⟨s + k, by omega, by omega⟩)).next = cut.output.next
    have hroundInput : roundInputAt initial z.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p z) rewards s active prefixRun
        ⟨s + k, by omega, by omega⟩ = cut.input := by
      have htimeFin : cut.input.time = ⟨s + k, by omega⟩ := Fin.ext htime
      exact round_input_ext hstate.symm hrows.symm hselected.symm htimeFin.symm hrewards.symm
    rw [hroundInput, cut.output_eq]
  let choice : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨r.payload, sharedLedger ledger, dispatched.startResult,
      (liveRegistersAt r cut.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (liveRegistersAt r cut.input.time) (liveOwnedAt r q cut.input.time) base cut.input.time)⟩
  have hchoice : ReferenceCollectionSegmentExtraction.choice cut.input = some choice := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [← hprepared, hbranch]
    simp only [DispatchCut.selection, selectionAt, liveRegistersAt, dite_eq_left rfl,
      reduceCtorEq, ↓reduceIte, ReferenceCollectionSegmentExtraction.choiceOfCut]
    rfl
  obtain ⟨completed, hextract⟩ := ReferenceCollectionSegmentExtraction.actual_collection_round_complete
    cut choice r.payload finished dispatched.startResult.clock.lastProposal hchoice hnextCoordinator
  obtain ⟨hcompletedChoice, hcompletedRound, hchecked, payloadX, proposalX, hXendpoint⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_checked cut completed hextract
  have hcontext : completed.context = choice :=
    Option.some.inj (hcompletedChoice.symm.trans hchoice)
  obtain ⟨recordingX, startedX, decodedX, bankX, hXrecording, _, hXstart,
    hXinput, hXreceive, _⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_inputs cut completed hextract
  have hXrecord : recordingX = recording :=
    Option.some.inj (hXrecording.symm.trans hrecordingOutput)
  subst recordingX
  rw [hcontext] at hXstart hXinput
  have hXstarted : startedX = ledgerStarted := by
    exact CoordinatorCollectionLedger.Checked.success.inj (hXstart.symm.trans hstartSuccess)
  subst startedX
  have haccepted : completed.accepted = false := by
    -- The extracted receiver call is the same call already proved rejected above.
    rw [← hprepared, hreceive] at hXreceive
    cases ha : completed.accepted with
    | false => rfl
    | true => simp only [ha, ↓reduceIte, reduceCtorEq] at hXreceive
  have hfinal : completed.final = finished := by
    exact (CoordinatorConfiguration.collection.inj (hXendpoint.symm.trans hnextCoordinator)).2.1
  refine ⟨hsT, cut, suffix, hsplit, hindex, htime, hstate, hrows, hselected, hrewards,
    r, q, base, hlive, hsigma, dispatched, hstart, ledger, hinit, hledger, hdomain,
    hclock, hpending, hnoAssignment, selected, hbranch, ?_, ?_, ?_,
    hledgerSigma, ?_, recording, hactualInput, htrace, hdiagnostic, hrecorder,
    ledgerStarted, hstartSuccess, hstartCandidate, input, decoded, bank, diagnostic,
    finished, hinput, hinputDomain, hinputCheck, htransition, hquota, rfl, hreceive, rfl, hbankUpdate,
    hbankFrame, hrawParsed, hreceiveDiagnostic, hdiagnosticInput, hdiagnosticExpected,
    hdiagnosticAfter, hdiagnosticRaw, hdiagnosticParsed, hdiagnosticAccepted,
    hdiagnosticWrong, hfinishSuccess, hfinishedValid, hclockFinish, hconfiguration,
    hfailure, hcommittedBank, hrecordingOutput, ?_, hnextCoordinator, hnextBank,
    hsuccessor, ?_, ?_, hchoice, completed, hextract, hcontext, hXinput,
    hcompletedRound, haccepted, hfinal, ?_⟩
  · omega
  · simpa only [htime] using huT
  · simpa only [htime] using huGrid
  · simpa only [htime] using hledgerCut
  · exact hupOutput.trans hreceiveDiagnostic
  · rw [hsuccessor]; exact hnextCoordinator
  · rw [hsuccessor]; exact hnextBank
  · simpa only [hcontext, haccepted, hfinal] using hchecked

end Bandits.Support.ReferenceGeneratedFirstCutoffCoordinatorEndpoint

end
