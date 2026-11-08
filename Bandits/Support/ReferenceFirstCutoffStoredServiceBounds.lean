/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

import Lean.Elab.Tactic.Omega

/-!
# Stored-service bounds at the actual first cutoff

The first cutoff's outside registers come from the live diagnostic replay.
At the rejected receiver's actual finish, the initialized cutoff registers
are retained and the first collection increment is one capped service update.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:41-70,
246-269,294`, `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`,
and `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceFirstCutoffStoredServiceBounds

variable {p : ConstructorDimensions.Parameters}

private theorem diagnostic_replay_last_service_bounds
    (capacity initialQueue : ℕ) (records : List (Bool × ℕ)) :
    CollectionKnownQueueContinuation.replayLastService capacity (0, initialQueue) 0 records ≤
        (QueueReplay.replay capacity (0, initialQueue) records).1 ∧
      CollectionKnownQueueContinuation.replayLastService capacity (0, initialQueue) 0 records ≤
        capacity := by
  classical
  cases hnil : records with
  | nil =>
      simp [CollectionKnownQueueContinuation.replayLastService, QueueReplay.replay]
  | cons first rest =>
      have hne : records ≠ [] := by simp [hnil]
      let last := records.getLast hne
      let pre := records.dropLast
      have hsplit : pre ++ [last] = records :=
        List.dropLast_append_getLast hne
      have hsplit' : pre ++ [last] = first :: rest := hsplit.trans hnil
      have hlast : (pre ++ [last]).getLast? = some last := by
        simp [pre, last]
      have hdrop : (pre ++ [last]).dropLast = pre := by simp
      rw [← hsplit']
      rcases last with ⟨enabled, arrival⟩
      let before := QueueReplay.replay capacity (0, initialQueue) pre
      cases enabled with
      | false =>
        have hlastService :
            CollectionKnownQueueContinuation.replayLastService capacity
                (0, initialQueue) 0 (pre ++ [(false, arrival)]) = 0 := by
          simp [CollectionKnownQueueContinuation.replayLastService, hlast, hdrop,
            QueueReplay.transition]
        have hfinal :
            QueueReplay.replay capacity (0, initialQueue) (pre ++ [(false, arrival)]) =
              before := by
          rw [QueueReplay.replay_append]
          simp [before, QueueReplay.replay, QueueReplay.transition]
        constructor
        · rw [hlastService, hfinal]
          exact Nat.zero_le _
        · rw [hlastService]
          exact Nat.zero_le _
      | true =>
        let service := min capacity (before.2 + arrival)
        have hserviceCap : service ≤ capacity := Nat.min_le_left _ _
        have hlastService :
            CollectionKnownQueueContinuation.replayLastService capacity
                (0, initialQueue) 0 (pre ++ [(true, arrival)]) = service := by
          simp [CollectionKnownQueueContinuation.replayLastService, hlast, hdrop,
            before, service, QueueReplay.transition]
        have hfinal :
            QueueReplay.replay capacity (0, initialQueue) (pre ++ [(true, arrival)]) =
              (before.1 + service, before.2 + arrival - service) := by
          rw [QueueReplay.replay_append]
          simp [before, service, QueueReplay.replay, QueueReplay.transition]
        constructor
        · rw [hlastService, hfinal]
          exact Nat.le_add_left _ _
        · rw [hlastService]
          exact hserviceCap

/-- At the actual first cutoff, the diagnostic-seeded preledger and the
rejected-receiver FINISH ledger have literal stored-service bounds.  The
cutoff and ready states are the indexed record of the original actual run.
The only execution selectors are the initialization crossing, the bounded
run span, and that the first live window reaches its first cutoff. -/
theorem actual_first_cutoff_stored_service_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
    let w := window.length
    let hw : w < E.records.length := by
      have hcount : E.records.length = count := by
        simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          ReferenceActivePhysicalHorizon.run_record_count
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState
              rate source rewards C_star C_h hcross)
            source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
            rewards
            (ReferenceInitializationRun.elapsed p
              (ReferenceInitializationRun.output
                (ActualReferenceInitializationBlock.referenceInput
                  source rewards C_star C_h rate)).completed)
            count hspan
            (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
              rate source rewards C_star C_h hcross).1
      rw [hcount]
      exact hshort
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))),
      E.records = window ++ cut :: suffix ∧
      cut = E.records.get ⟨w, hw⟩ ∧
      cut.input.time.val = s + w ∧
      cut.input.rows = source.1.2 ∧
      cut.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
      cut.input.rewards = rewards ∧
      ∃ (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
        (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
        (base : Fin (p.m - 1) → ℕ),
        cut.input.state.coordinator = .live r q base ∧
        let callInput := ReferenceActivePhysicalStep.liveInput cut.input r q base
        ∃ (dispatched : CoordinatorStartRoundCutoffDispatch.Output
            callInput.registers callInput.ownedRegisters base)
          (hstart : CoordinatorPhaseClock.startRound p rate.eta.val
            callInput.registers.time callInput.registers.priorClock
            callInput.registers.clockPending = .ok dispatched.startResult)
          (ledger : CoordinatorStartRoundCutoffDispatch.NewLedger callInput.registers)
          (hinit : dispatched.collectionInitialization = .success (some ledger))
          (hledger : ledger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hdomain : CoordinatorStartRoundCutoffDispatch.initializationDomainValid
            callInput.registers callInput.ownedRegisters base callInput.registers.time)
          (hclock : dispatched.startResult.clock =
            { callInput.registers.priorClock with u := some callInput.registers.time })
          (hpending : dispatched.startResult.pending = Finset.univ)
          (hnoAssignment : dispatched.startResult.assignmentStart = none)
          (selected : CoordinatorRoundDispatch.ArmSelection callInput.registers.payload
            dispatched.startResult callInput.registers.time
            callInput.registers.complementWeights cut.input.row),
          cut.output.preparation.coordinator = .live r q base
            (.cutoffChosen dispatched hstart ledger hinit hledger hdomain hclock hpending
              hnoAssignment selected) ∧
          ∃ (l0 : ReferenceActivePhysicalStep.Ledger rate)
            (initializer : ReferenceCollectionSegmentExtraction.Initializer p)
            (choice : ReferenceCollectionSegmentExtraction.Choice rate),
            l0 = ReferenceActivePhysicalStep.sharedLedger ledger ∧
            initializer = ReferenceCollectionSegmentExtraction.cutoffInitializer
              callInput.registers callInput.ownedRegisters base callInput.registers.time ∧
            ReferenceCollectionSegmentExtraction.choice cut.input = some choice ∧
            choice.initializer = some initializer ∧
            initializer.checkedStart rate = .success l0 ∧
            l0.cursor = s + w + 1 ∧ l0.cutoff = s + w + 1 ∧
            l0.freezeAt = r.gridBoundary ∧ s + w + 1 ≤ r.gridBoundary ∧
            (∀ a c, l0.cutoffRegisters a = some c →
              c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n) ∧
            (∀ a, l0.increment a ≤
              4 * rate.n * (min l0.cursor l0.freezeAt - l0.cutoff)) ∧
            ∃ (recording : CoordinatorRecordingOperation.Output p)
              (ledgerStarted : ReferenceActivePhysicalStep.Ledger rate)
            (input : _)
              (decoded : ReferenceActivePhysicalStep.Ledger rate)
              (bank : _)
              (f : ReferenceActivePhysicalStep.Ledger rate),
              ReferenceCoordinatorRecorderCallTrace.recording
                (ReferenceActiveHorizonMeasurability.roundRecordCode cut) = some recording ∧
              ledgerStarted = CoordinatorCollectionLedger.startRoundCandidate l0
                cut.input.time (ReferenceActivePhysicalStep.collectionEnabled l0 cut.input.time)
                (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) ∧
              input = ReferenceUpReception.receptionInputAtRow rate cut.input.row
                (ReferenceActivePhysicalStep.upInputs cut.output.preparation ledgerStarted)
                cut.input.time ∧
              decoded = { input.ledger with phase := CoordinatorCollectionLedger.Phase.decoded } ∧
              (ReferenceActivePhysicalStep.receiveUp cut.output.preparation ledgerStarted).result =
                .rejected (decoded, bank) ∧
              CoordinatorCollectionLedger.finishRound decoded = .success f ∧
              cut.output.next.coordinator =
                .collection r.payload f dispatched.startResult.clock.lastProposal ∧
              f.cutoff = s + w + 1 ∧ f.cursor = s + w + 2 ∧
              f.freezeAt = r.gridBoundary ∧
              f.cutoffRegisters = l0.cutoffRegisters ∧
              (∀ a c, f.cutoffRegisters a = some c →
                c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n) ∧
              (∀ a, f.increment a ≤
                4 * rate.n * (min f.cursor f.freezeAt - f.cutoff)) := by
  classical
  let I := ReferenceInitializationRun.output
    (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
  let s := ReferenceInitializationRun.elapsed p I.completed
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let window := ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records
  let w := window.length
  have hcount : E.records.length = count := by
    simpa [E, ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
      ReferenceActivePhysicalHorizon.run_record_count
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1
  have hw : w < count := by
    simpa [window, E] using hshort
  have hwE : w < E.records.length := by rw [hcount]; exact hw
  let cutE := E.records.get ⟨w, hwE⟩
  have hgeneratedRun :
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records = E.records := by
    change
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s rfl)).records = E.records
    change
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).records = E.records
    rfl
  have hshortGenerated : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s rfl count hspan).records).length < count := by
    rw [hgeneratedRun]
    exact hshort
  have hroot :=
    ReferenceGeneratedFirstCollectionAdmissionBoundary.actual_generated_first_collection_admission_boundary
      rate source rewards C_star C_h hcross s rfl count hspan hshortGenerated
  dsimp only at hroot
  rcases hroot with ⟨cutRoot, _rootPayload, _rootSaved, hrootIndex, _hrootBoundary⟩
  have hrootCut : cutRoot = cutE := by
    simpa [cutE, hgeneratedRun] using hrootIndex
  have hactualLaunchActive :=
    ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross
  have hseedActive : ReferenceActivePhysicalHorizon.allActiveAtStart
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross) s :=
    hactualLaunchActive.1
  have hseedFirst :
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross).coordinator =
        .first := hactualLaunchActive.2
  have hseedRun :
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan hseedActive).records = E.records := by
    change
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan hseedActive).records =
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan
        (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
          rate source rewards C_star C_h hcross).1).records
    congr 1
  have hseedWindowLength :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hseedActive).records).length = w := by
    rw [hseedRun]
  have hgeneratedWindowLength :
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
          rate source rewards C_star C_h hcross s rfl count hspan).records).length = w := by
    rw [hgeneratedRun]
  have hshortSeed : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan hseedActive).records).length < count := by
    rw [hseedRun]
    exact hshort
  have houtside :=
    ReferenceFirstCutoffOutsideInitialization.run_first_cutoff_outside_initializer
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s count hspan hseedActive hseedFirst hshortSeed
  dsimp only at houtside
  rcases houtside with ⟨cutOutside, suffixOutside, hsplitOutside, hindexOutside,
    htimeOutside, hactualOutside, rOutside, qOutside, baseOutside, hstateOutside,
    hliveOutside, dispatchOutside, hstartOutside, ledgerOutside, hinitOutside,
    hledgerOutside, hdomainOutside, hclockOutside, hpendingOutside,
    hnoAssignmentOutside, selectedOutside, hbranchOutside, hkPositiveOutside,
    hsigmaOutside, hbaseOutside, hbirthOutside, hproposalsOutside, hqueuesOutside,
    huOutside, hsigmaBeforeOutside, huTOutside, huGridOutside, hgridTOutside,
    hsigmaLedgerOutside, hcutoffLedgerOutside, hfreezeLedgerOutside,
    hfirstCutoffOutside, hslowAbsentOutside, hregistersOutside, hcutoffRegisters,
    hcurrentRegisters, _hbaseScore, _hpending, hincrement, _hgamma, _hraw, _henabled,
    hcursor, _hphase, _hsharedCutoff, _hsharedCurrent, _hsharedIncrement, _hsharedGamma,
    _hsharedRaw, _hsharedEnabled, _hsharedCursor, _hsharedPhase, hinitializerData⟩
  rcases hinitializerData with ⟨initializer, choice, hinitializer, hchoice,
    hchoiceInitializer, hcheckedStart⟩
  have houtsideIndex : cutOutside = cutE := by
    simpa [cutE, hseedRun] using hindexOutside
  have hrootOutside : cutRoot = cutOutside := hrootCut.trans houtsideIndex.symm
  have hready := ReferenceFirstCollectionReadyInitialization.actual_first_collection_ready_initialization
    rate source rewards C_star C_h hcross s rfl count hspan hshortGenerated
  dsimp only at hready
  rcases hready with ⟨hsT, cutReady, suffixReady, hsplitReady, hindexReady,
    htimeReady, hstateReady, hrowsReady, hselectedReady, hrewardsReady,
    rReady, qReady, baseReady, hreadyLive, hsigmaReady, dispatchReady,
    hstartReady, ledgerReady, hinitReady, hledgerReady, hdomainReady,
    hclockReady, hpendingReady, hnoAssignmentReady, selectedReady,
    hbranchReady, huReady, huTReady, hugReady, hsigmaLedgerReady,
    hcutoffLedgerReady, recordingReady, hactualInputReady, htraceReady,
    hrecordingDiagnosticReady, hrecordingRunReady, ledgerStartedReady,
    hstartSuccessReady, hstartCandidateReady, inputReady, decodedReady,
    bankReady, _diagnosticReady, finishedReady, hinputReady,
    hinputDomainReady, hinputCheckReady, htransitionReady, hquotaReady,
    hdecodedReady, hreceiveReady, hbankReady, hbankUpdateReady, hbankFrameReady,
    hrawParsedReady, hreceiveDiagnosticReady, hdiagnosticInputReady,
    hdiagnosticExpectedReady, hdiagnosticAfterReady, hdiagnosticRawReady,
    hdiagnosticParsedReady, hdiagnosticAcceptedReady, hdiagnosticWrongReady,
    hfinishReady, hreadyTail⟩
  rcases hreadyTail with ⟨_hvalidFinishedReady, _hclockFinishReady,
    hconfigurationReady, hfailureReady, hbankOutputReady, hrecordOutputReady,
    hupOutputReady, hnextReady, hnextBankReady, hsuccessorReady,
    hsuccessorCoordinatorReady, hsuccessorBankReady, hreadyFinalTail⟩
  rcases hreadyFinalTail with ⟨_hphaseFinishedReady, _hsigmaFinishedReady,
    hcutoffFinishedReady, hcursorFinishedReady, hfreezeFinishedReady,
    _hfreezeBoundFinishedReady, _hassignmentFinishedReady, hreadyFinalRest⟩
  have hreadyIndex : cutReady = cutE := by
    simpa [cutE, hgeneratedRun] using hindexReady
  have hrootReady : cutRoot = cutReady := hrootCut.trans hreadyIndex.symm
  clear hindexOutside houtsideIndex hactualOutside hindexReady hreadyIndex
  subst cutOutside
  subst cutReady
  have hsamePreparation := hbranchOutside.symm.trans hbranchReady
  cases hsamePreparation
  let t := cutRoot.input.time
  let u := s + w + 1
  let l0 : ReferenceActivePhysicalStep.Ledger rate :=
    ReferenceActivePhysicalStep.sharedLedger ledgerOutside
  have htimeValue : t.val + 1 = u := by
    change cutRoot.input.time.val + 1 = u
    rw [htimeOutside]
    rw [hseedWindowLength]
  have hl0Cutoff : l0.cutoff = u := by
    change ledgerOutside.cutoff = u
    rw [hcutoffLedgerOutside]
    exact htimeValue
  have hl0Cursor : l0.cursor = u := by
    change ledgerOutside.cursor = u
    rw [hcursor]
    exact htimeValue
  have hl0Increment : l0.increment = fun _ => 0 := by
    change ledgerOutside.increment = fun _ => 0
    exact hincrement
  have hl0Freeze : l0.freezeAt = rOutside.gridBoundary := by
    change ledgerOutside.freezeAt = rOutside.gridBoundary
    exact hfreezeLedgerOutside
  have huFreeze : u ≤ l0.freezeAt := by
    rw [hl0Freeze, ← htimeValue]
    exact huGridOutside
  have hl0Current : l0.currentRegisters = fun a =>
      (l0.cutoffRegisters a).map (fun c =>
        (⟨c.queue, c.lastService⟩ : CoordinatorCollectionLedger.CurrentRegister)) := by
    change ledgerOutside.currentRegisters = fun a =>
      (ledgerOutside.cutoffRegisters a).map (fun c =>
        (⟨c.queue, c.lastService⟩ : CoordinatorCollectionLedger.CurrentRegister))
    rw [hcurrentRegisters, hcutoffRegisters]
  have hl0CutoffRegisters : l0.cutoffRegisters =
      CoordinatorStartRoundCutoffDispatch.outsideRegisters
        (ReferenceActivePhysicalStep.liveInput cutRoot.input rOutside qOutside baseOutside).registers
        (ReferenceActivePhysicalStep.liveInput cutRoot.input rOutside qOutside baseOutside).ownedRegisters := by
    change ledgerOutside.cutoffRegisters = _
    exact hcutoffRegisters
  have hsharedPayloadRate : rOutside.payload.n = rate.n :=
    ReferenceActivePhysicalStep.payload_n_eq rOutside.payload
  let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recordingReady
  let enabled := ReferenceActivePhysicalStep.collectionEnabled l0 t
  have henabled : enabled = decide (u < l0.freezeAt) := by
    dsimp [enabled, ReferenceActivePhysicalStep.collectionEnabled]
    have hsigmapos : 0 < l0.sigma := by
      change 0 < ledgerOutside.sigma
      rw [hsigmaLedgerOutside]
      omega
    rw [hl0Cutoff, htimeValue]
    simp [hsigmapos]
  have hreadyInputLedger : inputReady.ledger = ledgerStartedReady := by
    rw [hinputReady]
    rfl
  have hdecodedStarted : decodedReady =
      { ledgerStartedReady with phase := CoordinatorCollectionLedger.Phase.decoded } := by
    rw [hdecodedReady, hreadyInputLedger]
  have hstartedEq : ledgerStartedReady =
      CoordinatorCollectionLedger.startRoundCandidate l0 t enabled raw := by
    simpa [l0, t, enabled, raw] using hstartCandidateReady
  have hfinishCandidate : finishedReady =
      CoordinatorCollectionLedger.finishRoundCandidate decodedReady := by
    unfold CoordinatorCollectionLedger.finishRound at hfinishReady
    split at hfinishReady
    · dsimp only at hfinishReady
      split at hfinishReady
      · exact (CoordinatorCollectionLedger.Checked.success.inj hfinishReady).symm
      · cases hfinishReady
    · cases hfinishReady
  have hfinishedCutoff : finishedReady.cutoffRegisters = l0.cutoffRegisters := by
    rw [hfinishCandidate, hdecodedStarted, hstartedEq]
    rfl
  have hfinishedFreeze : finishedReady.freezeAt = l0.freezeAt := by
    rw [hfinishCandidate, hdecodedStarted, hstartedEq]
    rfl
  have hfinishIncrement (a : Fin p.K) : finishedReady.increment a =
      (CoordinatorCollectionLedger.startRoundCandidate l0 t enabled raw).gammaLoc a := by
    rw [hfinishCandidate, hdecodedStarted, hstartedEq]
    simp [CoordinatorCollectionLedger.finishRoundCandidate,
      CoordinatorCollectionLedger.startRoundCandidate, hl0Increment]
  have hserviceFacts (a : Fin p.K) :
      (CoordinatorCollectionLedger.startRoundCandidate l0 t enabled raw).gammaLoc a ≤
          4 * rate.n ∧
        (¬ u < l0.freezeAt →
          (CoordinatorCollectionLedger.startRoundCandidate l0 t enabled raw).gammaLoc a = 0) := by
    cases hregister : l0.cutoffRegisters a with
    | none =>
        have hunknown : l0.currentRegisters a = none := by
          rw [hl0Current]
          simp [hregister]
        have hzero := CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
          l0 t enabled raw a hunknown
        exact ⟨by omega, fun _ => hzero⟩
    | some c =>
        have hcurrent : l0.currentRegisters a = some
            (⟨c.queue, c.lastService⟩ : CoordinatorCollectionLedger.CurrentRegister) := by
          rw [hl0Current]
          simp [hregister]
        by_cases hactive : u < l0.freezeAt
        · have henabled : enabled = true := by simp [henabled, hactive]
          have hrecord : CoordinatorCollectionLedger.localQueueRecord l0 t enabled raw a =
              (true, CoordinatorCollectionLedger.localArrival raw a) := by
            simp [CoordinatorCollectionLedger.localQueueRecord, henabled,
              htimeValue, hactive, CoordinatorCollectionLedger.sourceRound]
          have hgamma :
              (CoordinatorCollectionLedger.startRoundCandidate l0 t enabled raw).gammaLoc a =
                min (4 * rate.n) (c.queue + CoordinatorCollectionLedger.localArrival raw a) := by
            simp [CoordinatorCollectionLedger.startRoundCandidate, hcurrent,
              hrecord, QueueReplay.transition]
          refine ⟨?_, ?_⟩
          · rw [hgamma]
            exact Nat.min_le_left _ _
          · intro hnot
            exact (hnot hactive).elim
        · have hgamma :
              (CoordinatorCollectionLedger.startRoundCandidate l0 t enabled raw).gammaLoc a = 0 := by
            have henabled : enabled = false := by simp [henabled, hactive]
            simp [CoordinatorCollectionLedger.startRoundCandidate, hcurrent,
              CoordinatorCollectionLedger.localQueueRecord, henabled,
              htimeValue, hactive, CoordinatorCollectionLedger.sourceRound,
              QueueReplay.transition]
          exact ⟨by omega, fun _ => hgamma⟩
  have hwidthEnabled : u < l0.freezeAt → min (u + 1) l0.freezeAt - u = 1 := by
    intro hactive
    have hsucc : u + 1 ≤ l0.freezeAt := Nat.succ_le_of_lt hactive
    simp [Nat.min_eq_left hsucc]
  have hwidthFrozen : ¬ u < l0.freezeAt → min (u + 1) l0.freezeAt - u = 0 := by
    intro hactive
    have heq : l0.freezeAt = u := by omega
    rw [heq]
    simp
  have hfinishService (a : Fin p.K) : finishedReady.increment a ≤
      4 * rate.n * (min finishedReady.cursor finishedReady.freezeAt - finishedReady.cutoff) := by
    have hcursor : finishedReady.cursor = u + 1 := by
      simpa [u, hgeneratedWindowLength, Nat.add_assoc] using hcursorFinishedReady
    have hcutoff : finishedReady.cutoff = u := by
      simpa [u, hgeneratedWindowLength, Nat.add_assoc] using hcutoffFinishedReady
    rw [hcursor, hfinishedFreeze, hcutoff]
    by_cases hactive : u < l0.freezeAt
    · rw [hwidthEnabled hactive]
      rw [hfinishIncrement a]
      simpa only [Nat.mul_one] using (hserviceFacts a).1
    · rw [hwidthFrozen hactive]
      rw [hfinishIncrement a, (hserviceFacts a).2 hactive]
      simp
  have hcutoffBoundsInit : ∀ a c, l0.cutoffRegisters a = some c →
      c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n := by
    intro a c hc
    have hfast : a ∈ CanonicalFastSampling.fastArmFinset rOutside.payload.slowSet := by
      by_contra hnot
      have hnone := hslowAbsentOutside a hnot
      rw [hl0CutoffRegisters] at hc
      rw [hnone] at hc
      cases hc
    let fastArm : CanonicalFastSampling.FastArm rOutside.payload.slowSet := ⟨a, hfast⟩
    let diagnostic := ReferenceFirstComplementReplay.liveDiagnosticQueueRecords
      rOutside.payload a (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceActivePhysicalHorizon.run
          (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
          source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
          rewards s count hspan hseedActive).records) w
    have houtside := hregistersOutside fastArm
    have hregister : c = {
        score := (QueueReplay.replay (4 * rOutside.payload.n) (0, 0) diagnostic).1
        queue := (QueueReplay.replay (4 * rOutside.payload.n) (0, 0) diagnostic).2
        lastService := CollectionKnownQueueContinuation.replayLastService
          (4 * rOutside.payload.n) (0, 0) 0 diagnostic } := by
      apply Option.some.inj
      calc
        some c = l0.cutoffRegisters a := hc.symm
        _ = CoordinatorStartRoundCutoffDispatch.outsideRegisters
            (ReferenceActivePhysicalStep.liveInput cutRoot.input rOutside qOutside baseOutside).registers
            (ReferenceActivePhysicalStep.liveInput cutRoot.input rOutside qOutside baseOutside).ownedRegisters a := by
              rw [hl0CutoffRegisters]
        _ = some {
            score := (QueueReplay.replay (4 * rOutside.payload.n) (0, 0) diagnostic).1
            queue := (QueueReplay.replay (4 * rOutside.payload.n) (0, 0) diagnostic).2
            lastService := CollectionKnownQueueContinuation.replayLastService
              (4 * rOutside.payload.n) (0, 0) 0 diagnostic } := by
                simpa [fastArm, diagnostic, hseedRun] using houtside
    have hbounds := diagnostic_replay_last_service_bounds
      (4 * rOutside.payload.n) 0 diagnostic
    rw [hregister]
    constructor
    · exact hbounds.1
    · simpa [hsharedPayloadRate] using hbounds.2
  have hl0IncBound : ∀ a, l0.increment a ≤
      4 * rate.n * (min l0.cursor l0.freezeAt - l0.cutoff) := by
    intro a
    rw [hl0Increment, hl0Cursor, hl0Cutoff]
    simp [Nat.min_eq_left huFreeze]
  have hfrozenCutoffRegisters : finishedReady.cutoffRegisters = l0.cutoffRegisters :=
    hfinishedCutoff
  have hfinishedCutoffBounds : ∀ a c, finishedReady.cutoffRegisters a = some c →
      c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n := by
    intro a c hc
    rw [hfrozenCutoffRegisters] at hc
    exact hcutoffBoundsInit a c hc
  have hsplitActual : E.records = window ++ cutRoot :: suffixOutside := by
    simpa [window, hseedRun] using hsplitOutside
  have hcutLive : cutRoot.input.state.coordinator = .live rOutside qOutside baseOutside := by
    rw [hstateOutside]
    exact hliveOutside
  have hcutTime : cutRoot.input.time.val = s + w := by
    simpa [s, w, hseedWindowLength] using htimeOutside
  refine ⟨cutRoot, suffixOutside, hsplitActual, hrootCut, hcutTime,
    hrowsReady, hselectedReady, hrewardsReady, rOutside, qOutside, baseOutside,
    hcutLive, ?_⟩
  refine ⟨dispatchOutside, hstartOutside, ledgerOutside, hinitOutside,
    hledgerOutside, hdomainOutside, hclockOutside, hpendingOutside,
    hnoAssignmentOutside, selectedOutside, hbranchOutside, ?_⟩
  refine ⟨l0, initializer, choice, rfl, hinitializer, hchoice,
    hchoiceInitializer, ?_, ?_, ?_, ?_, ?_, hcutoffBoundsInit, hl0IncBound, ?_⟩
  · simpa [l0] using hcheckedStart
  · simpa [u] using hl0Cursor
  · simpa [u] using hl0Cutoff
  · exact hl0Freeze
  · simpa [u, hl0Freeze] using huFreeze
  · refine ⟨recordingReady, ledgerStartedReady, inputReady, decodedReady,
      bankReady, finishedReady, htraceReady, ?_, hinputReady,
      hdecodedReady, hreceiveReady, hfinishReady, hnextReady, ?_, ?_,
      ?_, hfinishedCutoff, hfinishedCutoffBounds, hfinishService⟩
    · simpa [t, enabled, raw] using hstartedEq
    · simpa [u, hgeneratedWindowLength, Nat.add_assoc] using hcutoffFinishedReady
    · simpa [u, hgeneratedWindowLength, Nat.add_assoc] using hcursorFinishedReady
    · exact hfinishedFreeze.trans hl0Freeze

end Bandits.Support.ReferenceFirstCutoffStoredServiceBounds

end
