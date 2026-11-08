/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionAdmissionBoundary

import Lean.Elab.Tactic.Omega

/-!
# One actual first-collection stored-service step

This file proves a numerical induction step for one record of the actual
first-collection run.  The incoming ledger, the parsed UP word, the recording,
the checked START, the filtered reception, and the checked FINISH all remain
the operations of that same physical record.

The three incoming conditions are local induction inputs: the literal ready
domain from `ReferenceContinuingCollectionStartDomains`, together with the
stored cutoff last-service and collection-increment inequalities.  This step
does not assert them for every record and does not derive physical-source
arrival or score identities from them.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:16-28,
41-70,80-100,277-294`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:46-79`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174,219-243`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionStoredServiceStep

/-! ### The one local service estimate -/

/-- Starting a round adds at most one service capacity to the stored
collection increment.  The only numerical induction premise is the literal
incoming increment inequality; no recorder cap or source-truth fact is used. -/
private theorem start_candidate_stored_increment_bound
    {p : ConstructorDimensions.Parameters}
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (t : Fin p.T)
    (raw : Option (Fin p.K × ℕ))
    (hcursor : l.cursor = t.val + 1)
    (hcut : l.cutoff ≤ l.cursor)
    (hfreeze : l.cutoff ≤ l.freezeAt)
    (hInc : ∀ a : Fin p.K,
      l.increment a ≤ 4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) :
    ∀ a : Fin p.K,
      l.increment a +
          (CoordinatorCollectionLedger.startRoundCandidate l t
            (ReferenceActivePhysicalStep.collectionEnabled l t) raw).gammaLoc a ≤
        4 * rate.n * (min (l.cursor + 1) l.freezeAt - l.cutoff) := by
  intro a
  have hcutMin : l.cutoff ≤ min l.cursor l.freezeAt :=
    Nat.le_min.mpr ⟨hcut, hfreeze⟩
  have hcutFromMinimum : l.cutoff ≤ l.cursor :=
    hcutMin.trans (Nat.min_le_left _ _)
  let candidate := CoordinatorCollectionLedger.startRoundCandidate l t
    (ReferenceActivePhysicalStep.collectionEnabled l t) raw
  have hservice : candidate.gammaLoc a ≤ 4 * rate.n := by
    by_cases hunknown : l.currentRegisters a = none
    · have hzero := CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
        l t (ReferenceActivePhysicalStep.collectionEnabled l t) raw a hunknown
      rw [show candidate.gammaLoc a =
        (CoordinatorCollectionLedger.startRoundCandidate l t
          (ReferenceActivePhysicalStep.collectionEnabled l t) raw).gammaLoc a by rfl]
      rw [hzero]
      exact Nat.zero_le _
    · cases hcurrent : l.currentRegisters a with
      | none => exact False.elim (hunknown hcurrent)
      | some current =>
          have hgamma : candidate.gammaLoc a =
              (QueueReplay.transition (4 * rate.n) (0, current.queue)
                (CoordinatorCollectionLedger.localQueueRecord l t
                  (ReferenceActivePhysicalStep.collectionEnabled l t) raw a)).1 := by
            simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
              hcurrent]
          rw [hgamma]
          have htransition :
              (QueueReplay.transition (4 * rate.n) (0, current.queue)
                (CoordinatorCollectionLedger.localQueueRecord l t
                  (ReferenceActivePhysicalStep.collectionEnabled l t) raw a)).1 ≤
                4 * rate.n := by
            by_cases henabled :
                (CoordinatorCollectionLedger.localQueueRecord l t
                  (ReferenceActivePhysicalStep.collectionEnabled l t) raw a).1 = true
            · simp [QueueReplay.transition, henabled]
            · simp [QueueReplay.transition, henabled]
          exact htransition
  by_cases hbefore : l.cursor < l.freezeAt
  · have hminOld : min l.cursor l.freezeAt = l.cursor := Nat.min_eq_left hbefore.le
    have hminNew : min (l.cursor + 1) l.freezeAt = l.cursor + 1 :=
      Nat.min_eq_left (by omega)
    clear hcut hfreeze hcutMin
    have hspan : l.cursor + 1 - l.cutoff =
        (l.cursor - l.cutoff) + 1 := by omega
    rw [hminOld] at hInc
    rw [hminNew, hspan]
    calc
      l.increment a + candidate.gammaLoc a ≤
          4 * rate.n * (l.cursor - l.cutoff) + 4 * rate.n :=
        Nat.add_le_add (hInc a) hservice
      _ = 4 * rate.n * ((l.cursor - l.cutoff) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  · have hfreezeCursor : l.freezeAt ≤ l.cursor := Nat.le_of_not_gt hbefore
    have henabled : ReferenceActivePhysicalStep.collectionEnabled l t = false := by
      cases hvalue : ReferenceActivePhysicalStep.collectionEnabled l t with
      | false => rfl
      | true =>
          have htest :
              0 < l.sigma ∧ l.cutoff ≤ t.val + 1 ∧ t.val + 1 < l.freezeAt := by
            simpa only [ReferenceActivePhysicalStep.collectionEnabled,
              decide_eq_true_eq] using hvalue
          exact False.elim (hbefore (by omega))
    have hgamma : candidate.gammaLoc a = 0 := by
      cases hcurrent : l.currentRegisters a <;>
        simp [candidate, CoordinatorCollectionLedger.startRoundCandidate,
          CoordinatorCollectionLedger.localQueueRecord, hcurrent, henabled,
          QueueReplay.transition]
    have hminOld : min l.cursor l.freezeAt = l.freezeAt :=
      Nat.min_eq_right hfreezeCursor
    have hminNew : min (l.cursor + 1) l.freezeAt = l.freezeAt :=
      Nat.min_eq_right (by omega)
    rw [hminOld] at hInc
    rw [hminNew, hgamma]
    simpa using hInc a

/-! ### The actual first-collection record -/

/-- Preserve the stored-service inequalities through one actual record of
the first collection window.

The first-collection run uses the original source arrays, complete continuous
reward table, and the shared initialization constants.  Its crossing and
reached-cutoff conditions only select this actual branch.

For the selected actual record, the hypotheses are precisely the actual
continuing-collection ready domain and the two literal local induction
inequalities.  In particular, no ordinary-follower survival or true physical
score identity is included in the ready-domain premise. -/
theorem actual_first_collection_stored_service_step
    {p : ConstructorDimensions.Parameters}
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ)
    (count : ℕ) :
    let I := ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)
    ∀ (hcross : I.crossing.isSome = true),
      let s := ReferenceInitializationRun.elapsed p I.completed
      ∀ (hspan : s + count ≤ p.T),
      let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length < count →
      let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
      let W := ReferenceCollectionPhaseHistory.collectionWindow E.records w
      ∀ (n : Fin W.length),
        let record := W[n]
        ∀ (payload : ReferenceActivePhysicalStep.Payload rate)
        (l : ReferenceActivePhysicalStep.Ledger rate)
        (saved : Option (Fin p.T × Bool)),
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          record.input payload l saved →
        (∀ a c, l.cutoffRegisters a = some c →
          c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n) →
        (∀ a, l.increment a ≤
          4 * rate.n * (min l.cursor l.freezeAt - l.cutoff)) →
        let x := record.input
        let candidate := CoordinatorCollectionLedger.startRoundCandidate l x.time
          (ReferenceActivePhysicalStep.collectionEnabled l x.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic record)
        let sender := ReferenceActivePhysicalStep.upSenderIndex x
        ∃ f : ReferenceActivePhysicalStep.Ledger rate,
          record.output.next.coordinator = .collection payload f saved ∧
          f.sigma = l.sigma ∧
          f.cursor = l.cursor + 1 ∧
          f.cutoff = l.cutoff ∧
          f.freezeAt = l.freezeAt ∧
          f.assignment = l.assignment ∧
          f.baseScore = l.baseScore ∧
          (((ReferenceCollectionSegmentExtraction.effectiveParse x candidate = none) ∨
              ∃ M : OrdinaryMessageCodec.UpRecord
                (CoordinatorCollectionLedger.codecParams p rate.eta.val),
                ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M ∧
                CoordinatorCollectionLedger.acceptUpCheck candidate sender M = false) →
            f.cutoffRegisters = l.cutoffRegisters) ∧
          (∀ M : OrdinaryMessageCodec.UpRecord
              (CoordinatorCollectionLedger.codecParams p rate.eta.val),
            ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M →
            CoordinatorCollectionLedger.acceptUpCheck candidate sender M = true →
              f.cutoffRegisters (l.assignment.arm sender) =
                some ⟨M.val.S, M.val.q, M.val.delta⟩ ∧
              (∀ b, b ≠ l.assignment.arm sender →
                f.cutoffRegisters b = l.cutoffRegisters b)) ∧
          (∀ a c, f.cutoffRegisters a = some c →
            c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n) ∧
          (∀ a, f.increment a ≤
            4 * rate.n * (min f.cursor f.freezeAt - f.cutoff)) := by
  intro I hcross s hspan E hshort w W n record payload l saved hReady hCut hInc
  let x := record.input
  let candidate := CoordinatorCollectionLedger.startRoundCandidate l x.time
    (ReferenceActivePhysicalStep.collectionEnabled l x.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic record)
  let sender := ReferenceActivePhysicalStep.upSenderIndex x
  have hReadyForFinish := hReady
  rcases hReady with ⟨_, _, _, _, _, _, _, _, hcutFreeze, _, _, hcursor,
    hcutCursor, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hcutCursor' : l.cutoff ≤ l.cursor := Nat.le_of_lt hcutCursor
  have hstage := start_candidate_stored_increment_bound l x.time
    (ReferenceCollectionRawBufferHistory.rawDiagnostic record)
    hcursor hcutCursor' hcutFreeze hInc

  cases hparse : ReferenceCollectionSegmentExtraction.effectiveParse x candidate with
  | none =>
      have hRejectedApi :=
        ReferenceContinuingCollectionRejectedFinishDomains.continuing_collection_rejected_finish_domains
          x payload l saved hReadyForFinish
      rcases hRejectedApi with ⟨cutoff, hcutoff, core, snap, hclockBound,
        hscores, hdispatch, harm, hlocal, hrecordInputs, o, l1, hrecordingRun,
        hstart, hstartCandidate, hstartValid, hstartPhase, hstartCursor,
        hstartSigma, hstartCutoff, hstartFreeze, hstartPending,
        hstartAssignment, hstartBase, hstartCutoffRegisters, hstartIncrement,
        hstartRegisters, hstartPairedMass, hstartCurrentBounds,
        hstartCutoffBounds, hstartPendingZero, hstartServiceBounds,
        hstartRawBounds, hstartEnabledHistory, hrejectedQuery⟩
      let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
        (ReferenceActivePhysicalStep.collectionInput x payload l
          (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
        snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
      let picked : ReferenceCollectionSegmentExtraction.Choice rate :=
        ⟨payload, l, snap.clockStarted, weights, none⟩
      have hpicked : ReferenceCollectionSegmentExtraction.choice x = some picked := by
        unfold ReferenceCollectionSegmentExtraction.choice
        rw [hdispatch]
        simp [picked, weights, ReferenceCollectionSegmentExtraction.choiceOfCut,
          ReferenceActivePhysicalStep.DispatchCut.selection]
      have htail := ReferenceCollectionSegmentExtraction.choice_tail x picked hpicked
      have hactualStart :
          CoordinatorCollectionLedger.startRound l (x.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled l x.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
            .success l1 := by
        simpa [ReferenceContinuingCollectionRejectedFinishDomains.sourceRound] using hstart
      have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
        (ReferenceActivePhysicalStep.prepare x) payload l snap.clockStarted weights o l1
        hrecordingRun hactualStart
      have hrawRecorded :
          (ReferenceActivePhysicalStep.step x).coordinator.recording = some o := by
        change ((ReferenceActivePhysicalStep.prepare x).observeCoordinator).recording = some o
        rw [htail, hpost]
        exact ReferenceCollectionSegmentExtraction.collectionFinish_recording x payload
          snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare x) l1)
      have hrawDiagnostic :
          ReferenceCollectionRawBufferHistory.rawDiagnostic record =
            CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o := by
        simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, record.output_eq,
          x, hrawRecorded,
          CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
      have hl1Candidate : l1 = candidate := by
        simpa [candidate, hrawDiagnostic] using hstartCandidate
      have hfinishInput :
          (ReferenceCollectionSegmentExtraction.effectiveParse x l1 = none ∨
            ∃ M, ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M ∧
              CoordinatorCollectionLedger.acceptUpCheck l1 sender M = false) := by
        left
        simpa only [hl1Candidate] using hparse
      rcases hrejectedQuery hfinishInput with ⟨l2, bank, hreceiveRejected,
        hl2Rejected, hreceiveDomain, hreceiveCheck, hdiagnostic, f,
        hfinishSuccess, hfinishCandidate, hfinishIncrement, hfinishGamma,
        hfinishCursor, hfinishPhase, hfinishPending, hfinishAssignment,
        hfinishBase, hfinishCutoffRegisters, hfinishCurrentRegisters,
        hfinishRaw, hfinishEnabled, hfinishPairBound, hfinishRawBound,
        hfinishHistory, hfinishValid, clockFinished, hclockFinish,
        hclockRegisters, hclockPending, hclockCommand, hproposal,
        hcollectionFinish, hobserveCoordinator, hstepCoordinator,
        hstepNext, hstepBank, hstepActivations, hstepFollowers, hstepOwn,
        hnextReady, hterminalReady⟩
      have hstartStored : ∀ a,
          l1.increment a + l1.gammaLoc a ≤
            4 * rate.n * (min (l.cursor + 1) l.freezeAt - l.cutoff) := by
        intro a
        rw [hl1Candidate]
        exact hstage a
      have hFinishedSigma : f.sigma = l.sigma := by
        rw [hfinishCandidate]
        simp [CoordinatorCollectionLedger.finishRoundCandidate, hl2Rejected,
          hstartSigma]
      have hFinishedCutoff : f.cutoff = l.cutoff := by
        rw [hfinishCandidate]
        simp [CoordinatorCollectionLedger.finishRoundCandidate, hl2Rejected,
          hstartCutoff]
      have hFinishedFreeze : f.freezeAt = l.freezeAt := by
        rw [hfinishCandidate]
        simp [CoordinatorCollectionLedger.finishRoundCandidate, hl2Rejected,
          hstartFreeze]
      have hFinishedCursor : f.cursor = l.cursor + 1 := by
        rw [hfinishCursor]
        have hcursor' : l.cursor =
            ReferenceContinuingCollectionRejectedFinishDomains.sourceRound x.time := by
          simpa [ReferenceContinuingCollectionRejectedFinishDomains.sourceRound,
            record, x] using hcursor
        rw [hcursor']
      have houtput : record.output.next.coordinator = .collection payload f saved := by
        rw [record.output_eq, hstepNext, hproposal]
      have hNoAcceptedMap :
          ((ReferenceCollectionSegmentExtraction.effectiveParse x candidate = none) ∨
            ∃ M : OrdinaryMessageCodec.UpRecord
              (CoordinatorCollectionLedger.codecParams p rate.eta.val),
              ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M ∧
              CoordinatorCollectionLedger.acceptUpCheck candidate sender M = false) →
            f.cutoffRegisters = l.cutoffRegisters := by
        intro _
        exact hfinishCutoffRegisters
      have hAcceptedMap :
          ∀ M : OrdinaryMessageCodec.UpRecord
              (CoordinatorCollectionLedger.codecParams p rate.eta.val),
            ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M →
            CoordinatorCollectionLedger.acceptUpCheck candidate sender M = true →
              f.cutoffRegisters (l.assignment.arm sender) =
                some ⟨M.val.S, M.val.q, M.val.delta⟩ ∧
              (∀ b, b ≠ l.assignment.arm sender →
                f.cutoffRegisters b = l.cutoffRegisters b) := by
        intro M hMparse hMaccept
        rw [hparse] at hMparse
        cases hMparse
      refine ⟨f, houtput, hFinishedSigma, hFinishedCursor,
        hFinishedCutoff, hFinishedFreeze, hfinishAssignment, hfinishBase,
        hNoAcceptedMap, hAcceptedMap, ?_, ?_⟩
      · intro a c hc
        rw [hfinishCutoffRegisters] at hc
        exact hCut a c hc
      · intro a
        rw [hfinishIncrement]
        rw [← hstartIncrement]
        simpa [hFinishedCursor, hFinishedFreeze, hFinishedCutoff] using hstartStored a

  | some M =>
      by_cases haccept : CoordinatorCollectionLedger.acceptUpCheck candidate sender M = true
      · have hAcceptedApi :=
          ReferenceContinuingCollectionAcceptedFinishDomains.continuing_collection_accepted_finish_domains
            x payload l saved hReadyForFinish
        rcases hAcceptedApi with ⟨cutoff, hcutoff, core, snap, hclockBound,
          hscores, hdispatch, harm, hlocal, hrecordInputs, o, l1,
          hrecordingRun, hstart, hstartCandidate, hstartValid, hstartPhase,
          hstartCursor, hstartSigma, hstartCutoff, hstartFreeze,
          hstartPending, hstartAssignment, hstartBase, hstartCutoffRegisters,
          hstartIncrement, hstartRegisters, hobserve, hrecording, hup,
          hreceiveDomain, hreceiveCheck, hbankInput, hacceptedMessages⟩
        have hrawRecorded : (ReferenceActivePhysicalStep.step x).coordinator.recording =
            some o := by
          simpa [ReferenceActivePhysicalStep.step] using hrecording
        have hrawDiagnostic :
            ReferenceCollectionRawBufferHistory.rawDiagnostic record =
              CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o := by
          simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, record.output_eq,
          x, hrawRecorded,
          CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
        have hl1Candidate : l1 = candidate := by
          simpa [candidate, hrawDiagnostic] using hstartCandidate
        have hparseL1 :
            ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M := by
          simpa only [hl1Candidate] using hparse
        have hacceptL1 : CoordinatorCollectionLedger.acceptUpCheck l1 sender M = true := by
          simpa only [hl1Candidate] using haccept
        let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x payload l
            (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
          snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
        let picked : ReferenceCollectionSegmentExtraction.Choice rate :=
          ⟨payload, l, snap.clockStarted, weights, none⟩
        have hpicked : ReferenceCollectionSegmentExtraction.choice x = some picked := by
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [hdispatch]
          simp [picked, weights, ReferenceCollectionSegmentExtraction.choiceOfCut,
            ReferenceActivePhysicalStep.DispatchCut.selection]
        have hparsePicked :
            ReferenceCollectionSegmentExtraction.effectiveParse x
              (CoordinatorCollectionLedger.startRoundCandidate picked.preLedger x.time
                (ReferenceActivePhysicalStep.collectionEnabled picked.preLedger x.time)
                (ReferenceCollectionRawBufferHistory.rawDiagnostic record)) = some M := by
          simpa [picked, candidate] using hparse
        have hacceptPicked :
            CoordinatorCollectionLedger.acceptUpCheck
              (CoordinatorCollectionLedger.startRoundCandidate picked.preLedger x.time
                (ReferenceActivePhysicalStep.collectionEnabled picked.preLedger x.time)
                (ReferenceCollectionRawBufferHistory.rawDiagnostic record)) sender M = true := by
          simpa [picked, candidate] using haccept
        have hbudgetRoot :=
          ReferenceFirstCollectionParsedUpBudgets.actual_first_collection_parsed_up_budget_calendar_replay_join
            rate source rewards C_star C_h count hcross hspan hshort
        have hbudgetChoice := hbudgetRoot n picked hpicked
        have hbudgetMessage := hbudgetChoice M hparsePicked hacceptPicked
        rcases hbudgetMessage with ⟨P0, birth, state, memory, offered, j, message,
          _hInit, _hSigma, _hCutoff, _hAssignment, _hValid, _hPending,
          _hCurrentUnknown, _hCutoffUnknown, _hLplusSigma, _hLplusCutoff,
          _hP0Sigma, _hP0Queues, _hBirthMember, _hBirthInstallation,
          _hBirthTime, _hConfiguration, _hCheckedOffer, hOffered, _hOfferWord,
          _hLastDown, _hJBound, _hJDisjunction, _hRetainedDown, _hMessageDown,
          _hMessageSigma, _hMessageQ, _hMSigma, hMessageScore, hMessageQueue,
          hMessageDelta, hReplayFacts, hJointBudget, hScoreBudget, hDeltaBudget,
          _hCapacity, _hLongerBound, _hPrefixIndices, _hPrefixLength,
          _hPrefixReplay, _hPrefixRows, _hLongerIndices, _hLongerLength,
          _hLongerReplay, _hCandidateRows⟩
        have hparsedActualOffer :
            ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some offered := by
          rw [hOffered]
          exact hparse
        have hparseL1Offer :
            ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some offered := by
          simpa only [hl1Candidate] using hparsedActualOffer
        have hparseL1Actual :
            ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M := by
          rw [hOffered] at hparseL1Offer
          exact hparseL1Offer
        have hJointBudgetFinish :
            M.val.S + M.val.q ≤ (l.cutoff - l.sigma) * ConstructorDimensions.D p := by
          simpa [picked, CoordinatorCollectionLedger.startRoundCandidate] using hJointBudget
        have hScoreBudgetFinish :
            M.val.S ≤ 4 * rate.n * (l.cutoff - l.sigma) := by
          simpa [picked, CoordinatorCollectionLedger.startRoundCandidate] using hScoreBudget
        have hAcceptedResult := hacceptedMessages M hparseL1Actual hacceptL1
          hJointBudgetFinish hScoreBudgetFinish
        rcases hAcceptedResult with ⟨past, currentRecord,
          hselectedUnknown, hselectedCutoffUnknown, hpastReplay, hcurrentReplay,
          hpastRows, hcurrentRow, hrecordsLength, hrecordAmounts, hcapacity,
          hReplayPrefix, henabledAtIndex, hReplayDomains, hReplayTotal,
          l2, bank, hl2Candidate, hl2Valid, hdecode, hreceive, hbankEq,
          hencoded, hdecodedMessage, hdiagnostic,
          hl2Phase, hl2Pending, hl2Sigma, hl2Cutoff, hl2Cursor, hl2Freeze,
          hl2Assignment, hl2Base, hl2CutoffSelected, hl2CurrentSelected,
          hl2IncrementSelected, hl2GammaSelected, hl2GammaFrame, hl2RawSelected,
          hl2Other, hl2Registers, hl2PendingZero, hl2CutoffMass, hl2PairBound,
          hl2RawBound, hl2EnabledHistory, hbankWellFormed, hbankPendingLength,
          hbankPendingEmpty, hcompletedBatch, hbankTransition, hbankOther,
          hbankPendingOutside, f, hfinishSuccess, hfinishCandidate, hfinishValid,
          hfinishIncrement, hfinishGamma, hfinishCursor, hfinishPhase,
          hfinishPending, hfinishSigma, hfinishCutoff, hfinishFreeze,
          hfinishAssignment, hfinishBase, hfinishCutoffRegisters,
          hfinishCurrentRegisters, hfinishRaw, hfinishEnabled,
          hfinishSelectedIncrement, hfinishOtherIncrement, hfinishGammaZero,
          hfinishRegisters, hfinishCutoffMass, hfinishPairBound,
          hfinishRawBound, hfinishEnabledHistory, hclockFinish,
          hclockRegisters, hclockPending, hclockCommand, hproposal,
          hcollectionFinish, hobserveFinish, hstepCoordinator, hstepNext,
          hstepBank, hstepActivations, hstepFollowers, hstepOwn, _⟩
        let records := past ++ [currentRecord]
        let oldSigma := l.sigma
        let oldCutoff := l.cutoff
        let oldFreeze := l.freezeAt
        let capacity := 4 * rate.n
        have hrawRecorded : (ReferenceActivePhysicalStep.step x).coordinator.recording =
            some o := by
          simpa [ReferenceActivePhysicalStep.step,
            ReferenceActivePhysicalStep.prepare, hdispatch] using hrecording
        have hrawDiagnostic :
            ReferenceCollectionRawBufferHistory.rawDiagnostic record =
              CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o := by
          simp [ReferenceCollectionRawBufferHistory.rawDiagnostic,
            record.output_eq, x, hrawRecorded,
            CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
        have hstartCandidateEq : l1 = candidate := by
          simpa [candidate, hrawDiagnostic] using hstartCandidate
        have hstartStored : ∀ a,
            l1.increment a + l1.gammaLoc a ≤
              4 * rate.n * (min (l.cursor + 1) l.freezeAt - l.cutoff) := by
          intro a
          rw [hstartCandidateEq]
          exact hstage a
        have hselectedArmEq :
            l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x) =
              l.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex x) := by
          rw [hstartAssignment]
        have hfinishSelectedCutoff :
            l2.cutoffRegisters (l.assignment.arm sender) =
              some ⟨M.val.S, M.val.q, M.val.delta⟩ := by
          simpa only [sender, hselectedArmEq] using hl2CutoffSelected
        have hselectedIncrementEq :
            f.increment (l.assignment.arm sender) =
              (QueueReplay.replay capacity (0, M.val.q) records).1 := by
          simpa only [sender, hselectedArmEq, capacity, records] using hfinishSelectedIncrement
        have hselectedDeltaLeScore : M.val.delta ≤ M.val.S := by
          rw [hMessageDelta, hMessageScore]
          exact Nat.sub_le _ _
        have hselectedDeltaCap : M.val.delta ≤ 4 * rate.n := hDeltaBudget
        have hfullPrefix := hReplayPrefix records.length (Nat.le_refl _)
        dsimp only at hfullPrefix
        have hprefixLength : records.length =
            (x.time.val + 1 - l.cutoff) + 1 := by
          simpa only [oldCutoff] using hrecordsLength
        have hspanRewrite :
            min (oldCutoff + records.length) oldFreeze - oldCutoff =
              min (l.cursor + 1) oldFreeze - oldCutoff := by
          have hjoin : oldCutoff + records.length = l.cursor + 1 := by
            rw [hprefixLength]
            have hcur : l.cursor = x.time.val + 1 := hcursor
            omega
          rw [hjoin]
        have hReplayStored :
            (QueueReplay.replay capacity (0, M.val.q) records).1 ≤
              capacity * (min (l.cursor + 1) oldFreeze - oldCutoff) := by
          have hbound := hfullPrefix.2.1
          have htake : List.take records.length (past ++ [currentRecord]) = records := by
            simp [records]
          rw [htake] at hbound
          simpa [oldCutoff, oldFreeze, capacity, hspanRewrite] using hbound
        have hfinishedCutoffMap :
            f.cutoffRegisters (l.assignment.arm sender) =
              some ⟨M.val.S, M.val.q, M.val.delta⟩ := by
          rw [hfinishCutoffRegisters, hfinishSelectedCutoff]
        have hfinishedCutoffMapOther : ∀ b,
            b ≠ l.assignment.arm sender →
              f.cutoffRegisters b = l.cutoffRegisters b := by
          intro b hb
          have hb' : b ≠ l1.assignment.arm sender := by
            simpa only [sender, hselectedArmEq] using hb
          calc
            f.cutoffRegisters b = l2.cutoffRegisters b := by
              rw [hfinishCutoffRegisters]
            _ = l1.cutoffRegisters b := (hl2Other b hb').2.1
            _ = l.cutoffRegisters b := by rw [hstartCutoffRegisters]
        have hfinishedCutoff : f.cutoff = l.cutoff := hfinishCutoff
        have hfinishedFreeze : f.freezeAt = l.freezeAt := hfinishFreeze
        have hfinishedSigma : f.sigma = l.sigma := hfinishSigma
        have hfinishedCursor : f.cursor = l.cursor + 1 := by
          rw [hfinishCursor]
          have hcursor' : l.cursor =
              ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound x.time := by
            simpa [ReferenceContinuingCollectionAcceptedFinishDomains.sourceRound,
              record, x] using hcursor
          rw [hcursor']
        have houtput : record.output.next.coordinator = .collection payload f saved := by
          rw [record.output_eq, hstepNext, hproposal]
        have hNoAcceptedMap :
            ((ReferenceCollectionSegmentExtraction.effectiveParse x candidate = none) ∨
              ∃ M' : OrdinaryMessageCodec.UpRecord
                (CoordinatorCollectionLedger.codecParams p rate.eta.val),
                ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M' ∧
                CoordinatorCollectionLedger.acceptUpCheck candidate sender M' = false) →
              f.cutoffRegisters = l.cutoffRegisters := by
          intro hnotAccepted
          rcases hnotAccepted with hnone | ⟨M', hMparse, hMreject⟩
          · rw [hparse] at hnone
            cases hnone
          · have hSameMessage : M' = M :=
              Option.some.inj (hMparse.symm.trans hparse)
            subst M'
            rw [haccept] at hMreject
            cases hMreject
        have hAcceptedMap :
            ∀ M' : OrdinaryMessageCodec.UpRecord
                (CoordinatorCollectionLedger.codecParams p rate.eta.val),
              ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M' →
              CoordinatorCollectionLedger.acceptUpCheck candidate sender M' = true →
                f.cutoffRegisters (l.assignment.arm sender) =
                  some ⟨M'.val.S, M'.val.q, M'.val.delta⟩ ∧
                (∀ b, b ≠ l.assignment.arm sender →
                  f.cutoffRegisters b = l.cutoffRegisters b) := by
          intro M' hMparse hMaccept
          have hSameMessage : M' = M :=
            Option.some.inj (hMparse.symm.trans hparse)
          subst M'
          constructor
          · exact hfinishedCutoffMap
          · exact hfinishedCutoffMapOther
        have hCutResult : ∀ a c, f.cutoffRegisters a = some c →
            c.lastService ≤ c.score ∧ c.lastService ≤ 4 * rate.n := by
          intro a c hregister
          by_cases ha : a = l.assignment.arm sender
          · subst a
            rw [hfinishedCutoffMap] at hregister
            have hc := Option.some.inj hregister
            cases hc
            exact ⟨hselectedDeltaLeScore, hselectedDeltaCap⟩
          · rw [hfinishedCutoffMapOther a ha] at hregister
            exact hCut a c hregister
        have hIncResult : ∀ a, f.increment a ≤
            4 * rate.n * (min f.cursor f.freezeAt - f.cutoff) := by
          intro a
          by_cases ha : a = l.assignment.arm sender
          · subst a
            rw [hselectedIncrementEq]
            simpa [hfinishedCursor, hfinishedFreeze, hfinishedCutoff,
              capacity, oldCutoff, oldFreeze] using hReplayStored
          · have ha' : a ≠ l1.assignment.arm sender := by
              simpa only [sender, hselectedArmEq] using ha
            calc
              f.increment a = l1.increment a + l1.gammaLoc a :=
                hfinishOtherIncrement a ha'
              _ ≤ 4 * rate.n * (min (l.cursor + 1) l.freezeAt - l.cutoff) :=
                hstartStored a
              _ = 4 * rate.n * (min f.cursor f.freezeAt - f.cutoff) := by
                rw [hfinishedCursor, hfinishedFreeze, hfinishedCutoff]
        refine ⟨f, houtput, hfinishedSigma, hfinishedCursor,
          hfinishedCutoff, hfinishedFreeze, hfinishAssignment, hfinishBase,
          hNoAcceptedMap, hAcceptedMap, hCutResult, hIncResult⟩
      · have hRejectedApi :=
          ReferenceContinuingCollectionRejectedFinishDomains.continuing_collection_rejected_finish_domains
            x payload l saved hReadyForFinish
        rcases hRejectedApi with ⟨cutoff, hcutoff, core, snap, hclockBound,
          hscores, hdispatch, harm, hlocal, hrecordInputs, o, l1,
          hrecordingRun, hstart, hstartCandidate, hstartValid, hstartPhase,
          hstartCursor, hstartSigma, hstartCutoff, hstartFreeze,
          hstartPending, hstartAssignment, hstartBase, hstartCutoffRegisters,
          hstartIncrement, hstartRegisters, hstartPairedMass, hstartCurrentBounds,
          hstartCutoffBounds, hstartPendingZero, hstartServiceBounds,
          hstartRawBounds, hstartEnabledHistory, hrejectedQuery⟩
        let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights
          (ReferenceActivePhysicalStep.collectionInput x payload l
            (ReferenceActivePhysicalStep.collectionClock payload l saved cutoff) cutoff)
          snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
        let picked : ReferenceCollectionSegmentExtraction.Choice rate :=
          ⟨payload, l, snap.clockStarted, weights, none⟩
        have hpicked : ReferenceCollectionSegmentExtraction.choice x = some picked := by
          unfold ReferenceCollectionSegmentExtraction.choice
          rw [hdispatch]
          simp [picked, weights, ReferenceCollectionSegmentExtraction.choiceOfCut,
            ReferenceActivePhysicalStep.DispatchCut.selection]
        have htail := ReferenceCollectionSegmentExtraction.choice_tail x picked hpicked
        have hactualStart :
            CoordinatorCollectionLedger.startRound l (x.time.val + 1)
              (ReferenceActivePhysicalStep.collectionEnabled l x.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
              .success l1 := by
          simpa [ReferenceContinuingCollectionRejectedFinishDomains.sourceRound] using hstart
        have hpost := ReferenceActivePhysicalStep.collectionPostChoice_after_start
          (ReferenceActivePhysicalStep.prepare x) payload l snap.clockStarted weights o l1
          hrecordingRun hactualStart
        have hrawRecorded :
            (ReferenceActivePhysicalStep.step x).coordinator.recording = some o := by
          change ((ReferenceActivePhysicalStep.prepare x).observeCoordinator).recording = some o
          rw [htail, hpost]
          exact ReferenceCollectionSegmentExtraction.collectionFinish_recording x payload
            snap.clockStarted o (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) l1)
        have hrawDiagnostic :
            ReferenceCollectionRawBufferHistory.rawDiagnostic record =
              CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o := by
          simp [ReferenceCollectionRawBufferHistory.rawDiagnostic, record.output_eq,
            x, hrawRecorded,
            CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder]
        have hl1Candidate : l1 = candidate := by
          simpa [candidate, hrawDiagnostic] using hstartCandidate
        have hfinishInput :
            (ReferenceCollectionSegmentExtraction.effectiveParse x l1 = none ∨
              ∃ M', ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M' ∧
                CoordinatorCollectionLedger.acceptUpCheck l1 sender M' = false) := by
          right
          refine ⟨M, ?_, ?_⟩
          · simpa only [hl1Candidate] using hparse
          · have hacceptFalse :
                CoordinatorCollectionLedger.acceptUpCheck candidate sender M = false := by
              exact Bool.eq_false_iff.mpr haccept
            simpa only [hl1Candidate] using hacceptFalse
        rcases hrejectedQuery hfinishInput with ⟨l2, bank, hreceiveRejected,
          hl2Rejected, hreceiveDomain, hreceiveCheck, hdiagnostic, f,
          hfinishSuccess, hfinishCandidate, hfinishIncrement, hfinishGamma,
          hfinishCursor, hfinishPhase, hfinishPending, hfinishAssignment,
          hfinishBase, hfinishCutoffRegisters, hfinishCurrentRegisters,
          hfinishRaw, hfinishEnabled, hfinishPairBound, hfinishRawBound,
          hfinishHistory, hfinishValid, clockFinished, hclockFinish,
          hclockRegisters, hclockPending, hclockCommand, hproposal,
          hcollectionFinish, hobserveCoordinator, hstepCoordinator,
          hstepNext, hstepBank, hstepActivations, hstepFollowers, hstepOwn,
          hnextReady, hterminalReady⟩
        have hstartStored : ∀ a,
            l1.increment a + l1.gammaLoc a ≤
              4 * rate.n * (min (l.cursor + 1) l.freezeAt - l.cutoff) := by
          intro a
          rw [hl1Candidate]
          exact hstage a
        have hFinishedSigma : f.sigma = l.sigma := by
          rw [hfinishCandidate]
          simp [CoordinatorCollectionLedger.finishRoundCandidate, hl2Rejected,
            hstartSigma]
        have hFinishedCutoff : f.cutoff = l.cutoff := by
          rw [hfinishCandidate]
          simp [CoordinatorCollectionLedger.finishRoundCandidate, hl2Rejected,
            hstartCutoff]
        have hFinishedFreeze : f.freezeAt = l.freezeAt := by
          rw [hfinishCandidate]
          simp [CoordinatorCollectionLedger.finishRoundCandidate, hl2Rejected,
            hstartFreeze]
        have hFinishedCursor : f.cursor = l.cursor + 1 := by
          rw [hfinishCursor]
          have hcursor' : l.cursor =
              ReferenceContinuingCollectionRejectedFinishDomains.sourceRound x.time := by
            simpa [ReferenceContinuingCollectionRejectedFinishDomains.sourceRound,
              record, x] using hcursor
          rw [hcursor']
        have houtput : record.output.next.coordinator = .collection payload f saved := by
          rw [record.output_eq, hstepNext, hproposal]
        have hNoAcceptedMap :
            ((ReferenceCollectionSegmentExtraction.effectiveParse x candidate = none) ∨
              ∃ M' : OrdinaryMessageCodec.UpRecord
                (CoordinatorCollectionLedger.codecParams p rate.eta.val),
                ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M' ∧
                CoordinatorCollectionLedger.acceptUpCheck candidate sender M' = false) →
              f.cutoffRegisters = l.cutoffRegisters := by
          intro _
          exact hfinishCutoffRegisters
        have hAcceptedMap :
            ∀ M' : OrdinaryMessageCodec.UpRecord
                (CoordinatorCollectionLedger.codecParams p rate.eta.val),
              ReferenceCollectionSegmentExtraction.effectiveParse x candidate = some M' →
              CoordinatorCollectionLedger.acceptUpCheck candidate sender M' = true →
                f.cutoffRegisters (l.assignment.arm sender) =
                  some ⟨M'.val.S, M'.val.q, M'.val.delta⟩ ∧
                (∀ b, b ≠ l.assignment.arm sender →
                  f.cutoffRegisters b = l.cutoffRegisters b) := by
          intro M' hMparse hMaccept
          rw [hparse] at hMparse
          cases hMparse
          exact False.elim (haccept hMaccept)
        refine ⟨f, houtput, hFinishedSigma, hFinishedCursor,
          hFinishedCutoff, hFinishedFreeze, hfinishAssignment, hfinishBase,
          hNoAcceptedMap, hAcceptedMap, ?_, ?_⟩
        · intro a c hc
          rw [hfinishCutoffRegisters] at hc
          exact hCut a c hc
        · intro a
          rw [hfinishIncrement]
          rw [← hstartIncrement]
          simpa [hFinishedCursor, hFinishedFreeze, hFinishedCutoff] using hstartStored a

end Bandits.Support.ReferenceFirstCollectionStoredServiceStep

end
