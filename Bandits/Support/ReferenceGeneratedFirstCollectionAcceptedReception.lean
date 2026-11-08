/-
Copyright (c) 2026 Bandits Lean formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceGeneratedFirstCollectionRejectedPrefix
public import Bandits.Support.ReferenceFirstCollectionParsedUpBudgets
public import Bandits.Support.ReferenceContinuingCollectionAcceptedDecodeDomains

import Lean.Elab.Tactic.Omega

/-!
# Actual first admissible first-collection UP reception

The original generated execution is followed through its rejected filtered
UP prefix. At the first locally admissible attempt this module identifies the
same physical round in the accepted collection window, obtains the sender and
calendar budgets from that original source, and proves the actual receiver
decode/replay step. It stops before collection FINISH. The next consumer is
`ReferenceGeneratedFirstCollectionAdmission`, which must compose the separately
accepted FINISH producer with the readiness, message, START and budgets
produced here.

Mathematical sources: `sources/zip4/manuscript/06_interruptions.tex:9-100,
164-177,246-295`, `sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support

namespace Bandits.Support.ReferenceGeneratedFirstCollectionAcceptedReception

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters} {rate : RateInput p}

private theorem takeWhile_getElem_of_forall_prefix {α : Type*}
    (pred : α → Bool) (xs : List α) :
    ∀ (i : ℕ) (hi : i < xs.length),
      (∀ j (_hj : j ≤ i) (hjlen : j < xs.length),
        pred (xs.get ⟨j, hjlen⟩) = true) →
      ∃ h : i < (xs.takeWhile pred).length,
        (xs.takeWhile pred)[i]'h = xs[i]'hi := by
  induction xs with
  | nil =>
      intro i hi _
      simp only [List.length_nil] at hi
      omega
  | cons head tail ih =>
      intro i hi hpred
      cases i with
      | zero =>
          have hhead := hpred 0 (by omega) (by omega)
          have hhead' : pred head = true := by simpa using hhead
          simp only [List.length_cons] at hi
          refine ⟨by simp [hhead'], ?_⟩
          simp [hhead']
      | succ i =>
          have hhead := hpred 0 (by omega) (by omega)
          have hhead' : pred head = true := by simpa using hhead
          have htail : ∀ j (hj : j ≤ i) (hjlen : j < tail.length),
              pred (tail.get ⟨j, hjlen⟩) = true := by
            intro j hj hjlen
            have h := hpred (j + 1) (by omega) (by omega)
            simpa using h
          have hiTail : i < tail.length := by simp only [List.length_cons] at hi; omega
          have hresult := ih i hiTail htail
          rcases hresult with ⟨hresult, heq⟩
          refine ⟨?_, ?_⟩
          · simpa [List.takeWhile_cons, hhead'] using Nat.succ_lt_succ hresult
          · simpa [List.takeWhile_cons, hhead'] using heq

theorem continuing_ready_calendar_bound
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload l saved) :
    l.cutoff - 1 + (x.time.val + 1 - l.cutoff) ≤ p.T := by
  rcases hReady with ⟨_, _, _, _, _, _, _, hcutT, _, _, _, hcursor, _hcutCursor, _⟩
  have hcutTime : l.cutoff ≤ x.time.val + 1 := by
    rw [← hcursor]
    omega
  omega

private theorem laterChosen_false_of_ready
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload l saved) :
    ReferenceCollectionPhaseHistory.laterChosen x = false := by
  have hStart := ReferenceContinuingCollectionStartDomains.continuing_collection_start_domains
    x payload l saved hReady
  rcases hStart with ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, _⟩
  simp [ReferenceCollectionPhaseHistory.laterChosen, hcoord]

private theorem collectionWindow_getElem_after_ready_prefix
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (w q : ℕ) (hcut : w < records.length)
    (hrecords : w + 1 + q < records.length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (saved : Option (Fin p.T × Bool))
    (hready : ∀ j (hj : j ≤ q),
      ∃ l : ReferenceActivePhysicalStep.Ledger rate,
        ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
          (records[w + 1 + j]'(by omega)).input payload l saved)
    :
    ∃ n : Fin (ReferenceCollectionPhaseHistory.collectionWindow records w).length,
      n.val = q + 1 ∧
      (ReferenceCollectionPhaseHistory.collectionWindow records w)[n.val] =
        records[w + 1 + q]'hrecords := by
  let xs := records.drop (w + 1)
  let pred := fun r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) =>
    !ReferenceCollectionPhaseHistory.laterChosen r.input
  have hq : q < xs.length := by
    simp only [xs, List.length_drop]
    omega
  have hprefix : ∀ j (hj : j ≤ q) (hjlen : j < xs.length),
      pred (xs.get ⟨j, hjlen⟩) = true := by
    intro j hj hjlen
    have hrecord : xs.get ⟨j, hjlen⟩ = records[w + 1 + j]'(by omega) := by
      simp [xs]
    rcases hready j hj with ⟨l, hReady⟩
    have hf := laterChosen_false_of_ready _ _ _ _ hReady
    rw [hrecord]
    simp [pred, hf]
  have htake := takeWhile_getElem_of_forall_prefix pred xs q hq hprefix
  rcases htake with ⟨hqTake, htake⟩
  have hwindow : ReferenceCollectionPhaseHistory.collectionWindow records w =
      records[w]'hcut :: xs.takeWhile pred := by
    unfold ReferenceCollectionPhaseHistory.collectionWindow
    rw [List.take_one_drop_eq_of_lt_length hcut]
    simp [xs, pred]
  have hlen : q + 1 <
      (ReferenceCollectionPhaseHistory.collectionWindow records w).length := by
    rw [hwindow]
    simp only [List.length_cons]
    omega
  let n : Fin (ReferenceCollectionPhaseHistory.collectionWindow records w).length :=
    ⟨q + 1, hlen⟩
  have htail : (xs.takeWhile pred)[q]'hqTake = records[w + 1 + q]'hrecords := by
    simpa [xs] using htake
  refine ⟨n, rfl, ?_⟩
  simpa only [hwindow, n, List.getElem_cons_succ] using htail

theorem actual_first_collection_run_eq_generated
    (rate : RateInput p) (source : SourceInput p)
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hspanActual :
      ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
        count ≤ p.T) :
    ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspanActual =
      ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s hsElapsed count hspan := by
  let initial := ReferenceFirstLaunchNumericalCell.launchState
    rate source rewards C_star C_h hcross
  have hinitial :
      ReferenceFirstCollectionEpochAlignment.actualLaunchState
          rate source rewards C_star C_h hcross = initial := by
    dsimp only [initial, ReferenceFirstCollectionEpochAlignment.actualLaunchState,
      ReferenceFirstLaunchNumericalCell.launchState]
  have hspan' := hspanActual
  change ReferenceActivePhysicalHorizon.run
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState
        rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      (ReferenceInitializationRun.elapsed p
        (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
      count hspan'
      (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
        rate source rewards C_star C_h hcross).1 = _
  cases hsElapsed
  simp only [ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun,
    ReferenceFirstCollectionEpochAlignment.actualLaunchState,
    ReferenceFirstLaunchNumericalCell.launchState]

/-- Focus the accepted decode theorem on the source consumer's actual START,
calendar replay, and receiver result. The two numerical inputs are explicit
here and are discharged by the parsed-budget join in the original-run proof.
-/
theorem accepted_reception_of_ready
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : record.input = x)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      x payload l saved)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (o : CoordinatorRecordingOperation.Output p)
    (l1 : ReferenceActivePhysicalStep.Ledger rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c)
    (hrecorded : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) c.payload c.started c.weights) = some o)
    (hstarted : CoordinatorCollectionLedger.startRound c.preLedger (x.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1) :
    ∃ cutoff : Fin p.T, cutoff.val + 1 = l.cutoff ∧
    let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
    let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
    ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
      (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
      (hb : snap.clockStarted.clock.g ≤ p.T + 1)
      (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck input = true),
    (ReferenceActivePhysicalStep.prepare x).coordinator =
      .collection payload l clock cutoff (.continuing core snap hb hs) ∧

      CoordinatorRecorderComplementBridge.run
        (ReferenceActivePhysicalStep.collectionRecordingInput
          (ReferenceActivePhysicalStep.prepare x) payload snap.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights input
            snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq)) = some o ∧
      CoordinatorCollectionLedger.startRound l (x.time.val + 1)
        (ReferenceActivePhysicalStep.collectionEnabled l x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 ∧
      l1 = CoordinatorCollectionLedger.startRoundCandidate l x.time
        (ReferenceActivePhysicalStep.collectionEnabled l x.time)
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) ∧
      l1.sigma = l.sigma ∧ l1.cutoff = l.cutoff ∧
      CoordinatorCollectionLedger.validLedgerCheck l1 = true ∧
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some o ∧
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up =
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) l1).diagnostic ∧
      CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o =
        ReferenceCollectionRawBufferHistory.rawDiagnostic record ∧
      let i := ReferenceActivePhysicalStep.upSenderIndex x
      let a := l1.assignment.arm i
      let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
        (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) l1) x.time
      CoordinatorUpReception.receptionInputDomain receptionInput ∧
      CoordinatorUpReception.receptionInputCheck receptionInput = true ∧
      receptionInput.upDecoderBank = x.state.upDecoderBank ∧
      ∀ (M' : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val)),
        ReferenceCollectionSegmentExtraction.effectiveParse x l1 = some M' →
        CoordinatorCollectionLedger.acceptUpCheck l1 i M' = true →
        M'.val.S + M'.val.q ≤ (l.cutoff - l.sigma) * ConstructorDimensions.D p →
        M'.val.S ≤ (4 * rate.n) * (l.cutoff - l.sigma) →
        ∃ past : List (Bool × ℕ),
        ∃ currentRecord : Bool × ℕ,
          l1.currentRegisters a = none ∧
          l1.cutoffRegisters a = none ∧
          CoordinatorCollectionLedger.replayRecords? l1 a
            (CoordinatorCollectionLedger.calendarIndices p.T (l.cutoff - 1)
              (x.time.val + 1 - l.cutoff)
              (continuing_ready_calendar_bound x payload l saved hReady)) = some past ∧
          CoordinatorCollectionLedger.replayRecords? l1 a [x.time] =
            some [currentRecord] ∧
          past = (CoordinatorCollectionLedger.calendarIndices p.T (l.cutoff - 1)
              (x.time.val + 1 - l.cutoff)
              (continuing_ready_calendar_bound x payload l saved hReady)).map (fun r =>
                (decide (ReferenceContinuingCollectionStartDomains.sourceRound r < l.freezeAt),
                  CoordinatorCollectionLedger.bufferedArrival l1 a r)) ∧
          currentRecord =
            (decide (ReferenceContinuingCollectionStartDomains.sourceRound x.time < l.freezeAt),
              CoordinatorCollectionLedger.bufferedArrival l1 a x.time) ∧
          let records := past ++ [currentRecord]
          records.length = (x.time.val + 1 - l.cutoff) + 1 ∧
          (∀ r, r ∈ records → r.2 ≤ ConstructorDimensions.D p) ∧
          (∀ h, h ≤ records.length →
            let Rh := QueueReplay.replay (4 * rate.n) (0, M'.val.q) (records.take h)
            M'.val.S + Rh.1 + Rh.2 ≤
              (l.cutoff - l.sigma + h) * ConstructorDimensions.D p ∧
            Rh.1 ≤ 4 * rate.n *
              (min (l.cutoff + h) l.freezeAt - l.cutoff) ∧
            (0 < h → Rh.1 -
              (QueueReplay.replay (4 * rate.n) (0, M'.val.q)
                (records.take (h - 1))).1 ≤ 4 * rate.n) ∧
            Rh.1 ≤ p.T * ConstructorDimensions.D p ∧
            Rh.2 ≤ p.T * ConstructorDimensions.D p) ∧
          (∀ j : Fin records.length,
            (records.get j).1 = decide (l.cutoff + j.val < l.freezeAt)) ∧
          CoordinatorCollectionLedger.replayOutputDomainsCheck (p := p) (4 * rate.n)
            M'.val.q records = true ∧
          M'.val.S + (QueueReplay.replay (4 * rate.n) (0, M'.val.q) records).1 ≤
            4 * rate.n * (min (x.time.val + 2) l.freezeAt - l.sigma) ∧
          ∃ l2 : ReferenceActivePhysicalStep.Ledger rate,
          ∃ bank : CoordinatorUpReception.UpDecoderBank p,
            l2 = CoordinatorCollectionLedger.acceptUpCandidate l1 i M' past currentRecord ∧
            CoordinatorCollectionLedger.validLedgerCheck l2 = true ∧
            CoordinatorCollectionLedger.decodeUp l1 i (some M') = .success l2 ∧
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) l1).result = .success (l2, bank) ∧
            bank = CoordinatorUpReception.decoderBankAfter receptionInput ∧
            (CoordinatorUpReception.decoderTransition receptionInput).2 =
              ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare x) ∧
            CoordinatorUpReception.parseDecoderOutput
              (CoordinatorUpReception.decoderTransition receptionInput).2 = some M' ∧
            (ReferenceActivePhysicalStep.receiveUp
              (ReferenceActivePhysicalStep.prepare x) l1).diagnostic =
              some {
                input := receptionInput
                expected := ReferenceActivePhysicalStep.upExpected
                  (ReferenceActivePhysicalStep.prepare x)
                decoderAfter := (CoordinatorUpReception.decoderTransition receptionInput).1
                raw := (CoordinatorUpReception.decoderTransition receptionInput).2
                parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
                locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
                rawMatches := decide ((CoordinatorUpReception.decoderTransition receptionInput).2 =
                  ReferenceActivePhysicalStep.upExpected
                    (ReferenceActivePhysicalStep.prepare x))
                wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
                  rate x.row (ReferenceActivePhysicalStep.upInputs
                    (ReferenceActivePhysicalStep.prepare x) l1) x.time
                  ((ReferenceActivePhysicalStep.prepare x).followers.followers i)
                  ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).1
                  ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.1
                  ((ReferenceActivePhysicalStep.prepare x).follower_alignment _).2.2.1 rfl } ∧
            l2.phase = .decoded ∧
            l2.pending = l.pending.erase i ∧
            l2.sigma = l.sigma ∧ l2.cutoff = l.cutoff ∧
            l2.assignment = l.assignment ∧ l2.baseScore = l.baseScore ∧
            l2.cutoffRegisters a = some ⟨M'.val.S, M'.val.q, M'.val.delta⟩ ∧
            l2.currentRegisters a = some ⟨
              (QueueReplay.replay (4 * rate.n) (0, M'.val.q) records).2,
              (QueueReplay.replay (4 * rate.n) (0, M'.val.q) records).1 -
                (QueueReplay.replay (4 * rate.n) (0, M'.val.q)
                  (records.take (records.length - 1))).1⟩ ∧
            l2.increment a = (QueueReplay.replay (4 * rate.n) (0, M'.val.q) records).1 ∧
            l2.gammaLoc a = 0 ∧
            (∀ b, l2.gammaLoc b = l1.gammaLoc b) ∧
            l2.rawBuffer a = (fun _ => none) ∧
            (∀ b, b ≠ a →
              l2.currentRegisters b = l1.currentRegisters b ∧
              l2.cutoffRegisters b = l1.cutoffRegisters b ∧
              l2.increment b = l1.increment b ∧ l2.rawBuffer b = l1.rawBuffer b) ∧
            (∀ b, (l2.currentRegisters b = none ↔
                CoordinatorCollectionLedger.armPending l2 b) ∧
              (l2.cutoffRegisters b = none ↔
                CoordinatorCollectionLedger.armPending l2 b)) ∧
            (∀ b, CoordinatorCollectionLedger.armPending l2 b →
              l2.increment b = 0 ∧ l2.gammaLoc b = 0) ∧
            (∀ b c, l2.cutoffRegisters b = some c →
              c.score + c.queue ≤ (l.cutoff - l.sigma) * ConstructorDimensions.D p) ∧
            (∀ b c q, l2.cutoffRegisters b = some c →
              l2.currentRegisters b = some q →
              c.score + l2.increment b + l2.gammaLoc b + q.queue ≤
                (x.time.val + 2 - l.sigma) * ConstructorDimensions.D p ∧
              c.score + l2.increment b + l2.gammaLoc b ≤
                4 * rate.n * (min (x.time.val + 2) l.freezeAt - l.sigma)) ∧
            (∀ r, l2.enabledHistory r =
              if l.cutoff ≤ ReferenceContinuingCollectionStartDomains.sourceRound r ∧
                  ReferenceContinuingCollectionStartDomains.sourceRound r ≤ x.time.val + 1 then
                some (decide
                  (ReferenceContinuingCollectionStartDomains.sourceRound r < l.freezeAt))
              else none) ∧
            CoordinatorUpReception.decoderBankWellFormed p bank ∧
            (x.state.upDecoderBank i).pending.length + 1 = AffineBatchDecoder.quota p ∧
            (bank i).pending = [] ∧
            (∃ batch, batch ∈ (bank i).completed ∧
              batch.length = AffineBatchDecoder.quota p) ∧
            (CoordinatorUpReception.decoderTransition receptionInput).1 =
              ⟨[], (x.state.upDecoderBank i).completed ++
                [(x.state.upDecoderBank i).pending ++
                  [AffineBatchDecoder.entry p
                    (CoordinatorUpReception.traceAt receptionInput) receptionInput.time]]⟩ ∧
            (∀ j, j ≠ i → bank j = x.state.upDecoderBank j) ∧
            (∀ j, j ∉ l2.pending → (bank j).pending = []) := by
  classical
  have hA :=
    ReferenceContinuingCollectionAcceptedDecodeDomains.continuing_collection_accepted_decode_domains
      x payload l saved hReady
  dsimp only at hA
  rcases hA with ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, _harm,
    _hlocal, _hrecordInputs, oA, l1A, hrecordA, hstartA, hcandA, hvalidA,
    _hphase, _hcursor, hsigmaA, hcutoffA, _hfreeze, _hpending,
    _hassignment, _hbase, _hcutoffRegisters, _hincrement, _hcurrentUpdate,
    _hstartMass, _hfreezeCurrent, _hrawNone, _hregisters, _hknownStart,
    _hcurrent, _hcutDomain, _hzero, _hgamma, _hcutMass, _hraw, _hhistory,
    _hrawBuffer, _hrawFrame, _hfresh, _hfuture, _hobserve, hrecordingA,
    hdiagnosticA, hreceiveDomainA, hreceiveCheckA, hbankInputA, hquery⟩
  let clock := ReferenceActivePhysicalStep.collectionClock payload l saved cutoff
  let input := ReferenceActivePhysicalStep.collectionInput x payload l clock cutoff
  let weights := CoordinatorCollectionInteractive.PreObservationInputs.weights input
    snap.inputsValid.ledger_valid snap.inputsValid.assignment_eq
  let expectedChoice : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨payload, l, snap.clockStarted, weights, none⟩
  let receptionInput := ReferenceUpReception.receptionInputAtRow rate x.row
    (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare x) l1) x.time
  have hchoiceExpected : ReferenceCollectionSegmentExtraction.choice x =
      some expectedChoice := by
    unfold ReferenceCollectionSegmentExtraction.choice
    rw [hcoord]
    simp [ReferenceCollectionSegmentExtraction.choiceOfCut,
      ReferenceActivePhysicalStep.DispatchCut.selection, expectedChoice, weights, input, clock]
  have hc : c = expectedChoice := Option.some.inj (hchoice.symm.trans hchoiceExpected)
  subst c
  have hrecordedSame : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare x) payload snap.clockStarted weights) = some o := by
    simpa [expectedChoice] using hrecorded
  have ho : o = oA := Option.some.inj (hrecordedSame.symm.trans hrecordA)
  have hstartedSame : CoordinatorCollectionLedger.startRound l
      (ReferenceContinuingCollectionStartDomains.sourceRound x.time)
      (ReferenceActivePhysicalStep.collectionEnabled l x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder oA) = .success l1 := by
    simpa [expectedChoice, ho,
      ReferenceContinuingCollectionStartDomains.sourceRound] using hstarted
  have hstartedOutput : CoordinatorCollectionLedger.startRound l
      (x.time.val + 1) (ReferenceActivePhysicalStep.collectionEnabled l x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1 := by
    simpa only [ReferenceContinuingCollectionStartDomains.sourceRound, ← ho] using hstartedSame
  have hl1 : l1 = l1A :=
    CoordinatorCollectionLedger.Checked.success.inj (hstartedSame.symm.trans hstartA)
  have hraw : CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o =
      ReferenceCollectionRawBufferHistory.rawDiagnostic record := by
    have hrecordingStepA : record.output.coordinator.recording = some oA := by
      subst x
      rw [record.output_eq]
      change (ReferenceActivePhysicalStep.prepare record.input).observeCoordinator.recording = some oA
      exact hrecordingA
    have hrecordingStep : record.output.coordinator.recording = some o := by
      simpa only [ho] using hrecordingStepA
    subst x
    simp [CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder,
      ReferenceCollectionRawBufferHistory.rawDiagnostic, hrecordingStep]
  have hcandidate : l1 = CoordinatorCollectionLedger.startRoundCandidate l x.time
      (ReferenceActivePhysicalStep.collectionEnabled l x.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) := by
    calc
      l1 = l1A := hl1
      _ = CoordinatorCollectionLedger.startRoundCandidate l x.time
          (ReferenceActivePhysicalStep.collectionEnabled l x.time)
          (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder oA) := hcandA
      _ = _ := by rw [ho]
  have hvalid : CoordinatorCollectionLedger.validLedgerCheck l1 = true := by
    simpa only [hl1] using hvalidA
  have hsigmaStarted : l1.sigma = l.sigma := by simpa only [hl1] using hsigmaA
  have hcutoffStarted : l1.cutoff = l.cutoff := by simpa only [hl1] using hcutoffA
  have hrecordingOutput :
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.recording = some o := by
    simpa only [ho] using hrecordingA
  have hdiagnosticOutput :
      (ReferenceActivePhysicalStep.prepare x).observeCoordinator.up =
        (ReferenceActivePhysicalStep.receiveUp
          (ReferenceActivePhysicalStep.prepare x) l1).diagnostic := by
    simpa only [hl1] using hdiagnosticA
  have hreceiveDomain : CoordinatorUpReception.receptionInputDomain receptionInput := by
    simpa only [← hl1] using hreceiveDomainA
  have hreceiveCheck : CoordinatorUpReception.receptionInputCheck receptionInput = true := by
    simpa only [← hl1] using hreceiveCheckA
  have hbankInput : receptionInput.upDecoderBank = x.state.upDecoderBank := by
    simpa only [← hl1] using hbankInputA
  refine ⟨cutoff, hcutoff, ?_⟩
  dsimp only
  refine ⟨core, snap, hb, hs, hcoord, ?_⟩
  refine ⟨hrecordedSame, hstartedOutput, hcandidate, hsigmaStarted,
    hcutoffStarted, hvalid,
    hrecordingOutput, hdiagnosticOutput, hraw, hreceiveDomain,
    hreceiveCheck, hbankInput, ?_⟩
  · intro M' hparse' haccept' hjoint' hscore'
    have hparseA : ReferenceCollectionSegmentExtraction.effectiveParse x l1A = some M' := by
      simpa only [hl1] using hparse'
    have hacceptA : CoordinatorCollectionLedger.acceptUpCheck l1A
        (ReferenceActivePhysicalStep.upSenderIndex x) M' = true := by
      simpa only [hl1] using haccept'
    have hresultA := hquery M' hparseA hacceptA hjoint' hscore'
    have hresult := by
      simpa only [← hl1] using hresultA
    rcases hresult with ⟨past, currentRecord, hcurrentNone, hcutoffNone, hpast,
      hcurrent, hpastMap, hcurrentMap, hlength, harrivals, _hcapacity, hprefix,
      hcalendar, hdomains, hscoreReplay, l2, bank, hcand2, hvalid2,
      hdecode2, hreceive2, hbank2, hrawExpected, hparsed, hdiagnostic2,
      hphase2, hpending2, hsigma2, hcutoff2, _hcursor2, _hfreeze2,
      hassignment2, hbase2, hcutRegs2, hcurrentRegs2, hincrement2,
      hgamma2, hgammaAll, hrawCleared, hframed, hregisterDomains,
      hpendingZeros, hcutBudgets, hjointBudgets, _hrawDomains,
      henabledHistory, hbankWellFormed, hquota, hcompleted,
      hbankTransition, hbankFrame, hbankPending⟩

    have hprefixOut : ∀ h, h ≤ (past ++ [currentRecord]).length →
        let Rh := QueueReplay.replay (4 * rate.n) (0, M'.val.q)
          ((past ++ [currentRecord]).take h)
        M'.val.S + Rh.1 + Rh.2 ≤ (l.cutoff - l.sigma + h) *
            ConstructorDimensions.D p ∧
          Rh.1 ≤ 4 * rate.n * (min (l.cutoff + h) l.freezeAt - l.cutoff) ∧
          (0 < h → Rh.1 -
            (QueueReplay.replay (4 * rate.n) (0, M'.val.q)
              ((past ++ [currentRecord]).take (h - 1))).1 ≤ 4 * rate.n) ∧
          Rh.1 ≤ p.T * ConstructorDimensions.D p ∧
          Rh.2 ≤ p.T * ConstructorDimensions.D p := by
      intro h hh
      rcases hprefix h hh with ⟨hjointPrefix, hcapPrefix, hT1Prefix,
        hT2Prefix, hdeltaPrefix⟩
      exact ⟨hjointPrefix, hcapPrefix, hdeltaPrefix, hT1Prefix, hT2Prefix⟩
    refine ⟨past, currentRecord, hcurrentNone, hcutoffNone, hpast,
      hcurrent, hpastMap, hcurrentMap, hlength, harrivals, hprefixOut,
      hcalendar, hdomains, hscoreReplay, ?_⟩
    refine ⟨l2, bank, hcand2, hvalid2, hdecode2, hreceive2, hbank2,
      hrawExpected, hparsed, hdiagnostic2, hphase2, hpending2, hsigma2,
      hcutoff2, hassignment2, hbase2, hcutRegs2, hcurrentRegs2,
      hincrement2, hgamma2, hgammaAll, hrawCleared, hframed,
      hregisterDomains, hpendingZeros, hcutBudgets, hjointBudgets,
      henabledHistory, hbankWellFormed, hquota, hcompleted,
      hbankTransition, hbankFrame, hbankPending⟩

/-- The original-sender evidence selected by the parsed-UP budget/calendar
join. Values are retained only for this physical source record and sender. -/
structure ParsedUpSourceEvidence
    (records window : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val))
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (l1 : ReferenceActivePhysicalStep.Ledger rate) (start w n : ℕ) : Type where
  P0 : ReferenceActivePhysicalStep.Payload rate
  birth : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
  state : ReferencePrelaunchFollower.State p rate.eta
  memory : ActiveFollowerLifecycle.LocalMemory p
  offered : OrdinaryMessageCodec.UpRecord
    (CoordinatorCollectionLedger.codecParams p rate.eta.val)
  downIndex : Fin records.length
  message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord (p := p) (rate := rate)
  source_choice : ReferenceCollectionSegmentExtraction.choice record.input = some c
  source_parse : ReferenceCollectionSegmentExtraction.effectiveParse record.input
    (CoordinatorCollectionLedger.startRoundCandidate c.preLedger record.input.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic record)) = some M
  source_accepted : CoordinatorCollectionLedger.acceptUpCheck
    (CoordinatorCollectionLedger.startRoundCandidate c.preLedger record.input.time
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
      (ReferenceCollectionRawBufferHistory.rawDiagnostic record))
    (ReferenceActivePhysicalStep.upSenderIndex record.input) M = true
  started_candidate : l1 = CoordinatorCollectionLedger.startRoundCandidate c.preLedger
    record.input.time (ReferenceActivePhysicalStep.collectionEnabled c.preLedger record.input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic record)
  P0_sigma : P0.sigma.val = start
  P0_zeroQueues : ∀ a, P0.queues a = 0
  birth_mem : birth ∈ records
  birth_time : birth.input.time.val = start
  birth_installation : ReferenceAssignmentPayloadPersistence.InstallationBirth birth P0
  actual_choice_ordinary :
    (ReferenceFollowerFixedReply.actualChoice record
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).configuration =
        .ordinary state memory
  checked_offer : ActiveFollowerQueueOperation.checkedUpOffer rate.eta
    (ReferenceFollowerFixedReply.actualChoice record
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).follower
    (ReferenceFollowerFixedReply.actualChoice record
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).row
    (ReferenceFollowerFixedReply.actualChoice record
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).activation
    (ReferenceFollowerFixedReply.actualChoice record
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).time state = .offer offered
  offered_is_parsed : offered = M
  prior_down_index : downIndex.val < w + n
  early_or_late_down : downIndex.val < w ∨ w ≤ downIndex.val ∧ downIndex.val < w + n
  retained_down : ReferenceAcceptedUpFollowerHistory.RetainedDown
    records[downIndex.val] (ReferenceActivePhysicalStep.upSenderIndex record.input) message
  last_down : state.lastDown = some message
  message_is_P0_down : message = P0.downRecord
    (ReferenceActivePhysicalStep.upSenderIndex record.input)
  message_sigma : message.val.sigma = start + 1
  message_queue_zero : message.val.q = 0
  parsed_sigma : M.val.sigma = start + 1
  joint_budget : M.val.S + M.val.q ≤
    (ledger.cutoff - ledger.sigma) * ConstructorDimensions.D p
  score_budget : M.val.S ≤
    (4 * rate.n) * (ledger.cutoff - ledger.sigma)
  delta_budget : M.val.delta ≤ 4 * rate.n
  sender_capacity : 4 * rate.n ≤ ConstructorDimensions.D p
  inclusive_calendar_replay :
    ∃ hbound : (start + w + 1) - 1 + (n + 1) ≤ p.T,
      let indices := CoordinatorCollectionLedger.calendarIndices p.T
        ((start + w + 1) - 1) (n + 1) hbound
      let longer := window.take n ++ [record]
      let sequence := ReferenceFirstCollectionCalendarReplay.prefixDiagnosticSequence rate longer
      let rows := longer.map (fun r =>
        (decide (r.input.time.val + 1 < c.preLedger.freezeAt),
          if r.input.time.val + 1 < c.preLedger.freezeAt then
            CoordinatorCollectionLedger.explicitArrival sequence
              (c.preLedger.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input))
              r.input.time
          else 0))
      indices = longer.map (fun r => r.input.time) ∧
      CoordinatorCollectionLedger.replayRecords? l1
        (c.preLedger.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input))
        indices = some rows ∧
      (∀ row, row ∈ rows → row.2 ≤ ConstructorDimensions.D p)

/-- The real selected-arm replay and receiver transition produced from the
original pending bank and the current physical record. -/
structure AcceptedReceiverOutput
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      record.input payload ledger saved)
    (l1 : ReferenceActivePhysicalStep.Ledger rate)
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val)) : Type where
  past : List (Bool × ℕ)
  currentRecord : Bool × ℕ
  l2 : ReferenceActivePhysicalStep.Ledger rate
  bank : CoordinatorUpReception.UpDecoderBank p
  reception_input_domain : CoordinatorUpReception.receptionInputDomain
    (ReferenceUpReception.receptionInputAtRow rate record.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)
  reception_input_check : CoordinatorUpReception.receptionInputCheck
    (ReferenceUpReception.receptionInputAtRow rate record.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time) = true
  reception_bank_is_original :
    (ReferenceUpReception.receptionInputAtRow rate record.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time).upDecoderBank =
      record.input.state.upDecoderBank
  current_register_unknown :
    l1.currentRegisters (l1.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex record.input)) = none
  cutoff_register_unknown :
    l1.cutoffRegisters (l1.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex record.input)) = none
  past_replay :
    let a := l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)
    CoordinatorCollectionLedger.replayRecords? l1 a
      (CoordinatorCollectionLedger.calendarIndices p.T (ledger.cutoff - 1)
        (record.input.time.val + 1 - ledger.cutoff)
        (continuing_ready_calendar_bound record.input payload ledger saved hReady)) = some past
  current_replay :
    let a := l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)
    CoordinatorCollectionLedger.replayRecords? l1 a [record.input.time] = some [currentRecord]
  past_calendar_values :
    let a := l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)
    past = (CoordinatorCollectionLedger.calendarIndices p.T (ledger.cutoff - 1)
      (record.input.time.val + 1 - ledger.cutoff)
      (continuing_ready_calendar_bound record.input payload ledger saved hReady)).map
        (fun r =>
          (decide (ReferenceContinuingCollectionStartDomains.sourceRound r < ledger.freezeAt),
            CoordinatorCollectionLedger.bufferedArrival l1 a r))
  current_calendar_value :
    let a := l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)
    currentRecord =
      (decide
        (ReferenceContinuingCollectionStartDomains.sourceRound record.input.time < ledger.freezeAt),
        CoordinatorCollectionLedger.bufferedArrival l1 a record.input.time)
  replay_records_length :
    (past ++ [currentRecord]).length = (record.input.time.val + 1 - ledger.cutoff) + 1
  replay_row_bounds : ∀ r, r ∈ past ++ [currentRecord] → r.2 ≤ ConstructorDimensions.D p
  replay_prefix_bounds : ∀ h, h ≤ (past ++ [currentRecord]).length →
    let Rh := QueueReplay.replay (4 * rate.n) (0, M.val.q)
      ((past ++ [currentRecord]).take h)
    M.val.S + Rh.1 + Rh.2 ≤ (ledger.cutoff - ledger.sigma + h) *
        ConstructorDimensions.D p ∧
      Rh.1 ≤ 4 * rate.n * (min (ledger.cutoff + h) ledger.freezeAt - ledger.cutoff) ∧
      (0 < h → Rh.1 -
        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((past ++ [currentRecord]).take (h - 1))).1 ≤ 4 * rate.n) ∧
      Rh.1 ≤ p.T * ConstructorDimensions.D p ∧ Rh.2 ≤ p.T * ConstructorDimensions.D p
  replay_calendar_bits : ∀ j : Fin (past ++ [currentRecord]).length,
    ((past ++ [currentRecord]).get j).1 =
      decide (ledger.cutoff + j.val < ledger.freezeAt)
  replay_output_domains : CoordinatorCollectionLedger.replayOutputDomainsCheck
    (p := p) (4 * rate.n) M.val.q (past ++ [currentRecord]) = true
  replay_score_bound : M.val.S +
      (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])).1 ≤
    4 * rate.n *
      (min (record.input.time.val + 2) ledger.freezeAt - ledger.sigma)
  accepted_candidate :
    l2 = CoordinatorCollectionLedger.acceptUpCandidate l1
      (ReferenceActivePhysicalStep.upSenderIndex record.input) M past currentRecord
  accepted_valid : CoordinatorCollectionLedger.validLedgerCheck l2 = true
  decoded : CoordinatorCollectionLedger.decodeUp l1
      (ReferenceActivePhysicalStep.upSenderIndex record.input) (some M) = .success l2
  received : (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) l1).result = .success (l2, bank)
  bank_after_input : bank = CoordinatorUpReception.decoderBankAfter
    (ReferenceUpReception.receptionInputAtRow rate record.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)
  raw_is_expected :
    (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate record.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)).2 =
      ReferenceActivePhysicalStep.upExpected (ReferenceActivePhysicalStep.prepare record.input)
  parsed_message : CoordinatorUpReception.parseDecoderOutput
      (CoordinatorUpReception.decoderTransition
        (ReferenceUpReception.receptionInputAtRow rate record.input.row
          (ReferenceActivePhysicalStep.upInputs
            (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)).2 = some M
  diagnostic_present : ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) l1).diagnostic = some d ∧
    d.input = ReferenceUpReception.receptionInputAtRow rate record.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time ∧
    d.expected = ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare record.input) ∧
    d.decoderAfter = (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate record.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)).1 ∧
    d.raw = (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate record.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)).2 ∧
    d.parsed = some M ∧
    d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
    d.rawMatches = decide (d.raw = d.expected) ∧
    d.wrongUniqueAccepted = ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
      rate record.input.row
      (ReferenceActivePhysicalStep.upInputs (ReferenceActivePhysicalStep.prepare record.input) l1)
      record.input.time
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex record.input))
      ((ReferenceActivePhysicalStep.prepare record.input).follower_alignment _).1
      ((ReferenceActivePhysicalStep.prepare record.input).follower_alignment _).2.1
      ((ReferenceActivePhysicalStep.prepare record.input).follower_alignment _).2.2.1 rfl
  actual_output_up : record.output.coordinator.up =
    (ReferenceActivePhysicalStep.receiveUp
      (ReferenceActivePhysicalStep.prepare record.input) l1).diagnostic
  decoded_phase : l2.phase = .decoded
  pending_erased : l2.pending = ledger.pending.erase
    (ReferenceActivePhysicalStep.upSenderIndex record.input)
  sigma_preserved : l2.sigma = ledger.sigma
  cutoff_preserved : l2.cutoff = ledger.cutoff
  assignment_preserved : l2.assignment = ledger.assignment
  base_score_preserved : l2.baseScore = ledger.baseScore
  selected_cutoff_register :
    l2.cutoffRegisters (l1.assignment.arm
      (ReferenceActivePhysicalStep.upSenderIndex record.input)) =
        some ⟨M.val.S, M.val.q, M.val.delta⟩
  selected_current_register :
    let a := l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)
    l2.currentRegisters a = some ⟨
      (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])).2,
      (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])).1 -
        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((past ++ [currentRecord]).take ((past ++ [currentRecord]).length - 1))).1⟩
  selected_increment :
    l2.increment (l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)) =
      (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [currentRecord])).1
  selected_gamma_zero :
    l2.gammaLoc (l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)) = 0
  gamma_preserved : ∀ a, l2.gammaLoc a = l1.gammaLoc a
  selected_raw_cleared :
    l2.rawBuffer (l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input)) =
      (fun _ => none)
  other_columns_framed : ∀ a,
    a ≠ l1.assignment.arm (ReferenceActivePhysicalStep.upSenderIndex record.input) →
      l2.currentRegisters a = l1.currentRegisters a ∧
      l2.cutoffRegisters a = l1.cutoffRegisters a ∧
      l2.increment a = l1.increment a ∧ l2.rawBuffer a = l1.rawBuffer a
  register_domains : ∀ a,
    (l2.currentRegisters a = none ↔ CoordinatorCollectionLedger.armPending l2 a) ∧
    (l2.cutoffRegisters a = none ↔ CoordinatorCollectionLedger.armPending l2 a)
  pending_zeroes : ∀ a, CoordinatorCollectionLedger.armPending l2 a →
    l2.increment a = 0 ∧ l2.gammaLoc a = 0
  cutoff_budgets : ∀ a c, l2.cutoffRegisters a = some c →
    c.score + c.queue ≤ (ledger.cutoff - ledger.sigma) * ConstructorDimensions.D p
  current_budgets : ∀ a c q, l2.cutoffRegisters a = some c →
    l2.currentRegisters a = some q →
      c.score + l2.increment a + l2.gammaLoc a + q.queue ≤
        (record.input.time.val + 2 - ledger.sigma) * ConstructorDimensions.D p ∧
      c.score + l2.increment a + l2.gammaLoc a ≤
        4 * rate.n * (min (record.input.time.val + 2) ledger.freezeAt - ledger.sigma)
  enabled_history : ∀ r, l2.enabledHistory r =
    if ledger.cutoff ≤ ReferenceContinuingCollectionStartDomains.sourceRound r ∧
        ReferenceContinuingCollectionStartDomains.sourceRound r ≤ record.input.time.val + 1 then
      some (decide (ReferenceContinuingCollectionStartDomains.sourceRound r < ledger.freezeAt))
    else none
  bank_well_formed : CoordinatorUpReception.decoderBankWellFormed p bank
  quota_increment :
    (record.input.state.upDecoderBank
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).pending.length + 1 =
        AffineBatchDecoder.quota p
  selected_bank_pending_empty :
    (bank (ReferenceActivePhysicalStep.upSenderIndex record.input)).pending = []
  completed_batch_exists : ∃ batch,
    batch ∈ (bank (ReferenceActivePhysicalStep.upSenderIndex record.input)).completed ∧
      batch.length = AffineBatchDecoder.quota p
  completed_batch_append :
    (CoordinatorUpReception.decoderTransition
      (ReferenceUpReception.receptionInputAtRow rate record.input.row
        (ReferenceActivePhysicalStep.upInputs
          (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time)).1 =
    ⟨[], (record.input.state.upDecoderBank
      (ReferenceActivePhysicalStep.upSenderIndex record.input)).completed ++
      [(record.input.state.upDecoderBank
        (ReferenceActivePhysicalStep.upSenderIndex record.input)).pending ++
        [AffineBatchDecoder.entry p
          (CoordinatorUpReception.traceAt (ReferenceUpReception.receptionInputAtRow rate
            record.input.row (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time))
          record.input.time]]⟩
  selected_bank_completed_append :
    (bank (ReferenceActivePhysicalStep.upSenderIndex record.input)).completed =
      (record.input.state.upDecoderBank
        (ReferenceActivePhysicalStep.upSenderIndex record.input)).completed ++
      [(record.input.state.upDecoderBank
        (ReferenceActivePhysicalStep.upSenderIndex record.input)).pending ++
        [AffineBatchDecoder.entry p
          (CoordinatorUpReception.traceAt (ReferenceUpReception.receptionInputAtRow rate
            record.input.row (ReferenceActivePhysicalStep.upInputs
              (ReferenceActivePhysicalStep.prepare record.input) l1) record.input.time))
          record.input.time]]
  bank_other_senders_framed : ∀ j, j ≠ ReferenceActivePhysicalStep.upSenderIndex record.input →
    bank j = record.input.state.upDecoderBank j
  other_pending_empty : ∀ j, j ∉ l2.pending → (bank j).pending = []

/-- Package A's actual receive operation after the two explicit sender budgets.
No collection FINISH or physical successor is asserted. -/
private theorem accepted_receiver_output_of_ready
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReadyEnd : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      r.input payload ledger saved)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (o : CoordinatorRecordingOperation.Output p)
    (l1 : ReferenceActivePhysicalStep.Ledger rate)
    (hchoiceR : ReferenceCollectionSegmentExtraction.choice r.input = some c)
    (hrecordedR : CoordinatorRecorderComplementBridge.run
      (ReferenceActivePhysicalStep.collectionRecordingInput
        (ReferenceActivePhysicalStep.prepare r.input) c.payload c.started c.weights) = some o)
    (hstartedR : CoordinatorCollectionLedger.startRound c.preLedger
      (r.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) = .success l1)
    (M : OrdinaryMessageCodec.UpRecord
      (CoordinatorCollectionLedger.codecParams p rate.eta.val))
    (hparseR : ReferenceCollectionSegmentExtraction.effectiveParse r.input l1 = some M)
    (hacceptR : CoordinatorCollectionLedger.acceptUpCheck l1
      (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true)
    (hjoint : M.val.S + M.val.q ≤
      (ledger.cutoff - ledger.sigma) * ConstructorDimensions.D p)
    (hscore : M.val.S ≤ (4 * rate.n) * (ledger.cutoff - ledger.sigma)) :
    Nonempty (AcceptedReceiverOutput r payload ledger saved hReadyEnd l1 M) := by
  classical
  obtain ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord,
    _hrecord, _hstart, _hcandidate, _hsigma, _hcut, _hvalid,
    _hrecording, hdiagnosticOutput, _hraw, hreceiveDomain,
    hreceiveCheck, hbankInput, hreceiverQuery⟩ :=
      accepted_reception_of_ready r r.input rfl payload ledger saved hReadyEnd
        c o l1 hchoiceR hrecordedR hstartedR
  have hreceiverResult := hreceiverQuery M hparseR hacceptR
    hjoint hscore
  rcases hreceiverResult with ⟨past, currentRecord, hcurrentNone, hcutoffNone,
    hpast, hcurrent, hpastMap, hcurrentMap, hlength, harrivals, hprefix,
    hcalendar, hdomains, hscoreReplay, l2, bank, hcand2, hvalid2,
    hdecode2, hreceive2, hbank2, hrawExpected, hparsed, hdiagnostic2,
    hphase2, hpending2, hsigma2, hcutoff2, hassignment2, hbase2,
    hcutRegs2, hcurrentRegs2, hincrement2, hgamma2, hgammaAll,
    hrawCleared, hframed, hregisterDomains, hpendingZeros, hcutBudgets,
    hjointBudgets, henabledHistory, hbankWellFormed, hquota, hcompleted,
    hbankTransition, hbankFrame, hbankPending⟩
  have houtputUp : r.output.coordinator.up =
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) l1).diagnostic := by
    rw [r.output_eq]
    change (ReferenceActivePhysicalStep.prepare r.input).observeCoordinator.up = _
    exact hdiagnosticOutput
  let receptionInput := ReferenceUpReception.receptionInputAtRow rate r.input.row
    (ReferenceActivePhysicalStep.upInputs
      (ReferenceActivePhysicalStep.prepare r.input) l1) r.input.time
  let transition := CoordinatorUpReception.decoderTransition receptionInput
  let diagnostic : ReferenceActivePhysicalStep.UpDiagnostic p rate := {
    input := receptionInput
    expected := ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input)
    decoderAfter := transition.1
    raw := transition.2
    parsed := ReferenceUpReception.rawParsedOutput rate receptionInput
    locallyAccepted := ReferenceUpReception.rawParsedLocalAcceptance rate receptionInput
    rawMatches := decide (transition.2 = ReferenceActivePhysicalStep.upExpected
      (ReferenceActivePhysicalStep.prepare r.input))
    wrongUniqueAccepted := ReferenceUpReception.wrongUniqueAndLocalAcceptanceAtRow
      rate r.input.row
      (ReferenceActivePhysicalStep.upInputs
        (ReferenceActivePhysicalStep.prepare r.input) l1) r.input.time
      ((ReferenceActivePhysicalStep.prepare r.input).followers.followers
        (ReferenceActivePhysicalStep.upSenderIndex r.input))
      ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).1
      ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.1
      ((ReferenceActivePhysicalStep.prepare r.input).follower_alignment _).2.2.1 rfl }
  have hdiagnosticPresent : ∃ d : ReferenceActivePhysicalStep.UpDiagnostic p rate,
      (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) l1).diagnostic = some d ∧
      d.input = receptionInput ∧
      d.expected = ReferenceActivePhysicalStep.upExpected
        (ReferenceActivePhysicalStep.prepare r.input) ∧
      d.decoderAfter = transition.1 ∧ d.raw = transition.2 ∧ d.parsed = some M ∧
      d.locallyAccepted = ReferenceUpReception.rawParsedLocalAcceptance rate d.input ∧
      d.rawMatches = decide (d.raw = d.expected) ∧
      d.wrongUniqueAccepted = diagnostic.wrongUniqueAccepted := by
    have hdiag : (ReferenceActivePhysicalStep.receiveUp
        (ReferenceActivePhysicalStep.prepare r.input) l1).diagnostic = some diagnostic := by
      simpa [diagnostic, transition, receptionInput] using hdiagnostic2
    refine ⟨diagnostic, hdiag, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
    simpa only [diagnostic, ReferenceUpReception.rawParsedOutput, transition, receptionInput]
      using hparsed
  let receiver : AcceptedReceiverOutput r payload ledger saved hReadyEnd l1 M := {
    past := past
    currentRecord := currentRecord
    l2 := l2
    bank := bank
    reception_input_domain := hreceiveDomain
    reception_input_check := hreceiveCheck
    reception_bank_is_original := hbankInput
    current_register_unknown := hcurrentNone
    cutoff_register_unknown := hcutoffNone
    past_replay := hpast
    current_replay := hcurrent
    past_calendar_values := hpastMap
    current_calendar_value := hcurrentMap
    replay_records_length := hlength
    replay_row_bounds := harrivals
    replay_prefix_bounds := hprefix
    replay_calendar_bits := hcalendar
    replay_output_domains := hdomains
    replay_score_bound := hscoreReplay
    accepted_candidate := hcand2
    accepted_valid := hvalid2
    decoded := hdecode2
    received := hreceive2
    bank_after_input := hbank2
    raw_is_expected := hrawExpected
    parsed_message := hparsed
    diagnostic_present := hdiagnosticPresent
    actual_output_up := houtputUp
    decoded_phase := hphase2
    pending_erased := hpending2
    sigma_preserved := hsigma2
    cutoff_preserved := hcutoff2
    assignment_preserved := hassignment2
    base_score_preserved := hbase2
    selected_cutoff_register := hcutRegs2
    selected_current_register := hcurrentRegs2
    selected_increment := hincrement2
    selected_gamma_zero := hgamma2
    gamma_preserved := hgammaAll
    selected_raw_cleared := hrawCleared
    other_columns_framed := hframed
    register_domains := hregisterDomains
    pending_zeroes := hpendingZeros
    cutoff_budgets := hcutBudgets
    current_budgets := hjointBudgets
    enabled_history := henabledHistory
    bank_well_formed := hbankWellFormed
    quota_increment := hquota
    selected_bank_pending_empty := hcompleted
    completed_batch_exists := hbankTransition
    completed_batch_append := hbankFrame
    selected_bank_completed_append := by
      rw [hbank2]
      change (Function.update receptionInput.upDecoderBank
        (ReferenceActivePhysicalStep.upSenderIndex r.input)
        (CoordinatorUpReception.decoderTransition receptionInput).1
        (ReferenceActivePhysicalStep.upSenderIndex r.input)).completed = _
      rw [Function.update_self, hbankFrame]
      rfl
    bank_other_senders_framed := hbankPending.1
    other_pending_empty := hbankPending.2 }
  exact ⟨receiver⟩

/-- Consume P at the same original-run window record. All local matching,
parse, acceptance and START-frame inputs are explicit; the source endpoint
below produces them from R and A. -/
private theorem parsed_up_source_evidence_of_actual_record
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
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
    let start := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∀ (n : Fin B.length)
      (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (_hnrecordK : B[n.val] = r)
      (c : ReferenceCollectionSegmentExtraction.Choice rate)
      (ledger l1 : ReferenceActivePhysicalStep.Ledger rate)
      (_hcandidateR : l1 = CoordinatorCollectionLedger.startRoundCandidate c.preLedger
        r.input.time (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic r))
      (_hsigmaStarted : l1.sigma = ledger.sigma)
      (_hcutoffStarted : l1.cutoff = ledger.cutoff)
      (_hchoiceR : ReferenceCollectionSegmentExtraction.choice r.input = some c)
      (M : OrdinaryMessageCodec.UpRecord
        (CoordinatorCollectionLedger.codecParams p rate.eta.val))
      (_hparseR : ReferenceCollectionSegmentExtraction.effectiveParse r.input l1 = some M)
      (_hacceptR : CoordinatorCollectionLedger.acceptUpCheck l1
        (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true),
      Nonempty (ParsedUpSourceEvidence execution.records B r c M ledger l1 start w n.val) := by
  classical
  let start := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let execution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  dsimp only
  intro n r hnrecordK c ledger l1 hcandidateR hsigmaStarted hcutoffStarted hchoiceR
    M hparseR hacceptR
  let lplus := CoordinatorCollectionLedger.startRoundCandidate c.preLedger
    B[n.val].input.time
    (ReferenceActivePhysicalStep.collectionEnabled c.preLedger B[n.val].input.time)
    (ReferenceCollectionRawBufferHistory.rawDiagnostic B[n.val])
  have hcandidateP : l1 = lplus := by
    calc
      l1 = CoordinatorCollectionLedger.startRoundCandidate c.preLedger r.input.time
          (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic r) := hcandidateR
      _ = lplus := by
        dsimp only [lplus]
        rw [← hnrecordK]
  have hparseP : ReferenceCollectionSegmentExtraction.effectiveParse
      B[n.val].input lplus = some M := by
    rw [hnrecordK, ← hcandidateP]
    exact hparseR
  have hacceptP : CoordinatorCollectionLedger.acceptUpCheck lplus
      (ReferenceActivePhysicalStep.upSenderIndex B[n.val].input) M = true := by
    rw [hnrecordK, ← hcandidateP]
    exact hacceptR
  have hchoiceP : ReferenceCollectionSegmentExtraction.choice B[n.val].input = some c := by
    rw [hnrecordK]
    exact hchoiceR
  have hProot :=
    ReferenceFirstCollectionParsedUpBudgets.actual_first_collection_parsed_up_budget_calendar_replay_join
      rate source rewards C_star C_h count hcross hspan hshort
  have hJoin := hProot n c hchoiceP M hparseP hacceptP
  simp only [Fin.getElem_fin] at hJoin
  rcases hJoin with ⟨P0, birth, state, memory, offered, jDown, message,
    _hinitializer, _hledgerSigma, _hledgerCutoff, _hledgerAssignment,
    _hvalidLedger, _hpending, _hcurrentUnknown, _hcutoffUnknown,
    _hlplusSigma, _hlplusCutoff, hP0Sigma, hP0Queues, hbirthMem,
    hbirth, _hbirthTime, _hconfiguration, hcheckedOffer, hOfferEq,
    _hword, hlastDown, _hjBound, _hjRange, hretained, hmessageP0,
    hmessageSigma, hmessageQ, hmessageMSigma, _hMScore, _hMQueue,
    _hMDelta, _hfirstReply, hbudgetJoint, hbudgetScore, hbudgetDelta,
    hbudgetCap, _hcalendarEnd, _hindices, _hindexLength, _hreplayPrior,
    _hrowsBound, _hlonger, _hlongerLength, _hreplayCandidate,
    _hcandidateRowsBound⟩
  have hcutoffPlus : lplus.cutoff = ledger.cutoff := by
    rw [← hcandidateP]
    exact hcutoffStarted
  have hsigmaPlus : lplus.sigma = ledger.sigma := by
    rw [← hcandidateP]
    exact hsigmaStarted
  have hbudgetJointLedger : M.val.S + M.val.q ≤
      (ledger.cutoff - ledger.sigma) * ConstructorDimensions.D p := by
    change M.val.S + M.val.q ≤
      (lplus.cutoff - lplus.sigma) * ConstructorDimensions.D p at hbudgetJoint
    rw [hcutoffPlus, hsigmaPlus] at hbudgetJoint
    exact hbudgetJoint
  have hbudgetScoreLedger : M.val.S ≤
      (4 * rate.n) * (ledger.cutoff - ledger.sigma) := by
    change M.val.S ≤ (4 * rate.n) * (lplus.cutoff - lplus.sigma) at hbudgetScore
    rw [hcutoffPlus, hsigmaPlus] at hbudgetScore
    exact hbudgetScore
  let sender : ParsedUpSourceEvidence execution.records B r c M ledger l1 start w n.val := {
    P0 := P0
    birth := birth
    state := state
    memory := memory
    offered := offered
    downIndex := jDown
    message := message
    source_choice := hchoiceR
    source_parse := by simpa [hcandidateR] using hparseR
    source_accepted := by simpa [hcandidateR] using hacceptR
    started_candidate := hcandidateR
    P0_sigma := by simpa only using hP0Sigma
    P0_zeroQueues := hP0Queues
    birth_mem := hbirthMem
    birth_time := by simpa only using _hbirthTime
    birth_installation := hbirth
    actual_choice_ordinary := by simpa only [hnrecordK] using _hconfiguration
    checked_offer := by simpa only [hnrecordK] using hcheckedOffer
    offered_is_parsed := hOfferEq
    prior_down_index := _hjBound
    early_or_late_down := _hjRange
    retained_down := by simpa only [hnrecordK] using hretained
    last_down := hlastDown
    message_is_P0_down := by simpa only [hnrecordK] using hmessageP0
    message_sigma := by simpa only using hmessageSigma
    message_queue_zero := hmessageQ
    parsed_sigma := by simpa only using hmessageMSigma
    joint_budget := hbudgetJointLedger
    score_budget := hbudgetScoreLedger
    delta_budget := hbudgetDelta
    sender_capacity := hbudgetCap
    inclusive_calendar_replay := by
      refine ⟨by simpa only using _hcalendarEnd, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hnrecordK] using _hlonger
      · rw [hcandidateR]
        simpa only [hnrecordK] using _hreplayCandidate
      · simpa only [hnrecordK] using _hcandidateRowsBound }
  exact ⟨sender⟩

/-- Locate the first locally admissible UP reception on the original physical
execution. The exhausted-prefix case has only its actual final boundary. The
other case carries the same record, ready state, START, parsed message, P
sender/calendar join, and focused A receiver result. This theorem stops before
the accepted collection FINISH.
-/
theorem actual_generated_first_collection_accepted_reception
    (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (s : ℕ)
    (hsElapsed : s = ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed)
    (count : ℕ) (hspan : s + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
        rate source rewards C_star C_h hcross s hsElapsed count hspan).records).length < count) :
    let initial := ReferenceFirstLaunchNumericalCell.launchState
      rate source rewards C_star C_h hcross
    let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
      rate source rewards C_star C_h hcross s hsElapsed count hspan
    let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
    let w := firstWindow.length
    let b := w + 1
    let Q := (execution.records.drop b).takeWhile
      (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
    let hcount : execution.records.length = count := by
      simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
        ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
          (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
            rate source rewards C_star C_h hcross s hsElapsed)
    let htail : b + Q.length ≤ count := by
      have hw : w < count := by simpa [execution, firstWindow, w] using hshort
      have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
      have hlen := hprefix.length_le
      have hdrop : (execution.records.drop b).length = count - b := by
        simp [List.length_drop, hcount]
      omega
    let k := b + Q.length
    let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
      ReferenceActivePhysicalHorizon.run initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + j)
        (by omega)
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s hsElapsed)
    let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
    ∃ cut payload saved,
      cut = execution.records[w]'(by
        have hw : w < count := by simpa [execution, firstWindow, w] using hshort
        simpa [execution, firstWindow, w] using Nat.lt_of_lt_of_eq hw hcount.symm) ∧
      (∃ ledger,
        (prefixAt Q.length (by omega)).finalState.coordinator =
          .collection payload ledger saved ∧
        ledger.pending = Finset.univ ∧ ledger.sigma = s + 1 ∧ ledger.cutoff = s + b ∧
        ((k = count ∧
          (prefixAt Q.length (by omega)).finalState = execution.finalState ∧
          (∀ htime : s + k < p.T,
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              (ReferenceActivePhysicalHorizon.roundInputAt initial source.1.2
                (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
                (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
                  rate source rewards C_star C_h hcross s hsElapsed)
                (prefixAt Q.length (by omega)) ⟨s + k, by omega, htime⟩)
              payload ledger saved) ∧
          (s + k = p.T →
            ReferenceContinuingCollectionRejectedFinishDomains.continuingCollectionReadyBoundaryDomain
              (prefixAt Q.length (by omega)).finalState payload ledger saved)) ∨
         (∃ hendpoint : k < count,
          ∃ r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate),
            r = execution.records[k]'(by
              exact Nat.lt_of_lt_of_eq hendpoint hcount.symm) ∧
            ∃ hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                r.input payload ledger saved,
              ∃ n : Fin B.length,
                n.val = Q.length + 1 ∧ n.val = k - w ∧
                ∃ _hWindowRecord : B[n.val] = r,
                ∃ c : ReferenceCollectionSegmentExtraction.Choice rate,
                  ∃ o : CoordinatorRecordingOperation.Output p,
                    ∃ l1 : ReferenceActivePhysicalStep.Ledger rate,
                      ∃ _hchoiceR : ReferenceCollectionSegmentExtraction.choice r.input = some c,
                        ∃ _hrecordedR : CoordinatorRecorderComplementBridge.run
                        (ReferenceActivePhysicalStep.collectionRecordingInput
                          (ReferenceActivePhysicalStep.prepare r.input)
                          c.payload c.started c.weights) = some o,
                          ∃ _hstartedR : CoordinatorCollectionLedger.startRound c.preLedger
                        (r.input.time.val + 1)
                        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
                        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) =
                          .success l1,
                            ∃ M : OrdinaryMessageCodec.UpRecord
                                (CoordinatorCollectionLedger.codecParams p rate.eta.val),
                              ∃ _hparseR : ReferenceCollectionSegmentExtraction.effectiveParse
                                  r.input l1 = some M,
                                ∃ _hacceptR : CoordinatorCollectionLedger.acceptUpCheck l1
                                    (ReferenceActivePhysicalStep.upSenderIndex r.input) M = true,
                              CoordinatorCollectionLedger.validLedgerCheck l1 = true ∧
                              CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o =
                                ReferenceCollectionRawBufferHistory.rawDiagnostic r ∧
                              c.payload = payload ∧ c.preLedger = ledger ∧ c.initializer = none ∧
                              (∃ cutoff : Fin p.T, cutoff.val + 1 = ledger.cutoff ∧
                                let input := ReferenceActivePhysicalStep.collectionInput
                                  r.input payload ledger
                                  (ReferenceActivePhysicalStep.collectionClock
                                    payload ledger saved cutoff) cutoff
                                ∃ (core : CoordinatorRoundDispatch.CollectionCoreValid input)
                                  (snap : CoordinatorCollectionInteractive.PreparedSnapshot input)
                                  (hb : snap.clockStarted.clock.g ≤ p.T + 1)
                                  (hs : CoordinatorRoundDispatch.collectionCurrentScoresCheck
                                    input = true),
                                  (ReferenceActivePhysicalStep.prepare r.input).coordinator =
                                    .collection payload ledger
                                      (ReferenceActivePhysicalStep.collectionClock
                                        payload ledger saved cutoff)
                                      cutoff (.continuing core snap hb hs) ∧
                                  c.started = snap.clockStarted) ∧
                              Nonempty
                                (ParsedUpSourceEvidence execution.records B r c M ledger l1 s w n.val ×
                                  AcceptedReceiverOutput r payload ledger saved hReady l1 M)))) := by
  classical
  let initial := ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross
  let execution := ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun
    rate source rewards C_star C_h hcross s hsElapsed count hspan
  let firstWindow := ReferenceFirstLiveConfirmationHistory.firstLiveWindow execution.records
  let w := firstWindow.length
  let b := w + 1
  let Q := (execution.records.drop b).takeWhile
    (fun record => ReferenceGeneratedFirstCollectionRejectedPrefix.rejectionEligible record.input)
  have hcount : execution.records.length = count := by
    simpa [execution, ReferenceGeneratedFirstCutoffSurvival.generatedFirstCutoffRun] using
      ReferenceActivePhysicalHorizon.run_record_count initial source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s count hspan
        (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
          rate source rewards C_star C_h hcross s hsElapsed)
  have htail : b + Q.length ≤ count := by
    have hw : w < count := by simpa [execution, firstWindow, w] using hshort
    have hprefix : Q <+: execution.records.drop b := List.takeWhile_prefix _
    have hlen := hprefix.length_le
    have hdrop : (execution.records.drop b).length = count - b := by
      simp [List.length_drop, hcount]
    omega
  let k := b + Q.length
  let prefixAt := fun (j : ℕ) (hj : j ≤ Q.length) =>
    ReferenceActivePhysicalHorizon.run initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s (b + j)
      (by omega)
      (ReferenceGeneratedFirstCutoffSurvival.generatedLaunchActive
        rate source rewards C_star C_h hcross s hsElapsed)
  let B := ReferenceCollectionPhaseHistory.collectionWindow execution.records w
  have hRgen :=
    ReferenceGeneratedFirstCollectionRejectedPrefix.actual_generated_first_collection_rejected_prefix
      rate source rewards C_star C_h hcross s hsElapsed count hspan hshort
  dsimp only at hRgen
  rcases hRgen with ⟨cut, payload, saved, hcut, _hseed, hboundary⟩
  have hq : Q.length + b ≤ count := by
    simpa [Nat.add_comm] using htail
  let j := Q.length
  have hj : j ≤ Q.length := by dsimp [j]; exact Nat.le_refl _
  have hindexPrefix : b + j ≤ count := by dsimp [j]; omega
  obtain ⟨ledger, hstate, hrest⟩ := hboundary j hj
  rcases hrest with ⟨hpendingBoundary, hsigmaBoundary, hcutBoundary, hreadyAtBoundary, hrest⟩
  rcases hrest with ⟨_hindexAtBoundary, hrest⟩
  rcases hrest with ⟨hterminal, hrest⟩
  rcases hrest with ⟨_hrejectedSteps, hrest⟩
  rcases hrest with ⟨hacceptedEndpoint, hexhaustedEndpoint⟩
  refine ⟨cut, payload, saved, ?_, ?_⟩
  · exact hcut
  · refine ⟨ledger, hstate, hpendingBoundary, hsigmaBoundary, hcutBoundary, ?_⟩
    by_cases hExhausted : k = count
    · left
      refine ⟨hExhausted, ?_, ?_, ?_⟩
      · simpa [prefixAt, j, k, b, execution, initial] using
          hexhaustedEndpoint rfl (by simpa [k, b, j] using hExhausted)
      · intro htime
        have hready := hreadyAtBoundary (by
          simpa only [k, j, Nat.add_assoc] using htime)
        simpa only [k, j, Nat.add_assoc] using hready
      · intro htime
        apply hterminal
        simpa [k, j, Nat.add_assoc] using htime
    · right
      have hnotExhausted : k < count := by omega
      refine ⟨hnotExhausted, ?_⟩
      have hindexStop : b + j < count := by
        simpa [j, k] using hnotExhausted
      have hrecordIndex : k < execution.records.length := by
        rw [hcount]
        exact hnotExhausted
      have hEnd := hacceptedEndpoint rfl hindexStop
      rcases hEnd with ⟨hReadyEnd, cutoff, hcutoff, core, snap, hb, hs, hcoord, hrest⟩
      rcases hrest with ⟨_, _, _, c, o, l1, hchoiceR, hrecordedR,
        hcPayload, hcLedger, hcStarted, hcInitializer, hstartedR, hparsedAccepted⟩
      rcases hparsedAccepted with ⟨M, hparseR, hacceptR, _hnotRejected⟩
      let r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
        execution.records[k]'hrecordIndex
      have hrRecord : r = execution.records[k]'hrecordIndex := rfl
      have hrecordsBound : w + 1 + Q.length < execution.records.length := by
        simpa [k, b, w] using hrecordIndex
      have hreadyPrefix : ∀ j' (hj' : j' ≤ Q.length),
          ∃ ledger' : ReferenceActivePhysicalStep.Ledger rate,
            ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
              (execution.records[w + 1 + j']'(by omega)).input payload ledger' saved := by
        intro j' hj'
        by_cases hjEq : j' = Q.length
        · subst j'
          refine ⟨ledger, ?_⟩
          simpa [r, k, b, j] using hReadyEnd
        · have hjLt : j' < Q.length := by omega
          obtain ⟨ledger', _hcoord', hrest'⟩ := hboundary j' (by omega)
          rcases hrest' with ⟨_, _, _, hreadyFun', hrest'⟩
          rcases hrest' with ⟨hindexFun', _⟩
          have hindex' : b + j' < count := by omega
          have htime' : s + b + j' < p.T := by omega
          have hReadyRound := hreadyFun' htime'
          have hinputEq := hindexFun' hindex'
          have hReadyRecord :
              ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                (execution.records[b + j']'(by rw [hcount]; exact hindex')).input
                payload ledger' saved := by
            rw [← hinputEq]
            exact hReadyRound
          refine ⟨ledger', ?_⟩
          simpa [b] using hReadyRecord
      have hcutIndex : w < execution.records.length := by
        omega
      obtain ⟨nGenerated, hnval, hnrecord⟩ :=
        collectionWindow_getElem_after_ready_prefix execution.records w Q.length
          hcutIndex hrecordsBound payload saved hreadyPrefix
      have hnrecordGen :
          (ReferenceCollectionPhaseHistory.collectionWindow execution.records w)[nGenerated.val] =
            r := by
        simpa [k, b, r, hnval] using hnrecord
      let n : Fin B.length := nGenerated
      have hnrecordK : B[n.val] = r := hnrecordGen
      have hnOffset : n.val = k - w := by
        calc
          n.val = Q.length + 1 := hnval
          _ = k - w := by change _ = (w + 1 + Q.length) - w; omega
      have hcandidate := accepted_reception_of_ready r r.input rfl
        payload ledger saved hReadyEnd c o l1 hchoiceR hrecordedR hstartedR
      rcases hcandidate with ⟨_cutoffA, _hcutoffA, _coreA, _snapA, _hbA, _hsA, _hcoordA, hrestReceiver⟩
      rcases hrestReceiver with ⟨_, _, hcandidateStart, hsigmaStarted,
        hcutoffStarted, hvalidStarted, _hrecordingOutput, hdiagnosticOutput,
        hrawStarted, hreceiveDomain, hreceiveCheck, hbankInput, hreceiverQuery⟩
      have hcandidateR : l1 = CoordinatorCollectionLedger.startRoundCandidate c.preLedger
          r.input.time (ReferenceActivePhysicalStep.collectionEnabled c.preLedger r.input.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic r) := by
        calc
          l1 = CoordinatorCollectionLedger.startRoundCandidate ledger r.input.time
              (ReferenceActivePhysicalStep.collectionEnabled ledger r.input.time)
              (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder o) := hcandidateStart
          _ = _ := by rw [← hcLedger, hrawStarted]
      let hspanActual : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput
              source rewards C_star C_h rate)).completed +
            count ≤ p.T := by simpa only [hsElapsed] using hspan
      have hrunEq := actual_first_collection_run_eq_generated
        rate source rewards C_star C_h hcross s hsElapsed count hspan hspanActual
      let actualExecution := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspanActual
      have hrunRecords : actualExecution.records = execution.records :=
        congrArg (fun run => run.records) hrunEq
      have hshortActual : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          actualExecution.records).length < count := by
        rw [hrunRecords]
        exact hshort
      let wActual :=
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow actualExecution.records).length
      let actualB := ReferenceCollectionPhaseHistory.collectionWindow actualExecution.records wActual
      have hwActual : wActual = w := by
        dsimp only [wActual]
        rw [hrunRecords]
      have hActualB : actualB = B := by
        dsimp only [actualB]
        rw [hrunRecords, hwActual]
      let nActual : Fin actualB.length := ⟨n.val, by rw [hActualB]; exact n.isLt⟩
      have hnActual : actualB[nActual.val] = r := by
        simpa only [hActualB, nActual] using hnrecordK
      have hsenderActual := parsed_up_source_evidence_of_actual_record
        rate source rewards C_star C_h hcross count hspanActual hshortActual
        nActual r hnActual c ledger l1 hcandidateR hsigmaStarted hcutoffStarted
        hchoiceR M hparseR hacceptR
      change Nonempty (ParsedUpSourceEvidence actualExecution.records actualB r c M ledger l1
        _ wActual n.val) at hsenderActual
      have hsender : Nonempty (ParsedUpSourceEvidence execution.records B r c M ledger l1
          s w n.val) := by
        simpa only [hrunRecords, hActualB, hwActual, ← hsElapsed] using hsenderActual
      obtain ⟨sender⟩ := hsender
      obtain ⟨receiver⟩ := accepted_receiver_output_of_ready r payload ledger saved hReadyEnd
        c o l1 hchoiceR hrecordedR hstartedR M hparseR hacceptR
        sender.joint_budget sender.score_budget
      refine ⟨r, hrRecord, hReadyEnd, n, hnval, hnOffset, hnrecordK,
        c, o, l1, hchoiceR, hrecordedR, hstartedR, M, hparseR, hacceptR,
        hvalidStarted, hrawStarted, hcPayload, hcLedger, hcInitializer, ?_, ?_⟩
      · exact ⟨cutoff, hcutoff, core, snap, hb, hs, hcoord, hcStarted⟩
      · exact ⟨(sender, receiver)⟩

end Bandits.Support.ReferenceGeneratedFirstCollectionAcceptedReception

end
