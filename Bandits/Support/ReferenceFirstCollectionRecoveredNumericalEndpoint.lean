/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionAcceptedSegmentPrefix
public import Bandits.Support.ReferenceFirstCollectionParsedUpCanonicalCutoff
public import Bandits.Support.ReferenceFirstCollectionQueueContinuation

import Lean.Elab.Tactic.Omega

/-!
# Original-source numerical endpoint of a recovered first-collection arm

Mathematical evidence:
`sources/zip4/manuscript/06_interruptions.tex:9-100,246-299`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The actual accepted segment prefix supplies the operational endpoint. Its
literal source cells identify every physical queue input through the current
round. The canonical parsed-UP theorem identifies the returned cutoff fields;
the queue continuation theorem then supplies the recovered queue and service
sum. Replay append needs equality of the sender's cutoff endpoint only.

Current readiness, effective parsing and acceptance remain explicit internal
branch conditions. No future successful execution or future readout presence
is an input or conclusion. The next consumers are the original-source
accepted-arm continuation and its all-arm join with KnownSourceSplice and the
actual ReadyStream. This result does not close a manuscript assertion.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ReferenceCollectionSegmentExtraction

namespace Bandits.Support.ReferenceFirstCollectionRecoveredNumericalEndpoint

variable {p : ConstructorDimensions.Parameters}

/-- A score offset commutes with the existing replay; the backlog is unchanged.
The one-round fact is the public queue-transition theorem. -/
private theorem replay_add_score (capacity score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (score, backlog) records =
      (score + (QueueReplay.replay capacity (0, backlog) records).1,
        (QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (0, backlog) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [CollectionKnownQueueContinuation.queueReplay_transition_add_score]
      rw [ih (score + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2]
      rw [ih (QueueReplay.transition capacity (0, backlog) record).1
        (QueueReplay.transition capacity (0, backlog) record).2]
      simp only [Nat.add_assoc]

/-- Equality through an inspected prefix restricts to each shorter prefix. -/
private theorem take_eq_of_take_eq {α : Type*} (xs ys : List α)
    (limit : ℕ) (heq : xs.take limit = ys.take limit)
    (h : ℕ) (hh : h ≤ limit) : xs.take h = ys.take h := by
  have ht := congrArg (fun zs : List α => zs.take h) heq
  simpa only [List.take_take, Nat.min_eq_left hh] using ht

/-- Transport the physical record using the full collection context. In
particular the freeze boundary, not merely sigma, must be shared. -/
private theorem physicalQueueRecord_context
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (left right : ReferenceActivePhysicalStep.Ledger rate)
    (hcontext : CollectionBufferProvenance.collectionContext left =
      CollectionBufferProvenance.collectionContext right)
    (arm : Fin p.K)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    ReferenceCollectionRawBufferHistory.physicalQueueRecord left arm record =
      ReferenceCollectionRawBufferHistory.physicalQueueRecord right arm record := by
  simp only [CollectionBufferProvenance.collectionContext, Prod.mk.injEq] at hcontext
  simp only [ReferenceCollectionRawBufferHistory.physicalQueueRecord,
    ReferenceActivePhysicalStep.collectionEnabled,
    hcontext.2.1, hcontext.2.2.1, hcontext.2.2.2.1]

section ActualSource

variable (rate : ReferenceActivePhysicalStep.RateInput p)
    (source : BootstrapPrivateRoundStreams.SourceInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput
        source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput
          source rewards C_star C_h rate)).completed + count ≤ p.T)

variable (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan).records).length < count)

include hshort

/-- The actual accepted arm's cutoff, inclusive recovered queue, last service
and increment are the numerical replays of the original source cells. The
readout witnesses retain every cell through the current acceptance round,
including enabled zero-arrival and disabled rows. -/
theorem actual_first_collection_recovered_numerical_endpoint
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (saved : Option (Fin p.T × Bool))
    (hReady : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      payload ledger saved)
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparse : effectiveParse
      (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input
      (CoordinatorCollectionLedger.startRoundCandidate ledger
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val])) = some M)
    (haccept : CoordinatorCollectionLedger.acceptUpCheck
      (CoordinatorCollectionLedger.startRoundCandidate ledger
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled ledger
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic
          (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val]))
      (ReferenceActivePhysicalStep.upSenderIndex
        (ReferenceCollectionPhaseHistory.collectionWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records
          (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
            (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
              rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input) M = true) :
    let epoch := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
      rate source rewards C_star C_h hcross count hspan
    let live := ReferenceFirstLiveConfirmationHistory.firstLiveWindow epoch.records
    let window := ReferenceCollectionPhaseHistory.collectionWindow epoch.records live.length
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let u := s + live.length + 1
    let i := ReferenceActivePhysicalStep.upSenderIndex window[n.val].input
    let a := ledger.assignment.arm i
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hcross count hspan
    let qp := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let Arr := fun Y : List (RecordedQueueRun.RoundInput p.K) =>
      Y.map (fun z => (z.enabled, RecordedQueueRun.quantizedArrival qp z a))
    let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (Arr (cells.take h))
    ∃ (c : Choice rate) (f : ReferenceActivePhysicalStep.Ledger rate)
      (completed : CompletedRound rate)
      (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (head : Choice rate) (initializer : Initializer p) (seg : Segment rate),
      0 < n.val ∧ choice window[n.val].input = some c ∧
      c.payload = payload ∧ c.preLedger = ledger ∧ c.initializer = none ∧
      window[n.val].output.next.coordinator = .collection payload f saved ∧
      f.cursor = u + n.val + 1 ∧ f.pending = ledger.pending.erase i ∧
      extractRound window[n.val] = some completed ∧ completed.context = c ∧
      completed.final = f ∧ completed.accepted = true ∧
      completed.input.parsed = some M ∧ completed.input.selectedFollower = i ∧
      cut = window[0]'(by exact Nat.lt_of_le_of_lt (Nat.zero_le n.val) n.isLt) ∧
      choice cut.input = some head ∧ head.initializer = some initializer ∧
      initializer.checkedStart rate = .success head.preLedger ∧
      (∀ j, initializer.base j = 0) ∧
      segmentAt epoch.records live.length = some seg ∧ seg.entry = cut ∧ seg.context = head ∧
      ∃ retained : n.val < seg.records.length,
      seg.records.take (n.val + 1) = window.take (n.val + 1) ∧
      seg.records[n.val]'retained = window[n.val] ∧
      CollectionCheckedExecution.checkedRounds head.preLedger
        (inputs (seg.records.take (n.val + 1))) =
        some (acceptances (seg.records.take (n.val + 1)), f) ∧
      endpointLedger head.preLedger (seg.records.take (n.val + 1)) = f ∧
      ∃ (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
          head.payload head.started head.weights))
        (present : ∀ k : Fin n.val,
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
            (window[k.val + 1]'(Nat.lt_of_le_of_lt (Nat.succ_le_of_lt k.isLt) n.isLt))).isSome = true),
      let c_u := ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate cut head rewards valid
      let D := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix rate s window n c_u present
      let R := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (Arr (cells ++ D.take h))
      D.length = n.val + 1 ∧ D[0]'(by
        rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length]; omega) = c_u ∧
      (∀ h : Fin (n.val + 1), 0 < h.val →
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
          (window[h.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h.isLt) n.isLt)) =
          some (D[h.val]'(by
            rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length]; exact h.isLt))) ∧
      (∀ h : Fin (n.val + 1),
        let record := window[h.val]'(Nat.lt_of_le_of_lt (Nat.le_of_lt_succ h.isLt) n.isLt)
        let cell := D[h.val]'(by
          rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length]; exact h.isLt)
        ∃ (call : Choice rate)
          (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
            (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
              call.payload call.started call.weights)),
          choice record.input = some call ∧ call.payload = payload ∧
          CollectionBufferProvenance.collectionContext call.preLedger =
            CollectionBufferProvenance.collectionContext head.preLedger ∧
          cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate record call rewards validCall ∧
          record.input.rows = source.1.2 ∧
          record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
          record.input.rewards = rewards ∧ record.input.time.val = s + live.length + h.val ∧
          cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
          cell.reward = (fun arm => ((rewards record.input.time arm).val : ℝ) /
            (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = payload.rate ∧
          (∀ arm : Fin p.K,
            ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger arm record =
              (cell.enabled, RecordedQueueRun.quantizedArrival qp cell arm))) ∧
      (∀ (h : ℕ), h ≤ n.val + 1 → ∀ arm : Fin p.K,
        (seg.records.take h).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger arm) =
        (D.take h).map (fun z =>
          (z.enabled, RecordedQueueRun.quantizedArrival qp z arm))) ∧
      f.cutoffRegisters a = some ⟨(V live.length).1, (V live.length).2,
        (V live.length).1 - (V (live.length - 1)).1⟩ ∧
      f.currentRegisters a = some ⟨(R (n.val + 1)).2,
        (R (n.val + 1)).1 - (R n.val).1⟩ ∧
      f.increment a =
        (QueueReplay.replay (4 * rate.n) (0, (V live.length).2) (Arr D)).1 ∧
      (V live.length).1 + f.increment a = (R (n.val + 1)).1 ∧ f.gammaLoc a = 0 := by
  classical
  intro epoch live window s u i a cells qp Arr V
  have hnWindow : n.val < window.length := n.isLt

  -- S produces the actual completion and the checked prefix through it.
  obtain ⟨c, recording, started, f, completed, cutS, headS, f0S, initializerS, seg,
      hn, hc, hpay, hledger, hinit, hrecording, hstart, hcandidate,
      hoperations, hcursor, hpending, hnext, he, hcompletedContext, hfinal,
      haccepted, hparsed, hselected, _hround, _hraw, _hcheckedCurrent,
      hcutS, hheadS, hinitS, _hinitSomeS, hcheckedInitS, _hcompletedHeadS,
      _hearlierS, _hfoldS, hsegment, hentry, hsegContext,
      retained, htake, hcurrentRecord, hcurrentExtract, hcheckedPrefix, _hinitialized⟩ :=
    ReferenceFirstCollectionAcceptedSegmentPrefix.actual_first_collection_accepted_segment_prefix
      rate source rewards C_star C_h count hcross hspan hshort n payload ledger saved
      hReady M hparse haccept

  -- These are definitionally the same launch and horizon; active-mode proofs
  -- are propositions, so their different derivations cannot change the run.
  have hrun : ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hcross count hspan = epoch := by rfl
  have hlive : ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hcross count hspan = live := by rfl
  have hqrun : ReferenceActivePhysicalHorizon.run
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s count hspan
      (ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
        rate source rewards C_star C_h hcross) = epoch := by rfl

  -- A produces the literal cutoff cell and every later SOME up to this n.
  have hsource :=
    ReferenceFirstCollectionCheckedSourcePrefix.actual_first_collection_checked_source_prefix
      rate source rewards C_star C_h hcross count hspan hshort n hn c hc
  dsimp only at hsource
  simp only [hrun, hlive, Fin.getElem_fin] at hsource
  obtain ⟨cut, suffix, r, q, base, head, f0, proposal, hindex, hrecords, hwindow,
      hstate, hheadPayload, hinitializerA, hhead, _hcompleted0, _hcutNext,
      valid, present, hDlen, hDzero, hcallPayload, _hcallInit,
      _hcontextF0, _hchain, _hfold, _hHlen, _hInputLen, _hDtailLen,
      _hHAt, hAll, _hSourceRows⟩ := hsource
  change epoch.records = live ++ cut :: suffix at hrecords
  change window = cut :: suffix.takeWhile
    (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) at hwindow
  have hzero : cut = window[0]'(by omega) := by
    have hz := congrArg (fun records => records[0]?) hwindow
    simpa only [List.getElem?_eq_getElem (by omega : 0 < window.length),
      List.getElem?_cons_zero, Option.some.injEq] using hz.symm
  have hcutEq : cutS = cut := hcutS.trans hzero.symm
  have hheadEq : headS = head := by
    have ht : choice cut.input = some headS := hcutEq ▸ hheadS
    exact Option.some.inj (ht.symm.trans hhead)
  have hinitializer : head.initializer = some initializerS := hheadEq ▸ hinitS
  have hcheckedInit : initializerS.checkedStart rate = .success head.preLedger :=
    hheadEq ▸ hcheckedInitS
  have hsegHead : seg.context = head := hsegContext.trans hheadEq
  have hsegEntry : seg.entry = cut := hentry.trans hcutEq

  let c_u := ReferenceFirstCollectionCheckedSourcePrefix.sourceCell rate cut head rewards valid
  let D := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix rate s window n c_u present
  let R := fun h => QueueReplay.replay (4 * rate.n) (0, 0) (Arr (cells ++ D.take h))
  have hDlength : D.length = n.val + 1 := hDlen

  -- Full context preservation connects the actual pre-ledger to the same
  -- head, including assignment and freeze boundary.
  have hcheckedHead : CollectionCheckedExecution.checkedRounds head.preLedger
      (inputs (seg.records.take (n.val + 1))) =
      some (acceptances (seg.records.take (n.val + 1)), f) := hheadEq ▸ hcheckedPrefix
  have hendpoint : endpointLedger head.preLedger (seg.records.take (n.val + 1)) = f := by
    rw [List.take_succ_eq_append_getElem retained, endpointLedger_append]
    simp only [endpointLedger, ReferenceCollectionSegmentExtraction.completed,
      List.filterMap_cons, hcurrentExtract, List.filterMap_nil,
      List.foldl_cons, List.foldl_nil, hfinal]

  have hcurrentSource := hAll ⟨n.val, Nat.lt_succ_self n.val⟩
  obtain ⟨callN, _validN, hcallN, _hpayN, hcontextN, _hinitN, _hcellN,
    _hrowsN, _hselectedN, _hrewardsN, _htimeN, _henabledN, _hclockN,
    _hrewardN, _hrateN, _houtN, _hreadN, _hcompleteN⟩ := hcurrentSource
  have hcallNEq : callN = c := Option.some.inj (hcallN.symm.trans hc)
  have hcontext : CollectionBufferProvenance.collectionContext ledger =
      CollectionBufferProvenance.collectionContext head.preLedger := by
    simpa only [hcallNEq, hledger] using hcontextN
  have hheadAssignment : head.preLedger.assignment = ledger.assignment :=
    (congrArg Prod.fst hcontext).symm
  have hinitFields := CollectionBufferProvenance.startCollectionChecked_success_context
    initializerS.assignment initializerS.sigma initializerS.cutoff initializerS.freezeAt
    initializerS.base initializerS.outside head.preLedger hcheckedInit
  have harm : initializerS.assignment.arm i = a := by
    change initializerS.assignment.arm i = ledger.assignment.arm i
    rw [← hinitFields.1, hheadAssignment]

  -- K identifies the actual first cutoff's base as the launch zero vector.
  -- Equality of the complete LIVE constructors identifies the dependent
  -- owned registers and base; no sigma-only substitution is used.
  have hK := ReferenceFirstCutoffKnownNumericalState.actual_first_cutoff_known_numerical_state
    rate source rewards C_star C_h hcross count hspan hshort
  dsimp only at hK
  obtain ⟨cutK, _suffixK, rK, qK, baseK, _dispatchedK, _hstartK,
      _ledgerK, _hinitK, _hledgerK, _hdomainK, _hclockK, _hpendingK,
      _hnoAssignmentK, _selectedK, _outK, hcutK, _hrecordsK, _hphysicalK,
      _htimeK, _hrowsK, _hselectedK, _hrewardsK, _hsigmaK, _hnRateK,
      hbaseK, hstateK, _hKtail⟩ := hK
  have hcutKLookup : epoch.records[live.length]? = some cutK := by
    have ht := congrArg (fun records => records[live.length]?) _hrecordsK
    simpa only [hrun, hlive, List.getElem?_append_right (Nat.le_refl live.length),
      Nat.sub_self, List.getElem?_cons_zero] using ht
  have hcutKEq : cutK = cut := Option.some.inj (hcutKLookup.symm.trans hindex)
  have hbase : ∀ j, base j = 0 := by
    have hliveState := hstate.symm.trans (hcutKEq ▸ hstateK)
    have hb : base = baseK := by
      cases hliveState
      rfl
    simpa only [hb] using hbaseK
  have hinitEq : initializerS = cutoffInitializer
      (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
      (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time :=
    Option.some.inj (hinitializer.symm.trans hinitializerA)
  have hbaseZero : ∀ j, initializerS.base j = 0 := by
    rw [hinitEq]
    exact hbase

  -- X is applied at S's very choice/candidate/message, with ledger identity
  -- used throughout the parse and acceptance expressions.
  have hparseC : effectiveParse window[n.val].input
      (CoordinatorCollectionLedger.startRoundCandidate c.preLedger window[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger window[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic window[n.val])) = some M := by
    simpa only [hledger] using hparse
  have hacceptC : CoordinatorCollectionLedger.acceptUpCheck
      (CoordinatorCollectionLedger.startRoundCandidate c.preLedger window[n.val].input.time
        (ReferenceActivePhysicalStep.collectionEnabled c.preLedger window[n.val].input.time)
        (ReferenceCollectionRawBufferHistory.rawDiagnostic window[n.val])) i M = true := by
    simpa only [hledger] using haccept
  have hX :=
    ReferenceFirstCollectionParsedUpCanonicalCutoff.actual_first_collection_parsed_up_canonical_cutoff
      rate source rewards C_star C_h count hcross hspan hshort n c hc M hparseC hacceptC
  dsimp only at hX
  obtain ⟨_P0, _birth, _dX, _messageX, _hbirth, _hinstall, _hbirthTime,
    _hP0, _hmessage, _hzeroQ, _hretainedX, _hdX, hsigma, hMS, hMq, hMdelta⟩ := hX
  have hMSV : M.val.S = (V live.length).1 := by simpa only [Fin.getElem_fin, hledger] using hMS
  have hMqV : M.val.q = (V live.length).2 := by simpa only [Fin.getElem_fin, hledger] using hMq
  have hMdeltaV : M.val.delta = (V live.length).1 - (V (live.length - 1)).1 := by
    simpa only [Fin.getElem_fin, hledger] using hMdelta

  -- Q only needs the PRODUCED segment, completion and first-sigma field.
  have hsegmentQ : segmentAt
      (ReferenceActivePhysicalHorizon.run
        (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
        source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
        s count hspan
        (ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
          rate source rewards C_star C_h hcross)).records live.length = some seg := by
    rw [hqrun]
    exact hsegment
  have hQ :=
    ReferenceFirstCollectionQueueContinuation.actual_first_assignment_accepted_up_queue_suffix_from_crossing
      source rewards C_star C_h hcross count hspan i live.length seg hsegmentQ
      n.val retained completed hcurrentExtract haccepted M hparsed hselected hsigma
  dsimp only at hQ
  obtain ⟨_global, _hglobal, _hglobalRecord, _hacceptedUp,
    d, _hd, message, _hretainedDown, _hmessageSigma,
    _huBound, _huLast, _hmPos, _hmBound, _hbBound, hMSQ, hMqQ, hMdeltaQ,
    _hboundary, initializerQ, hinitializerQ, _hcheckedStartQ, _hwholeQ,
    _startedQ, _hassignQ, _harmQ, _hsigmaQ, _hcutoffQ, _hfreezeQ, hforallQ, _hfullQ⟩ := hQ
  have hinitQEq : initializerQ = initializerS := by
    have hi : head.initializer = some initializerQ := hsegHead ▸ hinitializerQ
    exact Option.some.inj (hi.symm.trans hinitializer)
  subst initializerQ

  -- Every source/physical identity is retained for all arms. This also
  -- transports Q's head context across each individual source recorder call.
  have hsourceCells : ∀ h : Fin (n.val + 1),
      let record := window[h.val]'(by omega)
      let cell := D[h.val]'(by omega)
      ∃ (call : Choice rate)
        (validCall : CoordinatorRecorderComplementBridge.LocalInputsValid
          (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
            call.payload call.started call.weights)),
        choice record.input = some call ∧ call.payload = payload ∧
        CollectionBufferProvenance.collectionContext call.preLedger =
          CollectionBufferProvenance.collectionContext head.preLedger ∧
        cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate record call rewards validCall ∧
        record.input.rows = source.1.2 ∧
        record.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
        record.input.rewards = rewards ∧ record.input.time.val = s + live.length + h.val ∧
        cell.enabled = ReferenceActivePhysicalStep.collectionEnabled call.preLedger record.input.time ∧
        cell.reward = (fun arm => ((rewards record.input.time arm).val : ℝ) /
          (ConstructorDimensions.D p : ℝ)) ∧ cell.rate = payload.rate ∧
        (∀ arm : Fin p.K,
          ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger arm record =
            (cell.enabled, RecordedQueueRun.quantizedArrival qp cell arm)) := by
    intro h
    obtain ⟨call, validCall, hchoiceCall, hpayCall, hcontextCall, _hinitCall,
      hcell, hrows, hselectedCell, hrewards, htime, henabled, _hclock,
      hreward, hrate, hout, _hread, _hcomplete⟩ := hAll h
    refine ⟨call, validCall, hchoiceCall, hpayCall.trans hcallPayload.symm |>.trans hpay,
      hcontextCall, hcell, hrows, hselectedCell, hrewards, htime, henabled,
      hreward, ?_, ?_⟩
    · exact hrate.trans (congrArg (fun P : ReferenceActivePhysicalStep.Payload rate => P.rate)
        (hcallPayload.symm.trans hpay))
    · obtain ⟨_out, _hrun, _hdiagnostic, _hgate, _hraw, _harrival,
        hphysical, _habsent, _hzeroReward⟩ := hout
      intro arm
      rw [← physicalQueueRecord_context rate call.preLedger head.preLedger
        hcontextCall arm]
      exact hphysical arm

  have hphysicalPrefix : ∀ h, h ≤ n.val + 1 → ∀ arm : Fin p.K,
      (seg.records.take h).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord head.preLedger arm) =
      (D.take h).map (fun z =>
        (z.enabled, RecordedQueueRun.quantizedArrival qp z arm)) := by
    intro h hh arm
    rw [take_eq_of_take_eq seg.records window (n.val + 1) htake h hh]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take]
      rw [Nat.min_eq_left (by omega : h ≤ window.length),
        Nat.min_eq_left (by omega : h ≤ D.length)]
    · intro k hkLeft hkRight
      have hk : k < h := by
        simpa only [List.length_map, List.length_take,
          Nat.min_eq_left (by omega : h ≤ window.length)] using hkLeft
      obtain ⟨_call, _validCall, _hc, _hp, _hctx, _hcell, _hrows, _hsel,
        _hrewards, _htime, _henabled, _hreward, _hrate, hphysical⟩ :=
        hsourceCells ⟨k, by omega⟩
      simpa only [List.getElem_map, List.getElem_take] using hphysical arm

  -- Q's sender prefix is replaced by its endpoint, never by an asserted
  -- equality of sender lists. The predecessor h=n is retained for delta.
  let senderRecords := ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
    (ReferenceActivePhysicalHorizon.run
      (ReferenceFirstLaunchNumericalCell.launchState rate source rewards C_star C_h hcross)
      source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards
      s count hspan
      (ReferenceFirstLaunchNumericalCell.launchState_allActiveAtStart
        rate source rewards C_star C_h hcross)).records
    i d.val message
    (FollowerCutoffScan.firstCutoff p rate.eta.val
      (ActiveFollowerDownAcceptance.downStart p rate message)
      (FollowerCutoffScan.completeRowProposalBit p rate.eta.val
        (source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source))) - (s + 1))
  have hsender : QueueReplay.replay (4 * rate.n) (0, 0) senderRecords = V live.length := by
    apply Prod.ext
    · exact hMSQ.symm.trans hMSV
    · exact hMqQ.symm.trans hMqV
  have hcellsLength : cells.length = live.length :=
    ReferenceFirstWindowNumericalStream.actualLiveSourceCells_length
      rate source rewards C_star C_h hcross count hspan
  have hsenderAppend : ∀ h, h ≤ n.val + 1 →
      QueueReplay.replay (4 * rate.n) (0, 0)
        (senderRecords ++ (seg.records.take h).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord seg.context.preLedger
            (initializerS.assignment.arm i))) = R h := by
    intro h hh
    rw [hsegHead, harm, hphysicalPrefix h hh a, QueueReplay.replay_append, hsender]
    change QueueReplay.replay (4 * rate.n) (V live.length) (Arr (D.take h)) = _
    dsimp only [R, Arr]
    rw [List.map_append, QueueReplay.replay_append]
    have htakeCells : cells.take live.length = cells := by
      rw [← hcellsLength, List.take_length]
    change QueueReplay.replay (4 * rate.n) (V live.length) _ =
      QueueReplay.replay (4 * rate.n)
        (QueueReplay.replay (4 * rate.n) (0, 0) (Arr cells)) _
    rw [← htakeCells]

  obtain ⟨_suffixAccepted, _hcheckedSuffix, hcurrentQ, hincrementQ,
    _hsumQ, hcutoffQ, _hbaseSumQ, _hassignmentEndpoint, _hsigmaEndpoint,
    _hcutoffEndpoint, _hfreezeEndpoint⟩ :=
    hforallQ (n.val + 1) le_rfl (Nat.succ_le_of_lt retained)
  have hcurrent : f.currentRegisters a =
      some ⟨(R (n.val + 1)).2, (R (n.val + 1)).1 - (R n.val).1⟩ := by
    simp only [Nat.add_sub_cancel] at hcurrentQ
    rw [hsenderAppend (n.val + 1) le_rfl,
      hsenderAppend n.val (Nat.le_succ n.val)] at hcurrentQ
    simpa only [hsegHead, hendpoint, harm] using hcurrentQ
  have hcutoff : f.cutoffRegisters a =
      some ⟨(V live.length).1, (V live.length).2,
        (V live.length).1 - (V (live.length - 1)).1⟩ := by
    rw [← hMdeltaQ] at hcutoffQ
    simpa only [hsegHead, hendpoint, harm, hbaseZero, Nat.zero_add,
      ← hMSQ, ← hMqQ, hMSV, hMqV, hMdeltaV] using hcutoffQ
  have hDtake : D.take (n.val + 1) = D := by rw [← hDlength, List.take_length]
  have hincrement : f.increment a =
      (QueueReplay.replay (4 * rate.n) (0, (V live.length).2) (Arr D)).1 := by
    simpa only [hsegHead, hendpoint, harm, hphysicalPrefix (n.val + 1) le_rfl a,
      hDtake, ← hMqQ, hMqV] using hincrementQ
  have hscoreOffset : R (n.val + 1) =
      ((V live.length).1 +
        (QueueReplay.replay (4 * rate.n) (0, (V live.length).2) (Arr D)).1,
        (QueueReplay.replay (4 * rate.n) (0, (V live.length).2) (Arr D)).2) := by
    rw [← hsenderAppend (n.val + 1) le_rfl, QueueReplay.replay_append, hsender,
      hsegHead, harm, hphysicalPrefix (n.val + 1) le_rfl a, hDtake]
    exact replay_add_score (4 * rate.n) (V live.length).1 (V live.length).2 (Arr D)
  have hsum : (V live.length).1 + f.increment a = (R (n.val + 1)).1 := by
    rw [hincrement]
    exact (congrArg Prod.fst hscoreOffset).symm
  have hgamma : f.gammaLoc a = 0 := by
    obtain ⟨decoded, _bank, _hreceive, _hdecode, hfinish⟩ := hoperations
    rw [CollectionCheckedExecution.finishRound_success_candidate decoded f hfinish]
    rfl
  have hreadout : ∀ h : Fin (n.val + 1), 0 < h.val →
      ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
        (window[h.val]'(by omega)) = some (D[h.val]'(by omega)) := by
    intro h hh
    obtain ⟨_call, _valid, _hc, _hp, _hcontext, _hinit, _hcell, _hrows,
      _hselected, _hrewards, _htime, _henabled, _hclock, _hreward,
      _hrate, _hout, hread, _hcomplete⟩ := hAll h
    exact hread hh
  exact ⟨c, f, completed, cut, head, initializerS, seg, hn, hc, hpay,
    hledger, hinit, hnext, hcursor, hpending, he, hcompletedContext, hfinal,
    haccepted, hparsed, hselected, hzero, hhead, hinitializer, hcheckedInit,
    hbaseZero, hsegment, hsegEntry, hsegHead, retained, htake, hcurrentRecord,
    hcheckedHead, hendpoint, valid, present, hDlength, hDzero, hreadout,
    hsourceCells, hphysicalPrefix, hcutoff, hcurrent, hincrement, hsum, hgamma⟩

end ActualSource

end Bandits.Support.ReferenceFirstCollectionRecoveredNumericalEndpoint

end
