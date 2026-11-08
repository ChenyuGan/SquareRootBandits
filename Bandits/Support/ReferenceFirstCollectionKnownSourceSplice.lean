/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionCheckedSourcePrefix

import Lean.Elab.Tactic.Omega

/-!
# First collection known-arm numerical splice

This module consumes the checked actual collection prefix and the actual
first-cutoff numerical state to identify a known fast arm's literal queue
replay through an actual later choice.  The queue update includes enabled
zero-arrival service and disabled preservation.  The current round is only a
pure candidate calculation; no current checked completion or commit is claimed.

Mathematical evidence:
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/06_interruptions.tex:246-295,391-397`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionKnownSourceSplice

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable

variable {p : Parameters}

private theorem replay_add_score_offset (capacity offset score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (offset + score, backlog) records =
      (offset + (QueueReplay.replay capacity (score, backlog) records).1,
        (QueueReplay.replay capacity (score, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => rfl
  | cons record rest ih =>
      change QueueReplay.replay capacity
          (QueueReplay.transition capacity (offset + score, backlog) record) rest =
        (offset + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, backlog) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (score, backlog) record) rest).2)
      have hleft := CollectionKnownQueueContinuation.queueReplay_transition_add_score
        capacity (offset + score) backlog record
      have hright := CollectionKnownQueueContinuation.queueReplay_transition_add_score
        capacity score backlog record
      have hstep : QueueReplay.transition capacity (offset + score, backlog) record =
          (offset + (QueueReplay.transition capacity (score, backlog) record).1,
            (QueueReplay.transition capacity (score, backlog) record).2) := by
        rw [hleft, hright]
        apply Prod.ext
        · omega
        · rfl
      rw [hstep]
      exact ih (QueueReplay.transition capacity (score, backlog) record).1
        (QueueReplay.transition capacity (score, backlog) record).2

private theorem replay_score_mono (capacity : ℕ) (initial : ℕ × ℕ)
    (records : List (Bool × ℕ)) :
    initial.1 ≤ (QueueReplay.replay capacity initial records).1 := by
  induction records generalizing initial with
  | nil => exact le_rfl
  | cons record rest ih =>
      change initial.1 ≤
        (QueueReplay.replay capacity
          (QueueReplay.transition capacity initial record) rest).1
      have hstepMono : initial.1 ≤
          (QueueReplay.transition capacity initial record).1 := by
        cases record with
        | mk enabled arrival =>
            change initial.1 ≤
              (QueueReplay.transition capacity (initial.1, initial.2)
                (enabled, arrival)).1
            have h := congrArg Prod.fst
              (CollectionKnownQueueContinuation.queueReplay_transition_add_score
                capacity initial.1 initial.2 (enabled, arrival))
            rw [h]
            exact Nat.le_add_right _ _
      exact le_trans hstepMono (ih (QueueReplay.transition capacity initial record))

private theorem take_pos_split {α : Type} (records : List α) (n : ℕ)
    (hn : 0 < n) (hlen : n ≤ records.length) :
    records.take n = records[0]'(by
      cases records with
      | nil => simp at hlen; omega
      | cons first rest => simp) ::
      (records.take n).drop 1 := by
  cases records with
  | nil => simp at hlen; omega
  | cons first rest =>
      cases n with
      | zero => omega
      | succ n => simp

private theorem drop_tail_take_drop
    {α : Type} (records : List α) (n : ℕ)
    (hlen : records.length = n + 1) :
    ((records.take n).drop 1).dropLast = (records.take (n - 1)).drop 1 := by
  rw [List.dropLast_drop_eq_drop_dropLast,
    List.dropLast_take_eq_take_dropLast, List.dropLast_eq_take]
  simp [List.take_take, hlen]

private theorem replay_last_service_eq_score_delta_of_ne_nil
    (capacity : ℕ) (initial : ℕ × ℕ) (retained : ℕ)
    (records : List (Bool × ℕ)) (hne : records ≠ []) :
    CollectionKnownQueueContinuation.replayLastService capacity initial retained records =
      (QueueReplay.replay capacity initial records).1 -
        (QueueReplay.replay capacity initial records.dropLast).1 := by
  let last := records.getLast hne
  have hlast : records.getLast? = some last :=
    List.getLast?_eq_getLast_of_ne_nil hne
  calc
    CollectionKnownQueueContinuation.replayLastService capacity initial retained records =
        (QueueReplay.transition capacity
          (QueueReplay.replay capacity initial records.dropLast) last).1 -
          (QueueReplay.replay capacity initial records.dropLast).1 := by
      simp [CollectionKnownQueueContinuation.replayLastService, hlast, last]
    _ = (QueueReplay.replay capacity initial records).1 -
          (QueueReplay.replay capacity initial records.dropLast).1 := by
      rw [← List.dropLast_append_getLast hne, QueueReplay.replay_append]
      simp [QueueReplay.replay, last]

private theorem roundInput_ext {K : ℕ} (left right : RecordedQueueRun.RoundInput K)
    (henabled : left.enabled = right.enabled)
    (harm : left.recordedArm = right.recordedArm)
    (hreward : left.reward = right.reward) (hrate : left.rate = right.rate) :
    left = right := by
  cases left
  cases right
  cases henabled
  cases harm
  cases hreward
  cases hrate
  rfl

private theorem sourceCell_disabled (rate : RateInput p)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (rewards : RewardTable p)
    (valid : CoordinatorRecorderComplementBridge.LocalInputsValid
      (ReferenceActivePhysicalStep.collectionRecordingInput record.output.preparation
        call.payload call.started call.weights))
    (henabled : (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record call rewards valid).enabled = false) :
    (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record call rewards valid).recordedArm = none := by
  dsimp only [ReferenceFirstCollectionCheckedSourcePrefix.sourceCell] at henabled ⊢
  rw [henabled]
  exact SnapshotRecordingKernel.recordingMap_disabled _ _ _ _ _ _ _ _ _ _ _ _

private theorem local_record_eq_source_cell (rate : RateInput p)
    (ledger : ReferenceActivePhysicalStep.Ledger rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (cell : RecordedQueueRun.RoundInput p.K) (arm : Fin p.K)
    (henabled : ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time =
      cell.enabled)
    (hphysical : ReferenceCollectionRawBufferHistory.physicalQueueRecord ledger arm record =
      (cell.enabled, RecordedQueueRun.quantizedArrival
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm))
    (hdisabled : cell.enabled = false → cell.recordedArm = none) :
    CoordinatorCollectionLedger.localQueueRecord ledger record.input.time cell.enabled
      (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm =
        (cell.enabled, RecordedQueueRun.quantizedArrival
          (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm) := by
  cases he : cell.enabled with
  | false =>
      have hzero := RecordedQueueRun.quantizedArrival_eq_zero
        (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm (by
          rw [hdisabled he]
          simp)
      simp [CoordinatorCollectionLedger.localQueueRecord, hzero]
  | true =>
      have hbefore : record.input.time.val + 1 < ledger.freezeAt := by
        have hfst := congrArg Prod.fst hphysical
        simpa [ReferenceCollectionRawBufferHistory.physicalQueueRecord,
          henabled, he] using hfst
      have harrival : CoordinatorCollectionLedger.localArrival
          (ReferenceCollectionRawBufferHistory.rawDiagnostic record) arm =
            RecordedQueueRun.quantizedArrival
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) cell arm := by
        have hsnd := congrArg Prod.snd hphysical
        simpa [ReferenceCollectionRawBufferHistory.physicalQueueRecord, hbefore] using hsnd
      simp [CoordinatorCollectionLedger.localQueueRecord,
        CoordinatorCollectionLedger.sourceRound, hbefore, harrival]

variable (rate : RateInput p) (source : SourceInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ)
    (hc : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (count : ℕ)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed +
          count ≤ p.T)
    (hshort : (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan).length < count)

include hshort

/-- The actual first-collection checked prefix, together with the known-arm
score and service splice through the current arm-choice query.  The current
round facts concern only the pure `startRoundCandidate`. -/
theorem actual_first_collection_known_source_splice
    (j : Fin ((ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
        rate source rewards C_star C_h hc count hspan).records
      (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
        rate source rewards C_star C_h hc count hspan).length).length))
    (hj : 0 < j.val) (call : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstWindowNumericalStream.actualFirstLiveRun
          rate source rewards C_star C_h hc count hspan).records
        (ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
          rate source rewards C_star C_h hc count hspan).length)[j].input = some call)
    (a : CanonicalFastSampling.FastArm call.payload.slowSet) :
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    let E := ReferenceFirstWindowNumericalStream.actualFirstLiveRun
      rate source rewards C_star C_h hc count hspan
    let L := ReferenceFirstWindowNumericalStream.actualFirstLiveWindow
      rate source rewards C_star C_h hc count hspan
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records L.length
    let cells := ReferenceFirstWindowNumericalStream.actualLiveSourceCells
      rate source rewards C_star C_h hc count hspan
    let qpar := ReferenceFirstLaunchNumericalCell.queueParameters rate
    ∃ (cut : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
      (suffix : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
      (r : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (q : CoordinatorLiveServiceFinish.OwnedRegisters r)
      (base : Fin (p.m - 1) → ℕ)
      (head : ReferenceCollectionSegmentExtraction.Choice rate)
      (f0 : ReferenceActivePhysicalStep.Ledger rate)
      (proposal : Option (Fin p.T × Bool)),
      E.records[L.length]? = some cut ∧ E.records = L ++ cut :: suffix ∧
      B = cut :: suffix.takeWhile (fun record =>
        !ReferenceCollectionPhaseHistory.laterChosen record.input) ∧
      cut.input.state.coordinator = .live r q base ∧ head.payload = r.payload ∧
      head.initializer = some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt r cut.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt r q cut.input.time) base cut.input.time) ∧
      ReferenceCollectionSegmentExtraction.choice cut.input = some head ∧
      (∃ completed0 : ReferenceCollectionSegmentExtraction.CompletedRound rate,
        ReferenceCollectionSegmentExtraction.extractRound cut = some completed0 ∧
        completed0.context = head ∧ completed0.final = f0 ∧
        CollectionCheckedExecution.checkedRounds head.preLedger [completed0.input] =
          some ([completed0.accepted], f0)) ∧
      cut.output.next.coordinator = .collection r.payload f0 proposal ∧
      ∃ (headValid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput cut.output.preparation
          head.payload head.started head.weights))
        (present : ∀ k : Fin j.val,
          (ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
            (B[k.val + 1]'(by
              have hjB : j.val < B.length := j.isLt
              have hk := k.isLt
              omega))).isSome = true),
      let l0 := head.preLedger
      let c_u := ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate cut head rewards headValid
      let D := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix
        rate s B j c_u present
      let H := (B.take j.val).drop 1
      let Arr := fun X : List (RecordedQueueRun.RoundInput p.K) =>
        X.map (fun c => (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val))
      let R := fun h : ℕ => QueueReplay.replay (4 * rate.n) (0, 0)
        (Arr (cells ++ D.take h))
      let V := R 0
      D.length = j.val + 1 ∧
      D[0]'(by
        rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length
          rate s B j c_u present]
        omega) = c_u ∧
      (∀ k : Fin j.val,
        ReferenceLaterCollectionArrivalReadout.laterCollectionReadout s
          (B[k.val + 1]'(by
            have hk := k.isLt
            have hjB : j.val < B.length := j.isLt
            omega)) =
          some (D[k.val + 1]'(by
            rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length
              rate s B j c_u present]
            have hk := k.isLt
            omega))) ∧
      call.payload = r.payload ∧ call.initializer = none ∧
      CollectionBufferProvenance.collectionContext f0 =
        CollectionBufferProvenance.collectionContext l0 ∧
      ReferenceActivePhysicalHorizon.Connected cut.output.next H B[j].input.state ∧
      CollectionCheckedExecution.checkedRounds f0
        (ReferenceCollectionSegmentExtraction.inputs H) =
          some (ReferenceCollectionSegmentExtraction.acceptances H, call.preLedger) ∧
      H.length = j.val - 1 ∧
      (ReferenceCollectionSegmentExtraction.inputs H).length = H.length ∧
      ((D.take j.val).drop 1).length = H.length ∧
      (∀ k : Fin H.length, H[k] = B[k.val + 1]'(by
        have hk := k.isLt
        have hjB : j.val < B.length := j.isLt
        have hlen : H.length = j.val - 1 := by
          simp only [H, List.length_drop, List.length_take]
          omega
        omega)) ∧
      (∀ arm : Fin p.K,
        CollectionKnownQueueContinuation.inputQueueRecords f0 arm
          (ReferenceCollectionSegmentExtraction.inputs H) =
          ((D.take j.val).drop 1).map (fun cell =>
            (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell arm))) ∧
      ∃ oldLast,
        l0.cutoffRegisters a.val = some ⟨V.1, V.2, oldLast⟩ ∧
        call.preLedger.cutoffRegisters a.val = l0.cutoffRegisters a.val ∧
        call.preLedger.currentRegisters a.val = some ⟨(R j.val).2,
          (R j.val).1 - (R (j.val - 1)).1⟩ ∧
        call.preLedger.increment a.val = (R j.val).1 - V.1 ∧
        V.1 + call.preLedger.increment a.val = (R j.val).1 ∧
        let x := B[j].input
        let cand := CoordinatorCollectionLedger.startRoundCandidate call.preLedger x.time
          (ReferenceActivePhysicalStep.collectionEnabled call.preLedger x.time)
          (ReferenceCollectionRawBufferHistory.rawDiagnostic B[j])
        cand.cutoffRegisters a.val = l0.cutoffRegisters a.val ∧
        cand.increment a.val = call.preLedger.increment a.val ∧
        cand.currentRegisters a.val = some ⟨(R (j.val + 1)).2,
          (R (j.val + 1)).1 - (R j.val).1⟩ ∧
        cand.gammaLoc a.val = (R (j.val + 1)).1 - (R j.val).1 ∧
        V.1 + cand.increment a.val + cand.gammaLoc a.val = (R (j.val + 1)).1 ∧
        R (j.val + 1) = QueueReplay.transition (4 * rate.n) (R j.val)
          (ReferenceActivePhysicalStep.collectionEnabled call.preLedger x.time,
            RecordedQueueRun.quantizedArrival qpar
              (D[j.val]'(by
                rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length
                  rate s B j c_u present]
                omega)) a.val) ∧
        QueueReplay.transition (4 * rate.n) (R j.val) (false, 0) = R j.val ∧
        (ReferenceActivePhysicalStep.collectionEnabled call.preLedger x.time = false →
          cand.currentRegisters a.val = some ⟨(R j.val).2, 0⟩ ∧
          cand.gammaLoc a.val = 0) ∧
        (ReferenceActivePhysicalStep.collectionEnabled call.preLedger x.time = true →
          RecordedQueueRun.quantizedArrival qpar
            (D[j.val]'(by
              rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length
                rate s B j c_u present]
              omega)) a.val = 0 →
          QueueReplay.transition (4 * rate.n) (R j.val) (true, 0) =
            ((R j.val).1 + min (4 * rate.n) (R j.val).2,
              (R j.val).2 - min (4 * rate.n) (R j.val).2) ∧
          cand.gammaLoc a.val = min (4 * rate.n) (R j.val).2 ∧
          cand.currentRegisters a.val = some
            ⟨(R j.val).2 - min (4 * rate.n) (R j.val).2,
              min (4 * rate.n) (R j.val).2⟩) := by
  classical
  intro s E L B cells qpar
  let hprefix := ReferenceFirstCollectionCheckedSourcePrefix.actual_first_collection_checked_source_prefix
    rate source rewards C_star C_h hc count hspan hshort j hj call hchoice
  dsimp only at hprefix
  rcases hprefix with ⟨cutA, suffixA, rA, qA, baseA, headA, f0A, proposalA,
    hindexA, hrecordsA, hwindowA, hstateA, hpayloadA, hinitializerA, hchoiceA,
    hcompletedA, hnextA, headValid, present, hrestA⟩
  rcases hrestA with ⟨hDlength, hDzero, hcallPayload, hinitializerCall,
    hcontextF0, hconnected, hcheckedFold, hHlength, hinputsLength,
    hDtailLength, hHget, hAllChoices, hprefixQueueRecords⟩

  let hknown := ReferenceFirstCutoffKnownNumericalState.actual_first_cutoff_known_numerical_state
    rate source rewards C_star C_h hc count hspan hshort
  rcases hknown with ⟨cutK, suffixK, rK, qK, baseK, dispatched, hstart,
    ledger, hinit, hledger, hdomain, hclock, hpending, hnoAssignment,
    selected, out, hKrest⟩
  rcases hKrest with ⟨hcutK, hrecordsK, hphysicalCutK, htimeK, hrowsK,
    hselectedK, hrewardsK, hsigmaK, hnK, hbaseZeroK, hstateK, hprepK,
    huK, huBoundK, huGridK, hledgerCutoffK, hkposK, hpayloadsK, hKtail⟩
  dsimp only at hKtail
  rcases hKtail with ⟨hcuEnabled, hcuArm, hcuReward, hcuRate, henabledK,
    hrecorderK, hcutRecordingK, hnoGateK, hrawDiagnosticK, hzeroDiagnosticK,
    hslotK, hlocalArrivalK, hphysicalQueueK, hdisabledK, hboundaryK,
    hcellLengthK, hslowUnknownK, hstartedExistsK⟩
  rcases hstartedExistsK with ⟨ledgerStarted, hstageOneK, hstartedCandidateK,
    hfastKnownK, hstartedUnknownK, hrawBufferK, hreceiverK⟩
  rcases hreceiverK with ⟨inputK, diagnosticK, hinputK, hinputLedgerK,
    hinputDomainK, hinputCheckK, hrawParsedK, hfilteredK, hparsedK, hreceiveK,
    hdiagSomeK, hdiagInputK, hdiagRawK, hdiagParsedK, hdiagExpectedK,
    hdiagDecoderK, hdiagAcceptedK, hdiagMatchesK, hdiagWrongK, hbankOtherK,
    hbankEqK, hbatchCompletedK, hbatchPendingK, hfinishedDataK⟩
  rcases hfinishedDataK with ⟨f0K, hfinishK, hfinishedCandidateK,
    hfinishedCutoffRegistersK, hfinishedKnownK, hfinishedUnknownK,
    hconfigurationK, hnextCoordinatorK, hnextBankK, hcoordinatorBankK,
    hfailureNoneK, hrecordingFinalK, hupFinalK⟩

  have hbound : L.length < E.records.length := by
    have hlen : E.records.length = L.length + (suffixA.length + 1) := by
      rw [hrecordsA, List.length_append, List.length_cons]
    rw [hlen]
    omega
  have hcutAAt : cutA = E.records[L.length]'hbound := by
    have h := hindexA
    rw [List.getElem?_eq_getElem hbound] at h
    exact (Option.some.inj h).symm
  have hcutKAt : cutK = E.records[L.length]'hbound := by
    simpa only [E, L] using hcutK
  have hcutEq : cutA = cutK := hcutAAt.trans hcutKAt.symm
  have hstateEq : cutA.input.state.coordinator = cutK.input.state.coordinator :=
    congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord
      (p := p) (rate := rate) => record.input.state.coordinator) hcutEq
  rw [hstateA, hstateK] at hstateEq
  have hrEq : rA = rK := by
    injection hstateEq with hreg _ _
  subst rA
  have hqEq : qA = qK := by
    injection hstateEq with _ howned _
  have hbaseEq : baseA = baseK := by
    injection hstateEq with _ _ hbase
  subst qA
  subst baseA
  rw [hcutEq] at hconnected
  rw [hcutEq] at hrecordsA
  rw [hcutEq] at hwindowA

  let l0K := ReferenceActivePhysicalStep.sharedLedger ledger
  have hprepCut : (ReferenceActivePhysicalStep.prepare cutK.input).coordinator =
      .live rK qK baseK (.cutoffChosen dispatched hstart ledger hinit hledger
        hdomain hclock hpending hnoAssignment selected) := by
    have h := hprepK
    rw [cutK.output_eq] at h
    simpa [ReferenceActivePhysicalStep.step, ReferenceActivePhysicalStep.prepare] using h
  let headChoiceK : ReferenceCollectionSegmentExtraction.Choice rate :=
    ⟨rK.payload, l0K, dispatched.startResult,
      (ReferenceActivePhysicalStep.liveRegistersAt rK cutK.input.time).complementWeights,
      some (ReferenceCollectionSegmentExtraction.cutoffInitializer
        (ReferenceActivePhysicalStep.liveRegistersAt rK cutK.input.time)
        (ReferenceActivePhysicalStep.liveOwnedAt rK qK cutK.input.time)
        baseK cutK.input.time)⟩
  have hchoiceK : ReferenceCollectionSegmentExtraction.choice cutK.input =
      some headChoiceK := by
    unfold ReferenceCollectionSegmentExtraction.choice
    simp [hprepCut, headChoiceK, l0K, ReferenceCollectionSegmentExtraction.choiceOfCut,
      ReferenceActivePhysicalStep.DispatchCut.selection,
      ReferenceActivePhysicalStep.selectionAt]
  have hchoiceAAtK : ReferenceCollectionSegmentExtraction.choice cutK.input =
      some headA := by
    simpa [hcutEq] using hchoiceA
  have hheadEq : headChoiceK = headA :=
    Option.some.inj (hchoiceK.symm.trans hchoiceAAtK)
  have hnextKFromA : cutK.output.next.coordinator =
      .collection rK.payload f0A proposalA := by
    rw [hcutEq] at hnextA
    exact hnextA
  have hf0Eq : f0A = f0K := by
    have hcfg := hnextKFromA.symm.trans hnextCoordinatorK
    injection hcfg with _ hf _

  subst cutA
  subst headA
  subst f0A
  rw [← hcutKAt] at hstateA hinitializerA hchoiceA hcompletedA hnextA

  let fastArmK : CanonicalFastSampling.FastArm rK.payload.slowSet := by
    have hslow := congrArg
      (fun payload : ReferenceActivePhysicalStep.Payload rate => payload.slowSet)
      hcallPayload
    refine ⟨a.val, ?_⟩
    rw [← hslow]
    exact a.property

  specialize hfastKnownK fastArmK
  rcases hfastKnownK with ⟨hlocalQueueK, hcutoffArmK, hcurrentArmK,
    hincrementArmK, hstartedCurrentArmK, hgammaArmK, hstartedIncArmK,
    hstartedReplayK, henabledZeroK, hdisabledArmK⟩
  specialize hfinishedKnownK fastArmK
  rcases hfinishedKnownK with ⟨hfinishIncrementArmK, hfinishCurrentArmK,
    hfinishTotalArmK, hfinishDisabledArmK⟩

  let tK := cutK.input.time
  let weightsK := (ReferenceActivePhysicalStep.liveRegistersAt rK tK).complementWeights
  let recordingInputK := ReferenceActivePhysicalStep.collectionRecordingInput
    cutK.output.preparation rK.payload dispatched.startResult weightsK
  let localValidK : CoordinatorRecorderComplementBridge.LocalInputsValid recordingInputK :=
    ⟨selected.recorderBoundaryValid, fun i =>
      ⟨selected.choiceInputsValid.anchor_le_current i,
        selected.choiceInputsValid.current_le_twice_anchor i⟩⟩
  have hvalidEq : headValid = localValidK := Subsingleton.elim _ _
  subst headValid
  let hvK := CoordinatorRecorderComplementBridge.recorderInput_inputsValid
    recordingInputK localValidK
  let eK := ReferenceActivePhysicalStep.collectionEnabled l0K tK
  let cellK : RecordedQueueRun.RoundInput p.K := {
    enabled := eK
    recordedArm := SnapshotRecordingKernel.recordingMap p .collection eK
      (CoordinatorRecorderComplementBridge.recorderInput recordingInputK).eta
      hvK.eta_pos hvK.eta_source_cap
      (CoordinatorRecorderComplementBridge.recorderInput recordingInputK).anchor
      (CoordinatorRecorderComplementBridge.recorderInput recordingInputK).currentWeights
      hvK.anchor_pos hvK.current_pos hvK.anchor_le_current hvK.current_le_twice_anchor
      (cutK.input.row.2 tK).1
    reward := fun arm => ((rewards tK arm).val : ℝ) / (ConstructorDimensions.D p : ℝ)
    rate := rK.payload.rate
    reward_nonneg := fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    reward_le_one := by
      intro arm
      apply (div_le_one (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))).2
      exact_mod_cast Nat.le_of_lt_succ (rewards tK arm).isLt
    rate_pos := fun arm =>
      (CanonicalRecordingRates.beta_pos p rate.eta.property).trans_le
        (rK.payload.beta_le_rate arm) }

  let l0 := headChoiceK.preLedger
  let c_u := ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
    rate cutK headChoiceK rewards localValidK
  let D := ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix
    rate s B j c_u present
  let H := (B.take j.val).drop 1
  let Arr := fun X : List (RecordedQueueRun.RoundInput p.K) =>
    X.map (fun c => (c.enabled, RecordedQueueRun.quantizedArrival qpar c a.val))
  let R := fun h : ℕ => QueueReplay.replay (4 * rate.n) (0, 0)
    (Arr (cells ++ D.take h))
  let V := R 0

  have hsourceCellIndex :
      ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate cutK headChoiceK rewards localValidK =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate E.records[L.length] headChoiceK rewards localValidK :=
    congrArg (fun record => ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
      rate record headChoiceK rewards localValidK) hcutKAt
  have hD_eq_index : D =
      ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix rate s B j
        (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate E.records[L.length] headChoiceK rewards localValidK) present :=
    congrArg (fun cell => ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix
      rate s B j cell present) hsourceCellIndex
  have hDlengthK : D.length = j.val + 1 := by
    have h := hDlength
    rw [← hD_eq_index] at h
    exact h
  have hDzeroK : D[0]'(by rw [hDlengthK]; omega) = c_u := by
    simp [D, ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix]
  have hDtailLengthK : ((D.take j.val).drop 1).length = H.length := by
    simp only [H, List.length_drop, List.length_take]
    rw [ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_length
      rate s B j c_u present]
    rw [Nat.min_eq_left (by omega : j.val ≤ j.val + 1),
      Nat.min_eq_left (Nat.le_of_lt j.isLt)]

  have hcellEq :
      cellK = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate cutK headChoiceK rewards localValidK := by
    apply roundInput_ext
    · rfl
    · rfl
    · rfl
    · rfl

  let dcell := D[0]'(by
    rw [hDlengthK]
    omega)
  have hDheadCell : dcell = cellK := by
    have hzero : dcell =
        ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
          rate cutK headChoiceK rewards localValidK := by
      simpa [dcell] using hDzeroK
    exact hzero.trans hcellEq.symm

  let Dtail := (D.take j.val).drop 1
  let tailRecords := Dtail.map (fun cell =>
    (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val))
  have hDtakeOne : D.take 1 = [dcell] := by
    simp [dcell, D, ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix]
  have hcutoffReplayK : R 1 =
      QueueReplay.replay (4 * rate.n) (0, 0)
        ((cells ++ [cellK]).map (fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val))) := by
    dsimp [R, Arr]
    rw [hDtakeOne]
    simp only [List.map_append, List.map_cons, List.map_nil,
      hDheadCell]
  have hR1d : R 1 = QueueReplay.replay (4 * rate.n) (0, 0)
      (Arr (cells ++ [dcell])) := by
    dsimp [R]
    rw [hDtakeOne]
  have hKbase :
      QueueReplay.replay (4 * rate.n) (0, 0)
        ((cells ++ [cellK]).map (fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val))) =
        QueueReplay.transition (4 * rate.n)
          (QueueReplay.replay (4 * rate.n) (0, 0)
            (cells.map (fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val))))
          (eK, RecordedQueueRun.quantizedArrival qpar cellK a.val) := by
    have h := hstartedReplayK
    simpa [cellK, eK, qpar, fastArmK, List.map_append] using h
  have hV : V =
      QueueReplay.replay (4 * rate.n) (0, 0)
        (cells.map (fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val))) := by
    simp [V, R, Arr]
  have hVplus : R 1 =
      QueueReplay.transition (4 * rate.n) V
        (eK, RecordedQueueRun.quantizedArrival qpar cellK a.val) := by
    rw [hcutoffReplayK, hKbase, hV]

  have hsourceDsplit : D.take j.val =
      [dcell] ++ Dtail := by
    have h := take_pos_split D j.val hj (by rw [hDlengthK]; omega)
    simpa [dcell, Dtail] using h
  have hRsplit : R j.val =
      QueueReplay.replay (4 * rate.n) (R 1) tailRecords := by
    have hlist : cells ++ D.take j.val = (cells ++ [dcell]) ++ Dtail := by
      rw [hsourceDsplit, ← List.append_assoc]
    calc
      R j.val = QueueReplay.replay (4 * rate.n) (0, 0)
          (Arr (cells ++ D.take j.val)) := rfl
      _ = QueueReplay.replay (4 * rate.n) (0, 0)
          (Arr ((cells ++ [dcell]) ++ Dtail)) := by rw [hlist]
      _ = QueueReplay.replay (4 * rate.n)
          (QueueReplay.replay (4 * rate.n) (0, 0) (Arr (cells ++ [dcell])))
          (Arr Dtail) := by
            dsimp [Arr]
            rw [List.map_append, QueueReplay.replay_append]
      _ = QueueReplay.replay (4 * rate.n) (R 1) tailRecords := by
            rw [← hR1d]

  have hfastCutoff : l0K.cutoffRegisters a.val =
      some ⟨V.1, V.2, qK.previousService fastArmK⟩ := by
    simpa [hV, qpar] using hcutoffArmK
  have hfastInitialCurrent : l0K.currentRegisters a.val =
      some ⟨V.2, qK.previousService fastArmK⟩ := by
    simpa [hV, qpar] using hcurrentArmK
  have hfastFoldCurrent : f0K.currentRegisters a.val =
      some ⟨(R 1).2, (R 1).1 - V.1⟩ := by
    have h := hfinishCurrentArmK
    rw [← hKbase, ← hcutoffReplayK] at h
    simpa [hV] using h
  have hfastFoldIncrement : f0K.increment a.val = (R 1).1 - V.1 := by
    have h := hfinishIncrementArmK
    rw [← hKbase, ← hcutoffReplayK] at h
    simpa [hV] using h
  have hscoreOffset : V.1 + f0K.increment a.val = (R 1).1 := by
    have h := hfinishTotalArmK
    rw [hfastCutoff, ← hKbase, ← hcutoffReplayK] at h
    simpa [hV] using h

  have hqueueRecords : ∀ arm : Fin p.K,
      CollectionKnownQueueContinuation.inputQueueRecords f0K arm
          (ReferenceCollectionSegmentExtraction.inputs H) =
        ((D.take j.val).drop 1).map (fun cell =>
          (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell arm)) := by
    have h := hprefixQueueRecords
    rw [← hsourceCellIndex] at h
    simpa [H, D, c_u, s, B] using h
  have hfold := CollectionKnownQueueContinuation.checkedRounds_known_queue_continuation
    f0K call.preLedger a.val
    ⟨(R 1).2, (R 1).1 - V.1⟩
    (ReferenceCollectionSegmentExtraction.inputs H)
    (ReferenceCollectionSegmentExtraction.acceptances H)
    hfastFoldCurrent hcheckedFold
  dsimp only at hfold
  rcases hfold with ⟨hcurrentFinal, hincrementFinal, hassignmentFinal,
    hsigmaFinal, hcutoffFinal, hfreezeFinal, hcutoffRegisterFinal⟩

  have hscoreOffsetA : V.1 + f0K.increment a.val = (R 1).1 := hscoreOffset
  let tailReplay := QueueReplay.replay (4 * rate.n)
    (f0K.increment a.val, (R 1).2) tailRecords
  have hinitScore : R 1 = (V.1 + f0K.increment a.val, (R 1).2) := by
    apply Prod.ext
    · exact hscoreOffsetA.symm
    · rfl
  have hshiftedReplay : R j.val = (V.1 + tailReplay.1, tailReplay.2) := by
    rw [hRsplit]
    have hshift := replay_add_score_offset (4 * rate.n) V.1
      (f0K.increment a.val) (R 1).2 tailRecords
    rw [hinitScore]
    simpa [tailReplay] using hshift

  have hcurrentFinalRecords := hcurrentFinal
  rw [hqueueRecords a.val] at hcurrentFinalRecords
  have hcurrentFinalTail : call.preLedger.currentRegisters a.val =
      some ⟨(QueueReplay.replay (4 * rate.n)
          (f0K.increment a.val, (R 1).2) tailRecords).2,
        CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
          (f0K.increment a.val, (R 1).2) ((R 1).1 - V.1) tailRecords⟩ := by
    exact hcurrentFinalRecords
  have htailLength : tailRecords.length = j.val - 1 := by
    have hjle : j.val ≤ D.length := by rw [hDlengthK]; omega
    simp [tailRecords, Dtail, List.length_map, List.length_take,
      Nat.min_eq_left hjle]
  have hfinalCurrent : call.preLedger.currentRegisters a.val =
      some ⟨(R j.val).2,
        (R j.val).1 - (R (j.val - 1)).1⟩ := by
    cases hjval : j.val with
    | zero => omega
    | succ n =>
        by_cases hnzero : n = 0
        · subst n
          have htailNil : tailRecords = [] := by
            apply List.eq_nil_of_length_eq_zero
            rw [htailLength]
            omega
          have hlast : CollectionKnownQueueContinuation.replayLastService
              (4 * rate.n) (f0K.increment a.val, (R 1).2)
              ((R 1).1 - V.1) tailRecords = (R 1).1 - (R 0).1 := by
            simp [htailNil, CollectionKnownQueueContinuation.replayLastService, V]
          rw [hcurrentFinalTail]
          apply congrArg some
          simp only [CoordinatorCollectionLedger.CurrentRegister.mk.injEq]
          constructor
          · simpa [hjval, tailReplay, htailNil] using
              (congrArg Prod.snd hshiftedReplay).symm
          · simpa [hjval, htailNil] using hlast
        · have htailNonempty : tailRecords ≠ [] := by
            intro he
            have hlen := congrArg List.length he
            simp only [List.length_nil] at hlen
            rw [htailLength] at hlen
            omega
          have hlast := replay_last_service_eq_score_delta_of_ne_nil
            (4 * rate.n) (f0K.increment a.val, (R 1).2)
            ((R 1).1 - V.1) tailRecords htailNonempty
          have htailDropLast := drop_tail_take_drop D j.val hDlengthK
          have hrecordsDropLast : tailRecords.dropLast =
              ((D.take (j.val - 1)).drop 1).map (fun cell =>
                (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val)) := by
            change (Dtail.map (fun cell =>
              (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell a.val))).dropLast = _
            rw [List.dropLast_eq_take, List.length_map, ← List.map_take,
              ← List.dropLast_eq_take, htailDropLast]
          have hprevCells : D.take (j.val - 1) =
              [dcell] ++ (D.take (j.val - 1)).drop 1 := by
            have htake := take_pos_split D (j.val - 1) (by omega)
              (by rw [hDlengthK]; omega)
            simpa [dcell] using htake
          have hprevReplay : R (j.val - 1) =
              QueueReplay.replay (4 * rate.n) (R 1) tailRecords.dropLast := by
            have hprevList : cells ++ D.take (j.val - 1) =
                (cells ++ [dcell]) ++ (D.take (j.val - 1)).drop 1 := by
              calc
                cells ++ D.take (j.val - 1) =
                    cells ++ ([dcell] ++ (D.take (j.val - 1)).drop 1) :=
                      congrArg (List.append cells) hprevCells
                _ = (cells ++ [dcell]) ++ (D.take (j.val - 1)).drop 1 := by
                    exact (List.append_assoc cells [dcell]
                      ((D.take (j.val - 1)).drop 1)).symm
            calc
              R (j.val - 1) = QueueReplay.replay (4 * rate.n) (0, 0)
                  (Arr (cells ++ D.take (j.val - 1))) := rfl
              _ = QueueReplay.replay (4 * rate.n) (0, 0)
                  (Arr ((cells ++ [dcell]) ++ (D.take (j.val - 1)).drop 1)) := by
                    rw [hprevList]
              _ = QueueReplay.replay (4 * rate.n)
                  (QueueReplay.replay (4 * rate.n) (0, 0) (Arr (cells ++ [dcell])))
                  (Arr ((D.take (j.val - 1)).drop 1)) := by
                    dsimp [Arr]
                    rw [List.map_append, QueueReplay.replay_append]
              _ = QueueReplay.replay (4 * rate.n) (R 1) tailRecords.dropLast := by
                    rw [← hR1d]
                    apply congrArg (QueueReplay.replay (4 * rate.n) (R 1))
                    dsimp [Arr]
                    exact hrecordsDropLast.symm
          let prefixReplay := QueueReplay.replay (4 * rate.n)
            (f0K.increment a.val, (R 1).2) tailRecords.dropLast
          have hprevShifted : R (j.val - 1) =
              (V.1 + prefixReplay.1, prefixReplay.2) := by
            rw [hprevReplay]
            have hshift := replay_add_score_offset (4 * rate.n) V.1
              (f0K.increment a.val) (R 1).2 tailRecords.dropLast
            rw [← hinitScore] at hshift
            simpa [prefixReplay] using hshift
          let last := tailRecords.getLast htailNonempty
          have hsplit : tailRecords.dropLast ++ [last] = tailRecords :=
            List.dropLast_append_getLast htailNonempty
          have hReplaySplit : QueueReplay.replay (4 * rate.n)
              (f0K.increment a.val, (R 1).2) tailRecords =
              QueueReplay.replay (4 * rate.n)
                (QueueReplay.replay (4 * rate.n)
                  (f0K.increment a.val, (R 1).2) tailRecords.dropLast) [last] := by
            calc
              QueueReplay.replay (4 * rate.n)
                  (f0K.increment a.val, (R 1).2) tailRecords =
                  QueueReplay.replay (4 * rate.n)
                    (f0K.increment a.val, (R 1).2)
                    (tailRecords.dropLast ++ [last]) :=
                      congrArg (QueueReplay.replay (4 * rate.n)
                        (f0K.increment a.val, (R 1).2)) hsplit.symm
              _ = QueueReplay.replay (4 * rate.n)
                    (QueueReplay.replay (4 * rate.n)
                      (f0K.increment a.val, (R 1).2) tailRecords.dropLast) [last] :=
                    QueueReplay.replay_append (4 * rate.n)
                      (f0K.increment a.val, (R 1).2) tailRecords.dropLast [last]
          have hprefixLe : prefixReplay.1 ≤ tailReplay.1 := by
            have h := replay_score_mono (4 * rate.n)
              (QueueReplay.replay (4 * rate.n)
                (f0K.increment a.val, (R 1).2) tailRecords.dropLast) [last]
            calc
              prefixReplay.1 ≤
                  (QueueReplay.replay (4 * rate.n) prefixReplay [last]).1 := by
                simpa [prefixReplay] using h
              _ = tailReplay.1 := by
                have hscoreSplit := congrArg Prod.fst hReplaySplit
                simpa [tailReplay, prefixReplay] using hscoreSplit.symm
          have hlastTarget :
              CollectionKnownQueueContinuation.replayLastService
                  (4 * rate.n) (f0K.increment a.val, (R 1).2)
                  ((R 1).1 - V.1) tailRecords =
                (R j.val).1 - (R (j.val - 1)).1 := by
            have htop := congrArg Prod.fst hshiftedReplay
            have hbottom := congrArg Prod.fst hprevShifted
            have hlastScore :
                CollectionKnownQueueContinuation.replayLastService
                    (4 * rate.n) (f0K.increment a.val, (R 1).2)
                    ((R 1).1 - V.1) tailRecords =
                  tailReplay.1 - prefixReplay.1 := by
              rw [hlast]
            rw [hlastScore, htop, hbottom]
            omega
          rw [hcurrentFinalTail]
          apply congrArg some
          simp only [CoordinatorCollectionLedger.CurrentRegister.mk.injEq]
          constructor
          · have hqueue := congrArg Prod.snd hshiftedReplay
            rw [hjval] at hqueue
            simpa only [tailReplay] using hqueue.symm
          · simpa only [hjval] using hlastTarget

  have hfinalIncrement : call.preLedger.increment a.val =
      (R j.val).1 - V.1 := by
    have hcallIncrement : call.preLedger.increment a.val = tailReplay.1 := by
      simpa [tailReplay, tailRecords, Dtail, hqueueRecords a.val] using hincrementFinal
    have hscore := congrArg Prod.fst hshiftedReplay
    omega

  have hinputQueueTail :
      CollectionKnownQueueContinuation.inputQueueRecords f0K a.val
          (ReferenceCollectionSegmentExtraction.inputs H) = tailRecords := by
    rw [hqueueRecords a.val]
  have hqueueFinal :
      (QueueReplay.replay (4 * rate.n)
        (f0K.increment a.val, (R 1).2)
        (CollectionKnownQueueContinuation.inputQueueRecords f0K a.val
          (ReferenceCollectionSegmentExtraction.inputs H))).2 = (R j.val).2 := by
    rw [hinputQueueTail]
    simpa [tailReplay] using (congrArg Prod.snd hshiftedReplay).symm
  have hcurrentForCandidate : call.preLedger.currentRegisters a.val =
      some ⟨(R j.val).2,
        CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
          (f0K.increment a.val, (R 1).2) ((R 1).1 - V.1)
          (CollectionKnownQueueContinuation.inputQueueRecords f0K a.val
            (ReferenceCollectionSegmentExtraction.inputs H))⟩ := by
    rw [← hqueueFinal]
    exact hcurrentFinal

  have hcutoffCall : call.preLedger.cutoffRegisters a.val =
      l0K.cutoffRegisters a.val := by
    rw [hfinishedCutoffRegistersK] at hcutoffRegisterFinal
    exact hcutoffRegisterFinal

  let recordCurrent : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) :=
    B[j.val]'j.isLt
  have hcellAtCurrent : ∃ cell : RecordedQueueRun.RoundInput p.K,
      ∃ valid : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput
          recordCurrent.output.preparation call.payload call.started call.weights),
      cell = D[j.val]'(by rw [hDlengthK]; omega) ∧
      cell = ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
        rate recordCurrent call rewards valid ∧
      cell.enabled = ReferenceActivePhysicalStep.collectionEnabled
        call.preLedger recordCurrent.input.time ∧
    (∀ arm, ReferenceCollectionRawBufferHistory.physicalQueueRecord
        call.preLedger arm recordCurrent =
          (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell arm)) := by
    let currentFin : Fin (j.val + 1) := ⟨j.val, Nat.lt_succ_self _⟩
    obtain ⟨callJ, validJ, hchoiceJ, hpayloadJ, hcontextJ, _, hsourceCellJ,
      _, _, _, _, henabledJ, _, _, _, houtJ, _, _⟩ := hAllChoices currentFin
    have hcallJ : callJ = call := by
      have hchoiceEq : ReferenceCollectionSegmentExtraction.choice
          recordCurrent.input = some callJ := by
            simpa [currentFin, recordCurrent] using hchoiceJ
      exact Option.some.inj (hchoiceEq.symm.trans hchoice)
    cases hcallJ
    have hvalidCurrent : CoordinatorRecorderComplementBridge.LocalInputsValid
        (ReferenceActivePhysicalStep.collectionRecordingInput
          recordCurrent.output.preparation call.payload call.started call.weights) := by
      simpa [currentFin, recordCurrent] using validJ
    have hcellTransport := List.getElem_of_eq hD_eq_index
      (by rw [hDlengthK]; omega : j.val < D.length)
    have hsourceCellCurrent :
        D[j.val]'(by rw [hDlengthK]; omega) =
          ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate recordCurrent call rewards hvalidCurrent := by
      exact hcellTransport.trans hsourceCellJ
    refine ⟨D[j.val]'(by rw [hDlengthK]; omega), ?_, rfl,
      hsourceCellCurrent, ?_, ?_⟩
    · exact hvalidCurrent
    · exact (congrArg RecordedQueueRun.RoundInput.enabled hcellTransport).trans henabledJ
    · intro arm
      obtain ⟨outJ, _, _, _, _, _, hphysicalJ, _, _⟩ := houtJ
      exact (hphysicalJ arm).trans (congrArg
        (fun cell : RecordedQueueRun.RoundInput p.K =>
          (cell.enabled, RecordedQueueRun.quantizedArrival qpar cell arm))
        hcellTransport.symm)
  rcases hcellAtCurrent with
    ⟨cellJ, validJ, hcellIndexJ, hsourceCellJ, henabledJ, hphysicalJ⟩

  let x := recordCurrent.input
  let enabledJ := ReferenceActivePhysicalStep.collectionEnabled call.preLedger x.time
  let rawJ := ReferenceCollectionRawBufferHistory.rawDiagnostic recordCurrent
  let cand := CoordinatorCollectionLedger.startRoundCandidate call.preLedger x.time
    enabledJ rawJ
  have hlocalCurrent : CoordinatorCollectionLedger.localQueueRecord
      call.preLedger x.time enabledJ rawJ a.val =
        (enabledJ, RecordedQueueRun.quantizedArrival qpar cellJ a.val) := by
    have hdisabled : cellJ.enabled = false → cellJ.recordedArm = none := by
      intro hf
      have hfsource :
          (ReferenceFirstCollectionCheckedSourcePrefix.sourceCell
            rate recordCurrent call rewards validJ).enabled = false := by
        rw [← hsourceCellJ]
        exact hf
      simpa [hsourceCellJ] using
        sourceCell_disabled rate recordCurrent call rewards validJ hfsource
    have hp := hphysicalJ a.val
    have he : ReferenceActivePhysicalStep.collectionEnabled call.preLedger x.time =
        cellJ.enabled := by simpa [x] using henabledJ.symm
    have hp' : ReferenceCollectionRawBufferHistory.physicalQueueRecord
        call.preLedger a.val recordCurrent =
          (cellJ.enabled, RecordedQueueRun.quantizedArrival qpar cellJ a.val) := by
      exact hp
    simpa [x, enabledJ, rawJ, he] using
      local_record_eq_source_cell rate call.preLedger recordCurrent cellJ a.val he hp' hdisabled

  have hRsucc : R (j.val + 1) =
      QueueReplay.transition (4 * rate.n) (R j.val)
        (enabledJ, RecordedQueueRun.quantizedArrival qpar cellJ a.val) := by
    have hjD : j.val < D.length := by rw [hDlengthK]; omega
    have htake := (List.take_append_getElem hjD).symm
    have hsplit : D.take (j.val + 1) = D.take j.val ++ [D[j.val]'hjD] := by
      simp only [htake]
    dsimp [R, Arr]
    rw [hsplit]
    simp only [List.map_append, List.map_singleton]
    rw [← List.append_assoc, QueueReplay.replay_append, ← hcellIndexJ]
    rw [henabledJ]
    rfl

  have htransitionAdd := CollectionKnownQueueContinuation.queueReplay_transition_add_score
    (4 * rate.n) (R j.val).1 (R j.val).2
      (enabledJ, RecordedQueueRun.quantizedArrival qpar cellJ a.val)
  have hzeroTransition :
      QueueReplay.transition (4 * rate.n) (0, (R j.val).2)
        (enabledJ, RecordedQueueRun.quantizedArrival qpar cellJ a.val) =
      ((R (j.val + 1)).1 - (R j.val).1, (R (j.val + 1)).2) := by
    apply Prod.ext
    · have hsum := congrArg Prod.fst hRsucc
      rw [htransitionAdd] at hsum
      omega
    · have hqueue := congrArg Prod.snd hRsucc
      rw [htransitionAdd] at hqueue
      exact hqueue.symm

  have hcandCurrent : cand.currentRegisters a.val =
      some ⟨(R (j.val + 1)).2, (R (j.val + 1)).1 - (R j.val).1⟩ := by
    have h := CoordinatorCollectionLedger.startRoundCandidate_known_transition
      call.preLedger x.time enabledJ rawJ a.val
      ⟨(R j.val).2,
        CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
          (f0K.increment a.val, (R 1).2)
          ((R 1).1 - V.1)
          (CollectionKnownQueueContinuation.inputQueueRecords f0K a.val
            (ReferenceCollectionSegmentExtraction.inputs H))⟩ hcurrentForCandidate
    rw [hlocalCurrent, hzeroTransition] at h
    simpa [cand, CoordinatorCollectionLedger.startRoundCandidate] using h

  have hcandGamma : cand.gammaLoc a.val =
      (R (j.val + 1)).1 - (R j.val).1 := by
    have hgammaRaw :
        (QueueReplay.transition (4 * rate.n) (0, (R j.val).2)
          (enabledJ, RecordedQueueRun.quantizedArrival qpar cellJ a.val)).1 =
            (R (j.val + 1)).1 - (R j.val).1 := by
      have hsum := congrArg Prod.fst hRsucc
      rw [htransitionAdd] at hsum
      omega
    calc
      cand.gammaLoc a.val =
          (QueueReplay.transition (4 * rate.n) (0, (R j.val).2)
            (CoordinatorCollectionLedger.localQueueRecord call.preLedger x.time enabledJ rawJ a.val)).1 := by
              simp [cand, CoordinatorCollectionLedger.startRoundCandidate,
                hfinalCurrent, hlocalCurrent]
      _ = (R (j.val + 1)).1 - (R j.val).1 := by
            rw [hlocalCurrent]
            exact hgammaRaw

  have hcandCutoff : cand.cutoffRegisters a.val = l0K.cutoffRegisters a.val := by
    simp [cand, CoordinatorCollectionLedger.startRoundCandidate, hcutoffCall]
  have hcandIncrement : cand.increment a.val = call.preLedger.increment a.val := by
    rfl
  have htotalNext : V.1 + cand.increment a.val + cand.gammaLoc a.val =
      (R (j.val + 1)).1 := by
    rw [hcandIncrement, hfinalIncrement, hcandGamma]
    have hVle : V.1 ≤ (R j.val).1 := by
      rw [hshiftedReplay]
      omega
    have hRle : (R j.val).1 ≤ (R (j.val + 1)).1 := by
      have hmono := congrArg Prod.fst hRsucc
      rw [htransitionAdd] at hmono
      omega
    omega

  have hdisabledCandidate : enabledJ = false →
      cand.currentRegisters a.val = some ⟨(R j.val).2, 0⟩ ∧
      cand.gammaLoc a.val = 0 := by
    intro hfalse
    have hstep : QueueReplay.transition (4 * rate.n) (R j.val) (false, 0) = R j.val := by
      rfl
    have hRsame : R (j.val + 1) = R j.val := by
      rw [hRsucc, hfalse]
      simp [QueueReplay.transition]
    constructor
    · rw [hcandCurrent, hRsame]
      simp
    · rw [hcandGamma, hRsame]
      simp

  have henabledZero : enabledJ = true →
      RecordedQueueRun.quantizedArrival qpar cellJ a.val = 0 →
      QueueReplay.transition (4 * rate.n) (R j.val) (true, 0) =
        ((R j.val).1 + min (4 * rate.n) (R j.val).2,
          (R j.val).2 - min (4 * rate.n) (R j.val).2) ∧
      cand.gammaLoc a.val = min (4 * rate.n) (R j.val).2 ∧
      cand.currentRegisters a.val = some
        ⟨(R j.val).2 - min (4 * rate.n) (R j.val).2,
          min (4 * rate.n) (R j.val).2⟩ := by
    intro hen hzero
    refine ⟨QueueReplay.transition_enabled_zero_arrival
      (4 * rate.n) (R j.val).1 (R j.val).2, ?_, ?_⟩
    · rw [hcandGamma, hRsucc, hen, hzero]
      simp [QueueReplay.transition]
    · rw [hcandCurrent, hRsucc, hen, hzero]
      simp [QueueReplay.transition]

  have hindexAligned : E.records[L.length]? = some cutK := by
    rw [List.getElem?_eq_getElem hbound]
    rw [← hcutKAt]
  have hrecordsAligned : E.records = L ++ cutK :: suffixA := by
    simpa only [E, L] using hrecordsA
  have hwindowAligned : B = cutK :: suffixA.takeWhile
      (fun record => !ReferenceCollectionPhaseHistory.laterChosen record.input) := by
    simpa only [B, E, L] using hwindowA
  have hconnectedAligned : ReferenceActivePhysicalHorizon.Connected
      cutK.output.next H B[j].input.state := by
    simpa only [B, E, L, H] using hconnected
  have hsumBase : V.1 + call.preLedger.increment a.val = (R j.val).1 := by
    have hVle : V.1 ≤ (R j.val).1 := by
      rw [hshiftedReplay]
      omega
    rw [hfinalIncrement]
    omega
  refine ⟨cutK, suffixA, rK, qK, baseK, headChoiceK, f0K, proposalA,
    hindexAligned, hrecordsAligned, hwindowAligned, hstateA, hpayloadA,
    hinitializerA, hchoiceA, hcompletedA, hnextA, localValidK, present,
    hDlengthK, hDzeroK,
    (fun k => ReferenceFirstCollectionCheckedSourcePrefix.readoutPrefix_readout
      rate s B j c_u present k), hcallPayload,
    hinitializerCall, hcontextF0, hconnectedAligned, hcheckedFold, hHlength,
    hinputsLength, hDtailLengthK, hHget, hqueueRecords, ?_⟩
  refine ⟨qK.previousService fastArmK, ?_, hcutoffCall, hfinalCurrent,
    hfinalIncrement, hsumBase, hcandCutoff, hcandIncrement, hcandCurrent, hcandGamma,
    htotalNext, ?_, rfl, hdisabledCandidate,
    ?_⟩
  · simpa [l0, V, hV] using hfastCutoff
  · simpa only [Fin.getElem_fin, enabledJ, x, recordCurrent, hcellIndexJ,
      R, Arr, D, c_u] using hRsucc
  · simpa [enabledJ, x, recordCurrent, D, E, L, B, c_u, s,
      hcellIndexJ, cand, R, Arr] using henabledZero

end Bandits.Support.ReferenceFirstCollectionKnownSourceSplice

end
