/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstAcceptedUpOnlineReplay
public import Bandits.Support.ReferenceCollectionUpReplayHistory

import Lean.Elab.Tactic.Omega

/-!
# First assignment numerical replay joined to one actual collection record

Sources: `sources/zip4/manuscript/06_interruptions.tex:80-100,192-233,246-295,301-344`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:34-64`, and
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`.

This internal result joins the zero-seeded sender-local replay of an actual
first-assignment accepted UP to the coordinator's actual collection segment
and the same accepted physical round. The final queue expression is the
literal concatenation of those two existing streams. It does not identify
that concatenation with the manuscript's source Delta/Gamma/B/Z sequence.
-/

@[expose] public section

noncomputable section

open Bandits.Support
open ConstructorDimensions
open ReferenceActivePhysicalStep
open ReferenceActivePhysicalHorizon
open ReferenceCollectionSegmentExtraction
open ReferenceCollectionPhaseHistory
open CoordinatorCollectionLedger
open ReferenceFirstAcceptedUpNumericSnapshot
open QueueReplay

namespace Bandits.Support.ReferenceFirstCollectionNumericalReplay

variable {p : ConstructorDimensions.Parameters}
variable {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem transition_add_score (capacity score backlog : ℕ)
    (record : Bool × ℕ) :
    QueueReplay.transition capacity (score, backlog) record =
      (score + (QueueReplay.transition capacity (0, backlog) record).1,
        (QueueReplay.transition capacity (0, backlog) record).2) := by
  cases record with
  | mk enabled arrival =>
      cases enabled <;> simp [QueueReplay.transition]

private theorem replay_add_score (capacity score backlog : ℕ)
    (records : List (Bool × ℕ)) :
    QueueReplay.replay capacity (score, backlog) records =
      (score + (QueueReplay.replay capacity (0, backlog) records).1,
        (QueueReplay.replay capacity (0, backlog) records).2) := by
  induction records generalizing score backlog with
  | nil => simp [QueueReplay.replay]
  | cons record rest ih =>
      have htransition := transition_add_score capacity score backlog record
      change QueueReplay.replay capacity
          (QueueReplay.transition capacity (score, backlog) record) rest =
        (score + (QueueReplay.replay capacity
          (QueueReplay.transition capacity (0, backlog) record) rest).1,
          (QueueReplay.replay capacity
            (QueueReplay.transition capacity (0, backlog) record) rest).2)
      rw [htransition]
      rw [ih (score + (QueueReplay.transition capacity (0, backlog) record).1)
        (QueueReplay.transition capacity (0, backlog) record).2]
      rw [ih (QueueReplay.transition capacity (0, backlog) record).1
        (QueueReplay.transition capacity (0, backlog) record).2]
      simp only [Nat.add_assoc]

private theorem replay_score_le_single_append (capacity : ℕ)
    (initial : ℕ × ℕ) (records : List (Bool × ℕ))
    (record : Bool × ℕ) :
    (QueueReplay.replay capacity initial records).1 ≤
      (QueueReplay.replay capacity initial (records ++ [record])).1 := by
  rw [QueueReplay.replay_append]
  cases record with
  | mk enabled arrival =>
      cases enabled <;> simp [QueueReplay.replay, QueueReplay.transition]

private theorem executedTail_of_choice
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (c : ReferenceCollectionSegmentExtraction.Choice rate)
    (hchoice : ReferenceCollectionSegmentExtraction.choice x = some c) :
    ReferenceCollectionPhaseHistory.executedTail x = some
      ⟨c.payload, c.preLedger, c.started, c.weights⟩ := by
  let prepared := ReferenceActivePhysicalStep.prepare x
  have hselection : prepared.coordinator.selection ≠ none := by
    intro hnone
    simp [ReferenceCollectionSegmentExtraction.choice, prepared, hnone] at hchoice
  have hcut : ReferenceCollectionSegmentExtraction.choiceOfCut
      prepared.coordinator = some c := by
    simpa [ReferenceCollectionSegmentExtraction.choice, prepared, hselection] using hchoice
  cases hcoord : prepared.coordinator with
    | first outcome =>
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
    | live registers owned base outcome =>
        cases outcome with
        | cutoffChosen dispatched hstart ledger hinit hledger hvalid hclock
            hpending hnone selected =>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
          have hc := Option.some.inj hcut
          cases hc
          unfold ReferenceCollectionPhaseHistory.executedTail
          dsimp only [prepared]
          rw [ite_eq_right hselection, hcoord]
        | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
    | collection payload ledger clock cutoff outcome =>
        cases outcome with
        | continuing core snapshot boundary scores =>
          simp only [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
          have hc := Option.some.inj hcut
          cases hc
          unfold ReferenceCollectionPhaseHistory.executedTail
          dsimp only [prepared]
          rw [ite_eq_right hselection, hcoord]
        | _ => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
    | invalidCollectionCutoff =>
        simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut
    | dagger => simp [ReferenceCollectionSegmentExtraction.choiceOfCut, hcoord] at hcut

/-- Join U's actual first-DOWN initialized sender replay with R's actual
coordinator physical collection replay at one selected accepted record. The
root inputs are the original run, original whole tables and reward table,
the actual focal initial local state, an actual extracted segment record,
and its actual accepted/parser/sender selectors. No accepted-event predicate,
replay list, matching trace, true cutoff field, or queue law is supplied.

The result reconstructs the finished coordinator registers from the same
retained DOWN replay followed by the actual segment's physical records through
the accepted current round. The concatenated expression remains an internal
projection: source-global arrival identity and source ledger-cutoff identity
are separate producers. -/
theorem actual_first_collection_numerical_replay
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (J : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (i : Fin (p.m - 1))
    (seed : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hseed : initial.followers i = .ordinary seed memory)
    (hnone : seed.lastDown = none)
    (hunoccupied : seed.status = .unoccupied)
    (hvalid : ActiveFollowerLifecycle.localBufferValid seed)
    (hpair : seed.buffer.Pairwise (fun a b => a.calendarRound < b.calendarRound))
    (htime : ∀ saved ∈ seed.buffer, saved.calendarRound ≤ start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k < segment.records.length)
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound
      (segment.records[k]'hk) = some completed)
    (haccepted : completed.accepted = true)
    (M : ReferenceCollectionPhaseHistory.UpRecord p rate)
    (hparsed : completed.input.parsed = some M)
    (hselected : completed.input.selectedFollower = i)
    (hsigma : M.val.sigma = start + 1) :
    let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
    ∃ globalIndex : Fin E.records.length,
      globalIndex.val = offset + k ∧
      E.records[globalIndex.val] = segment.records[k]'hk ∧
      ReferenceCollectionPhaseHistory.AcceptedUp
        (E.records[globalIndex.val]).input i M ∧
      ∃ j : Fin E.records.length, j.val < globalIndex.val ∧
        ∃ message : ReferenceFirstAcceptedUpNumericSnapshot.DownRecord
            (p := p) (rate := rate),
          ReferenceAcceptedUpFollowerHistory.RetainedDown E.records[j.val] i message ∧
          message.val.sigma = start + 1 ∧
          let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
          let u := FollowerCutoffScan.firstCutoff p rate.eta.val
            (ActiveFollowerDownAcceptance.downStart p rate message) bits
          let m := u - (start + 1)
          let b := max m (j.val + 1)
          let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
            (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
              E.records i j.val message h)
          start + 1 < u ∧ u ≤ start + globalIndex.val + 1 ∧
          0 < m ∧ m ≤ globalIndex.val ∧ b ≤ globalIndex.val ∧
          M.val.S = (V m).1 ∧ M.val.q = (V m).2 ∧
          M.val.delta = (V m).1 - (V (m - 1)).1 ∧
          (∃ hb : b < E.records.length, ∃ boundary boundaryMemory,
            (ReferenceFollowerFixedReply.actualChoice E.records[b] i).configuration =
              .ordinary boundary boundaryMemory ∧
            boundary.status = .unoccupied ∧ boundary.lastDown = some message ∧
            boundary.S = (V m).1 ∧ boundary.backlog = (V m).2 ∧
            boundary.delta = (V m).1 - (V (m - 1)).1) ∧
          ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
            segment.context.initializer = some initializer ∧
            initializer.checkedStart rate = .success segment.context.preLedger ∧
            CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
              (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
              initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
              initializer.base initializer.outside segment.inputs =
                .success ⟨segment.context.preLedger, segment.accepted, segment.final⟩ ∧
            ∃ prefixExecution : CollectionCheckedExecution.Execution p rate.eta.val
                rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
                rate.n rate.n_scale,
              CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
                (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
                initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
                initializer.base initializer.outside (segment.inputs.take k) =
                  .success prefixExecution ∧
              prefixExecution.initial = segment.context.preLedger ∧
              prefixExecution.final = ReferenceCollectionSegmentExtraction.endpointLedger
                segment.context.preLedger (segment.records.take k) ∧
              ∃ recording started decoded bank finished,
                let record := segment.records[k]'hk
                record.output.coordinator.recording = some recording ∧
                CoordinatorRecorderComplementBridge.run
                  (ReferenceActivePhysicalStep.collectionRecordingInput
                    (ReferenceActivePhysicalStep.prepare record.input)
                    completed.context.payload completed.context.started completed.context.weights) =
                    some recording ∧
                CoordinatorCollectionLedger.startRound completed.context.preLedger
                  (record.input.time.val + 1)
                  (ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger
                    record.input.time)
                  (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
                    .success started ∧
                (ReferenceActivePhysicalStep.receiveUp
                  (ReferenceActivePhysicalStep.prepare record.input) started).result =
                    .success (decoded, bank) ∧
                CoordinatorCollectionLedger.decodeUp started i (some M) = .success decoded ∧
                CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
                finished = completed.final ∧
                completed.input = ReferenceCollectionSegmentExtraction.inputOf record.input
                  completed.context.preLedger recording started ∧
                let arm := started.assignment.arm i
                ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
                  ∃ lastIndex : Fin p.T,
                    CoordinatorCollectionLedger.sourceRound lastIndex = started.cursor ∧
                    lastIndex = record.input.time ∧ started.cursor - started.cutoff = k ∧
                    started.assignment = initializer.assignment ∧
                    started.sigma = initializer.sigma ∧
                    started.cutoff = initializer.cutoff ∧
                    started.freezeAt = initializer.freezeAt ∧
                    started.baseScore = initializer.base ∧
                    1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
                    started.cursor ≤ p.T ∧
                    prefixExecution.final.currentRegisters arm = none ∧
                    started.currentRegisters arm = none ∧ started.gammaLoc arm = 0 ∧
                    let C := fun h => (segment.records.take h).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm)
                    let Q := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
                      (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords
                        E.records i j.val message m ++ C h)
                    ∃ past current,
                      CoordinatorCollectionLedger.replayRecords? started arm
                        (CoordinatorCollectionLedger.calendarIndices p.T
                          (started.cutoff - 1) (started.cursor - started.cutoff) hbound) =
                            some past ∧
                      CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] =
                            some [current] ∧
                      CollectionBufferProvenance.suppliedReplayRecords?
                        (segment.inputs.take k ++ [completed.input]) arm started.freezeAt
                        (CoordinatorCollectionLedger.calendarIndices p.T
                          (started.cutoff - 1) (started.cursor - started.cutoff) hbound ++
                          [lastIndex]) = some (past ++ [current]) ∧
                      past = C k ∧
                      current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm record ∧
                      past ++ [current] = C (k + 1) ∧
                      C k ++ [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm record] = C (k + 1) ∧
                      finished.cutoffRegisters arm =
                        some ⟨started.baseScore i + (V m).1, (V m).2,
                          (V m).1 - (V (m - 1)).1⟩ ∧
                      finished.currentRegisters arm =
                        some ⟨(Q (k + 1)).2, (Q (k + 1)).1 - (Q k).1⟩ ∧
                      finished.increment arm =
                        (QueueReplay.replay (4 * rate.n) (0, (V m).2) (C (k + 1))).1 ∧
                      (V m).1 + finished.increment arm = (Q (k + 1)).1 := by
  classical
  let E := ReferenceActivePhysicalHorizon.run initial rows J rewards start count span active
  have hpartition := ReferenceCollectionSegmentExtraction.segmentAt_partition
    E.records offset segment hsegment
  have hkDrop : k < (E.records.drop offset).length := by
    rw [← hpartition]
    simp only [List.length_append]
    omega
  have hglobalBound : offset + k < E.records.length := by
    simp only [List.length_drop] at hkDrop
    omega
  let globalIndex : Fin E.records.length := ⟨offset + k, hglobalBound⟩
  have hdropRecord : (E.records.drop offset)[k]'hkDrop = segment.records[k]'hk := by
    have hkAppend : k < (segment.records ++ segment.remaining).length := by
      simp only [List.length_append]
      omega
    calc
      (E.records.drop offset)[k]'hkDrop =
          (segment.records ++ segment.remaining)[k]'hkAppend := by
        exact (List.getElem_of_eq hpartition hkAppend).symm
      _ = segment.records[k]'hk := List.getElem_append_left hk
  have hglobalRecord : E.records[globalIndex.val] = segment.records[k]'hk := by
    dsimp only [globalIndex]
    calc
      E.records[offset + k]'hglobalBound = (E.records.drop offset)[k]'hkDrop :=
        (List.getElem_drop).symm
      _ = segment.records[k]'hk := hdropRecord

  let record := segment.records[k]'hk
  have hrecord := ReferenceCollectionSegmentExtraction.actual_collection_round_checked
    record completed hextract
  have hchoice : ReferenceCollectionSegmentExtraction.choice record.input =
      some completed.context := hrecord.1
  have hphysical := ReferenceCollectionUpReplayHistory.actual_accepted_up_physical_replay_join
    initial rows J rewards start count span active hfirst offset segment hsegment k hk
    completed hextract haccepted M hparsed i hselected
  rcases hphysical with ⟨initializer, hinitializer, hcheckedStart, hwholeRun,
    prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
    recording, started, decoded, bank, finished, hrecording, hrunRecorder,
    hstart, hreceive, hdecode, hfinish, hfinished, hinput,
    hbound, lastIndex, hlastSource, hlastIndex, hcursorDifference,
    hstartedAssignment, hstartedSigma, hstartedCutoff, hstartedFreeze,
    hstartedBase, hcutoffPositive, hcutoffLe, hcursorLe,
    hprefixUnknown, hstartedUnknown,
    past, current, hpast, hcurrent, hsuppplied, hpastPhysical,
    hcurrentPhysical, hphysicalList, hphysicalSplit, hfinishedCurrent,
    hfinishedIncrement, hfinishedCutoff⟩

  let tail : ReferenceCollectionPhaseHistory.Tail record.input :=
    ⟨completed.context.payload, completed.context.preLedger,
      completed.context.started, completed.context.weights⟩
  have htail : ReferenceCollectionPhaseHistory.executedTail record.input = some tail := by
    simpa [tail] using executedTail_of_choice record.input completed.context hchoice
  have hparseInput :
      (ReferenceCollectionSegmentExtraction.inputOf record.input
        completed.context.preLedger recording started).parsed = some M := by
    rw [hinput] at hparsed
    exact hparsed
  have hfiltered :
      ReferenceCollectionPhaseHistory.filteredParsed record.input started = some M := by
    simpa [ReferenceCollectionPhaseHistory.filteredParsed,
      ReferenceCollectionSegmentExtraction.inputOf,
      ReferenceCollectionSegmentExtraction.effectiveParse] using hparseInput
  have hsender : i = ReferenceActivePhysicalStep.upSenderIndex record.input := by
    have hselectedInput := congrArg
      (fun input : CollectionCheckedExecution.RoundInput
          (p := p) (eta := rate.eta.val) => input.selectedFollower) hinput
    have hselectedActual : completed.input.selectedFollower =
        ReferenceActivePhysicalStep.upSenderIndex record.input := by
      simpa [ReferenceCollectionSegmentExtraction.inputOf] using hselectedInput
    exact hselected.symm.trans hselectedActual
  have hAccepted : ReferenceCollectionPhaseHistory.AcceptedUp record.input i M := by
    refine ⟨tail, recording, started, decoded, bank, htail, ?_, ?_, hreceive,
      hfiltered, hsender⟩
    · simpa [tail] using hrunRecorder
    · exact hstart

  have hAcceptedGlobal : ReferenceCollectionPhaseHistory.AcceptedUp
      (E.records[globalIndex.val]).input i M := by
    rw [hglobalRecord]
    exact hAccepted

  have hOnline := ReferenceFirstAcceptedUpOnlineReplay.run_first_accepted_up_online_replay
    initial rows J rewards start count span active hfirst i seed memory hseed hnone
    hunoccupied hvalid hpair htime globalIndex M hAcceptedGlobal hsigma
  rcases hOnline with ⟨j, hjGlobal, message, hretained, hmessageSigma,
      hu, huBound, hmPositive, hmBound, hbBound, hMS, hMq, hMdelta,
      hb, boundary, boundaryMemory, hboundaryChoice, hboundaryStatus,
      hboundaryDown, hboundaryS, hboundaryQ, hboundaryDelta⟩
  let bits := FollowerCutoffScan.completeRowProposalBit p rate.eta.val (rows J)
  let u := FollowerCutoffScan.firstCutoff p rate.eta.val
    (ActiveFollowerDownAcceptance.downStart p rate message) bits
  let m := u - (start + 1)
  let b := max m (j.val + 1)
  let V := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message h)
  change j.val < globalIndex.val at hjGlobal
  change start + 1 < u at hu
  change u ≤ start + globalIndex.val + 1 at huBound
  change 0 < m at hmPositive
  change m ≤ globalIndex.val at hmBound
  change b ≤ globalIndex.val at hbBound
  change M.val.S = (V m).1 at hMS
  change M.val.q = (V m).2 at hMq
  change M.val.delta = (V m).1 - (V (m - 1)).1 at hMdelta

  let arm := started.assignment.arm i
  let C := fun h => (segment.records.take h).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord segment.context.preLedger arm)
  let Q := fun h => QueueReplay.replay (4 * rate.n) (0, 0)
    (ReferenceFirstAcceptedUpNumericSnapshot.firstReplyQueueRecords E.records i j.val message m ++
      C h)
  have hqueueCompose (h : ℕ) :
      Q h = ((V m).1 +
        (QueueReplay.replay (4 * rate.n) (0, (V m).2) (C h)).1,
        (QueueReplay.replay (4 * rate.n) (0, (V m).2) (C h)).2) := by
    dsimp [Q, V]
    rw [QueueReplay.replay_append]
    exact replay_add_score (4 * rate.n) (V m).1 (V m).2 (C h)

  let physicalCurrent :=
    ReferenceCollectionRawBufferHistory.physicalQueueRecord segment.context.preLedger arm
      record
  have hphysicalSplitC : C k ++ [physicalCurrent] = C (k + 1) := by
    dsimp [C, physicalCurrent, record, arm]
    exact hphysicalSplit
  have hcollectionReplay :
      QueueReplay.replay (4 * rate.n) (0, M.val.q) (C k ++ [physicalCurrent]) =
        QueueReplay.replay (4 * rate.n) (0, (V m).2) (C (k + 1)) := by
    calc
      QueueReplay.replay (4 * rate.n) (0, M.val.q) (C k ++ [physicalCurrent]) =
          QueueReplay.replay (4 * rate.n) (0, M.val.q) (C (k + 1)) := by
            rw [hphysicalSplitC]
      _ = QueueReplay.replay (4 * rate.n) (0, (V m).2) (C (k + 1)) := by
        rw [hMq]
  have hprefixReplay :
      QueueReplay.replay (4 * rate.n) (0, M.val.q) (C k) =
        QueueReplay.replay (4 * rate.n) (0, (V m).2) (C k) := by
    rw [hMq]
  have hcurrentQueue : finished.currentRegisters arm =
      some ⟨(Q (k + 1)).2, (Q (k + 1)).1 - (Q k).1⟩ := by
    rw [hfinishedCurrent]
    simp only [Option.some.injEq, CoordinatorCollectionLedger.CurrentRegister.mk.injEq]
    constructor
    · change (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (C k ++ [physicalCurrent])).2 = (Q (k + 1)).2
      rw [hcollectionReplay, hqueueCompose (k + 1)]
    · change (QueueReplay.replay (4 * rate.n) (0, M.val.q)
          (C k ++ [physicalCurrent])).1 -
        (QueueReplay.replay (4 * rate.n) (0, M.val.q) (C k)).1 =
          (Q (k + 1)).1 - (Q k).1
      rw [hcollectionReplay, hprefixReplay,
        hqueueCompose (k + 1), hqueueCompose k]
      have hscoreLe := replay_score_le_single_append (4 * rate.n)
        (0, (V m).2) (C k) physicalCurrent
      omega
  have hincrementCollection : finished.increment arm =
      (QueueReplay.replay (4 * rate.n) (0, (V m).2) (C (k + 1))).1 := by
    rw [hfinishedIncrement]
    change (QueueReplay.replay (4 * rate.n) (0, M.val.q)
      (C k ++ [physicalCurrent])).1 = _
    rw [hcollectionReplay]
  have hcutoffV : finished.cutoffRegisters arm =
      some ⟨started.baseScore i + (V m).1, (V m).2,
        (V m).1 - (V (m - 1)).1⟩ := by
    rw [hfinishedCutoff, hMS, hMq, hMdelta]
  have hcombinedIncrement : (V m).1 + finished.increment arm = (Q (k + 1)).1 := by
    rw [hincrementCollection, hqueueCompose (k + 1)]
  have hpreUnknown : completed.context.preLedger.currentRegisters arm = none :=
    CollectionBufferProvenance.startRound_success_unknown_reflects
      completed.context.preLedger started (record.input.time.val + 1)
      (ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger
        record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording)
      arm hstart hstartedUnknown
  have hstartedCandidate :=
    CoordinatorCollectionUpRoundStep.InputsValid.startRound_success_candidate
      completed.context.preLedger (record.input.time.val + 1) (by omega) (by omega)
      (ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger
        record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording)
      started hstart
  have htimeIndex :
      (⟨record.input.time.val + 1 - 1, by omega⟩ : Fin p.T) = record.input.time := by
    apply Fin.ext
    simp
  have hgammaLoc : started.gammaLoc arm = 0 := by
    rw [hstartedCandidate, htimeIndex]
    exact CoordinatorCollectionLedger.startRoundCandidate_unknown_zero
      completed.context.preLedger record.input.time
      (ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger
        record.input.time)
      (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording)
      arm hpreUnknown

  refine ⟨globalIndex, rfl, hglobalRecord, hAcceptedGlobal, ?_⟩
  refine ⟨j, ?_, message, hretained, hmessageSigma, ?_⟩
  · change j.val < globalIndex.val
    exact hjGlobal
  refine ⟨hu, huBound, hmPositive, hmBound, hbBound, hMS, hMq, hMdelta,
    ?_, ?_⟩
  · exact ⟨hb, boundary, boundaryMemory, hboundaryChoice, hboundaryStatus,
      hboundaryDown, hboundaryS, hboundaryQ, hboundaryDelta⟩
  · refine ⟨initializer, hinitializer, hcheckedStart, hwholeRun, ?_⟩
    refine ⟨prefixExecution, hprefixRun, hprefixInitial, hprefixFinal, ?_⟩
    refine ⟨recording, started, decoded, bank, finished, ?_, hrunRecorder,
      hstart, hreceive, hdecode, hfinish, hfinished, hinput, ?_⟩
    · exact hrecording
    · refine ⟨hbound, lastIndex, hlastSource, hlastIndex, hcursorDifference,
        hstartedAssignment, hstartedSigma, hstartedCutoff, hstartedFreeze,
        hstartedBase, hcutoffPositive, hcutoffLe, hcursorLe, hprefixUnknown,
        hstartedUnknown, hgammaLoc, ?_⟩
      exact ⟨past, current, hpast, hcurrent, hsuppplied, hpastPhysical,
        hcurrentPhysical, hphysicalList, hphysicalSplit, hcutoffV,
        hcurrentQueue, hincrementCollection, hcombinedIncrement⟩

end Bandits.Support.ReferenceFirstCollectionNumericalReplay

end
