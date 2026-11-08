/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionUpReplayHistory
public import Bandits.Support.CollectionKnownQueueContinuation

import Lean.Elab.Tactic.Omega

/-!
# Physical continuation after an accepted collection UP

For each retained physical endpoint after an accepted UP, the checked suffix
is derived from the same segment's checked prefixes. Its endpoint queue
registers are identified with one replay of the actual accepted physical
prefix and the actual post-acceptance physical records. Disabled records keep
their physical diagnostic arrivals; replay equivalence follows from the
literal disabled transition, without asserting equality of the record lists.

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:40-70,80-100,246-283`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`. This is an
internal execution identity. Parsed `M.q`, `M.S`, `M.delta`, and initializer
base scores remain parsed or retained values; no true-data, global queue, or
regret conclusion is asserted.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionAcceptedQueueContinuation

open ConstructorDimensions
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.QueueReplay
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceCollectionRawBufferHistory
open Bandits.Support.ReferenceCollectionPrefixLedgerHistory

variable {p : ReferenceActivePhysicalHorizon.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem dropLast_take_eq_take_pred {α : Type} (xs : List α)
    (n : ℕ) (hn : n ≤ xs.length) (hnpos : 0 < n) :
    (xs.take n).dropLast = xs.take (n - 1) := by
  have hidx : n - 1 < xs.length := by omega
  rw [show n = (n - 1) + 1 by omega,
    List.take_succ_eq_append_getElem hidx]
  have hne : xs.take (n - 1) ++ [xs[n - 1]] ≠ [] := by
    exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  have hlast := List.dropLast_append_getLast hne
  have hlastValue : List.getLast (xs.take (n - 1) ++ [xs[n - 1]]) hne = xs[n - 1] :=
    List.getLast_append_singleton _
  rw [hlastValue] at hlast
  exact List.append_left_injective [xs[n - 1]] hlast

private theorem checkedRounds_append_split
    (initial middle final : Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (first second : List (RoundInput (p := p) (eta := rate.eta.val)))
    (acceptedFirst acceptedAll : List Bool)
    (hfirst : checkedRounds initial first = some (acceptedFirst, middle))
    (hall : checkedRounds initial (first ++ second) = some (acceptedAll, final)) :
    ∃ acceptedSecond,
      acceptedAll = acceptedFirst ++ acceptedSecond ∧
      checkedRounds middle second = some (acceptedSecond, final) := by
  induction first generalizing initial acceptedFirst middle acceptedAll with
  | nil =>
      simp only [checkedRounds] at hfirst
      rcases hfirst with ⟨rfl, rfl⟩
      exact ⟨acceptedAll, by simp, hall⟩
  | cons input rest ih =>
      cases hstart : startRound initial (sourceRound input.round)
          input.enabled input.raw with
      | invalid => simp [checkedRounds, hstart] at hfirst
      | rejected bad => simp [checkedRounds, hstart] at hfirst
      | success started =>
          cases hdecode : decodeUp started input.selectedFollower input.parsed with
          | invalid => simp [checkedRounds, hstart, hdecode] at hfirst
          | success decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfirst
                  | some pair =>
                      have hfirst' : true :: pair.1 = acceptedFirst ∧ pair.2 = middle := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail] using hfirst
                      rcases hfirst' with ⟨hacceptedFirst, hmiddle⟩
                      have hwholeTail :
                          ∃ tailAccepted,
                            checkedRounds finished (rest ++ second) =
                              some (tailAccepted, final) ∧
                            acceptedAll = true :: tailAccepted := by
                        cases hwhole : checkedRounds finished (rest ++ second) with
                        | none =>
                            rw [List.cons_append] at hall
                            simp [checkedRounds, hstart, hdecode, hfinish, hwhole] at hall
                        | some wholePair =>
                            have hwhole' : true :: wholePair.1 = acceptedAll ∧
                                wholePair.2 = final := by
                              rw [List.cons_append] at hall
                              simpa [checkedRounds, hstart, hdecode, hfinish, hwhole]
                                using hall
                            rcases hwhole' with ⟨hflags, hfinal⟩
                            cases acceptedAll with
                            | nil => simp at hflags
                            | cons flag flags =>
                                injection hflags with hflagHead hflagsTail
                                have hflag : flag = true := by
                                  exact hflagHead.symm
                                subst flag
                                have hpair : wholePair = (flags, final) := by
                                  apply Prod.ext
                                  · exact hflagsTail
                                  · exact hfinal
                                exact ⟨flags, by rw [hpair], rfl⟩
                      obtain ⟨tailAccepted, hwholeTail, hwholeFlags⟩ := hwholeTail
                      have htailMiddle : checkedRounds finished rest =
                          some (pair.1, middle) := by rw [← hmiddle]; exact htail
                      obtain ⟨acceptedSecond, hflags, htailSplit⟩ :=
                        ih finished middle pair.1 tailAccepted htailMiddle hwholeTail
                      refine ⟨acceptedSecond, ?_, htailSplit⟩
                      calc
                        acceptedAll = true :: tailAccepted := hwholeFlags
                        _ = (true :: pair.1) ++ acceptedSecond := by rw [hflags]; rfl
                        _ = acceptedFirst ++ acceptedSecond := by rw [← hacceptedFirst]
          | rejected decoded =>
              cases hfinish : finishRound decoded with
              | invalid => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | rejected bad => simp [checkedRounds, hstart, hdecode, hfinish] at hfirst
              | success finished =>
                  cases htail : checkedRounds finished rest with
                  | none => simp [checkedRounds, hstart, hdecode, hfinish, htail] at hfirst
                  | some pair =>
                      have hfirst' : false :: pair.1 = acceptedFirst ∧ pair.2 = middle := by
                        simpa [checkedRounds, hstart, hdecode, hfinish, htail] using hfirst
                      rcases hfirst' with ⟨hacceptedFirst, hmiddle⟩
                      have hwholeTail :
                          ∃ tailAccepted,
                            checkedRounds finished (rest ++ second) =
                              some (tailAccepted, final) ∧
                            acceptedAll = false :: tailAccepted := by
                        cases hwhole : checkedRounds finished (rest ++ second) with
                        | none =>
                            rw [List.cons_append] at hall
                            simp [checkedRounds, hstart, hdecode, hfinish, hwhole] at hall
                        | some wholePair =>
                            have hwhole' : false :: wholePair.1 = acceptedAll ∧
                                wholePair.2 = final := by
                              rw [List.cons_append] at hall
                              simpa [checkedRounds, hstart, hdecode, hfinish, hwhole]
                                using hall
                            rcases hwhole' with ⟨hflags, hfinal⟩
                            cases acceptedAll with
                            | nil => simp at hflags
                            | cons flag flags =>
                                injection hflags with hflagHead hflagsTail
                                have hflag : flag = false := by
                                  exact hflagHead.symm
                                subst flag
                                have hpair : wholePair = (flags, final) := by
                                  apply Prod.ext
                                  · exact hflagsTail
                                  · exact hfinal
                                exact ⟨flags, by rw [hpair], rfl⟩
                      obtain ⟨tailAccepted, hwholeTail, hwholeFlags⟩ := hwholeTail
                      have htailMiddle : checkedRounds finished rest =
                          some (pair.1, middle) := by rw [← hmiddle]; exact htail
                      obtain ⟨acceptedSecond, hflags, htailSplit⟩ :=
                        ih finished middle pair.1 tailAccepted htailMiddle hwholeTail
                      refine ⟨acceptedSecond, ?_, htailSplit⟩
                      calc
                        acceptedAll = false :: tailAccepted := hwholeFlags
                        _ = (false :: pair.1) ++ acceptedSecond := by rw [hflags]; rfl
                        _ = acceptedFirst ++ acceptedSecond := by rw [← hacceptedFirst]

private theorem extracted_inputs_forall₂
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hall : ∀ record ∈ records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true) :
    List.Forall₂
      (fun record input => ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
          input = completed.input)
      records (ReferenceCollectionSegmentExtraction.inputs records) := by
  induction records with
  | nil => exact List.Forall₂.nil
  | cons record rest ih =>
      have hhead := hall record (by simp)
      have htail : ∀ record ∈ rest,
          (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true := by
        intro record hmem
        exact hall record (List.mem_cons_of_mem _ hmem)
      cases hExtract : ReferenceCollectionSegmentExtraction.extractRound record with
      | none => simp [hExtract] at hhead
      | some completed =>
          simpa [ReferenceCollectionSegmentExtraction.inputs,
            ReferenceCollectionSegmentExtraction.completed, hExtract] using
            (List.Forall₂.cons
              (show ∃ completed',
                ReferenceCollectionSegmentExtraction.extractRound record = some completed' ∧
                  completed.input = completed'.input from ⟨completed, hExtract, rfl⟩)
              (ih htail))

private theorem replay_eq_of_transition_forall₂
    (capacity : ℕ) {left right : List (Bool × ℕ)}
    (hrecords : List.Forall₂
      (fun x y => ∀ registers,
        QueueReplay.transition capacity registers x =
          QueueReplay.transition capacity registers y) left right)
    (initial : ℕ × ℕ) :
    QueueReplay.replay capacity initial left = QueueReplay.replay capacity initial right := by
  induction hrecords generalizing initial with
  | nil => rfl
  | @cons x y xs ys hxy htail ih =>
      change QueueReplay.replay capacity (QueueReplay.transition capacity initial x) xs =
        QueueReplay.replay capacity (QueueReplay.transition capacity initial y) ys
      rw [hxy initial]
      exact ih (QueueReplay.transition capacity initial y)

private theorem replayLastService_eq_of_transition_forall₂
    (capacity : ℕ) {left right : List (Bool × ℕ)}
    (hrecords : List.Forall₂
      (fun x y => ∀ registers,
        QueueReplay.transition capacity registers x =
          QueueReplay.transition capacity registers y) left right)
    (initial : ℕ × ℕ) (retained : ℕ) :
    CollectionKnownQueueContinuation.replayLastService capacity initial retained left =
      CollectionKnownQueueContinuation.replayLastService capacity initial retained right := by
  induction hrecords generalizing initial retained with
  | nil => rfl
  | @cons x y xs ys hxy htail ih =>
      rw [CollectionKnownQueueContinuation.replayLastService_cons,
        CollectionKnownQueueContinuation.replayLastService_cons]
      cases htail with
      | nil => simp [hxy initial]
      | @cons x₂ y₂ xs₂ ys₂ hxy₂ htail₂ =>
          rw [hxy initial]
          exact ih (QueueReplay.transition capacity initial y)
            ((QueueReplay.transition capacity initial y).1 - initial.1)

private theorem replayLastService_append_difference
    (capacity : ℕ) (initial : ℕ × ℕ)
    (before : List (Bool × ℕ)) (current : Bool × ℕ) :
    ∀ suffix : List (Bool × ℕ),
      let acceptedPrefix := before ++ [current]
      let prefixReplay := QueueReplay.replay capacity initial acceptedPrefix
      let initialService := prefixReplay.1 -
        (QueueReplay.replay capacity initial before).1
      let previous := if suffix = [] then before else acceptedPrefix ++ suffix.dropLast
      CollectionKnownQueueContinuation.replayLastService capacity prefixReplay
        initialService suffix =
        (QueueReplay.replay capacity initial (acceptedPrefix ++ suffix)).1 -
          (QueueReplay.replay capacity initial previous).1 := by
  intro suffix
  induction suffix generalizing before current with
  | nil =>
      simp [CollectionKnownQueueContinuation.replayLastService]
  | cons record rest ih =>
      cases rest with
      | nil =>
          dsimp
          rw [CollectionKnownQueueContinuation.replayLastService_cons]
          simp [QueueReplay.replay]
      | cons next tail =>
          dsimp
          rw [CollectionKnownQueueContinuation.replayLastService_cons]
          have ih' := ih (before ++ [current]) record
          simpa [List.append_assoc, QueueReplay.replay_append,
            QueueReplay.replay] using ih'

private theorem localQueue_transition_eq_physical
    (started : Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (input : RoundInput (p := p) (eta := rate.eta.val))
    (pre : ReferenceActivePhysicalStep.Ledger rate)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (arm : Fin p.K)
    (hround : input.round = record.input.time)
    (henabled : input.enabled = ReferenceActivePhysicalStep.collectionEnabled pre record.input.time)
    (hraw : input.raw = ReferenceCollectionRawBufferHistory.rawDiagnostic record)
    (hfreeze : started.freezeAt = pre.freezeAt)
    (registers : ℕ × ℕ) :
    QueueReplay.transition (4 * rate.n) registers
        (CoordinatorCollectionLedger.localQueueRecord started input.round input.enabled
          input.raw arm) =
      QueueReplay.transition (4 * rate.n) registers
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record) := by
  cases hEnabled : ReferenceActivePhysicalStep.collectionEnabled pre record.input.time <;>
    by_cases hbefore : record.input.time.val + 1 < pre.freezeAt <;>
    simp [CoordinatorCollectionLedger.localQueueRecord,
      ReferenceCollectionRawBufferHistory.physicalQueueRecord,
      CoordinatorCollectionLedger.sourceRound, QueueReplay.transition,
      hround, henabled, hraw, hfreeze, hEnabled, hbefore]

/-- Continue the same physical collection segment after one of its actually
accepted UP rounds. Each checked suffix and endpoint is produced from real
segment prefixes. Queue replay starts at the parsed cutoff queue, retains the
accepted round once, and then consumes the physical post-acceptance records.
The public boundary selectors are exactly those of
`actual_accepted_up_physical_replay_join`; no checked run or suffix result is
supplied as an input. -/
theorem actual_accepted_up_physical_queue_suffix_continuation
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (k : ℕ) (hk : k < segment.records.length)
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound
      (segment.records[k]'hk) = some completed)
    (haccepted : completed.accepted = true)
    (M : UpRecord (CoordinatorCollectionLedger.codecParams p rate.eta.val))
    (hparsed : completed.input.parsed = some M)
    (i : Fin (p.m - 1))
    (hselected : completed.input.selectedFollower = i) :
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
          (segment.records[k]'hk).output.coordinator.recording = some recording ∧
          CoordinatorRecorderComplementBridge.run
            (ReferenceActivePhysicalStep.collectionRecordingInput
              (ReferenceActivePhysicalStep.prepare (segment.records[k]'hk).input)
              completed.context.payload completed.context.started completed.context.weights) =
            some recording ∧
          CoordinatorCollectionLedger.startRound completed.context.preLedger
            ((segment.records[k]'hk).input.time.val + 1)
            (ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger
              (segment.records[k]'hk).input.time)
            (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording) =
              .success started ∧
          (ReferenceActivePhysicalStep.receiveUp
            (ReferenceActivePhysicalStep.prepare (segment.records[k]'hk).input) started).result =
              .success (decoded, bank) ∧
          CoordinatorCollectionLedger.decodeUp started i (some M) = .success decoded ∧
          CoordinatorCollectionLedger.finishRound decoded = .success finished ∧
          finished = completed.final ∧
          completed.input = ReferenceCollectionSegmentExtraction.inputOf
            (segment.records[k]'hk).input completed.context.preLedger recording started ∧
          ∃ hbound : started.cutoff - 1 + (started.cursor - started.cutoff) ≤ p.T,
            ∃ lastIndex : Fin p.T,
              sourceRound lastIndex = started.cursor ∧
              lastIndex = (segment.records[k]'hk).input.time ∧
              started.cursor - started.cutoff = k ∧
              started.assignment = initializer.assignment ∧
              initializer.assignment.arm i = started.assignment.arm i ∧
              started.sigma = initializer.sigma ∧
              started.cutoff = initializer.cutoff ∧
              started.freezeAt = initializer.freezeAt ∧
              started.baseScore = initializer.base ∧
              1 ≤ started.cutoff ∧
              started.cutoff ≤ started.cursor ∧
              started.cursor ≤ p.T ∧
              prefixExecution.final.currentRegisters (started.assignment.arm i) = none ∧
              started.currentRegisters (started.assignment.arm i) = none ∧
              ∃ past current,
                CoordinatorCollectionLedger.replayRecords? started (started.assignment.arm i)
                  (CoordinatorCollectionLedger.calendarIndices p.T
                    (started.cutoff - 1) (started.cursor - started.cutoff) hbound) =
                    some past ∧
                CoordinatorCollectionLedger.replayRecords? started (started.assignment.arm i) [lastIndex] =
                  some [current] ∧
                CollectionBufferProvenance.suppliedReplayRecords?
                  (segment.inputs.take k ++ [completed.input]) (started.assignment.arm i) started.freezeAt
                  (CoordinatorCollectionLedger.calendarIndices p.T
                    (started.cutoff - 1) (started.cursor - started.cutoff) hbound ++
                    [lastIndex]) = some (past ++ [current]) ∧
                past = (segment.records.take k).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (started.assignment.arm i)) ∧
                current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger (started.assignment.arm i) (segment.records[k]'hk) ∧
                past ++ [current] = (segment.records.take (k + 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (started.assignment.arm i)) ∧
                (segment.records.take k).map
                    (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                      segment.context.preLedger (started.assignment.arm i)) ++
                  [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger (started.assignment.arm i) (segment.records[k]'hk)] =
                  (segment.records.take (k + 1)).map
                    (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                      segment.context.preLedger (started.assignment.arm i)) ∧
                finished.currentRegisters (started.assignment.arm i) = some ⟨
                  (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((segment.records.take (k + 1)).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger (started.assignment.arm i)))).2,
                  (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((segment.records.take (k + 1)).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger (started.assignment.arm i)))).1 -
                  (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((segment.records.take k).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger (started.assignment.arm i)))).1⟩ ∧
                finished.increment (started.assignment.arm i) =
                  (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((segment.records.take (k + 1)).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger (started.assignment.arm i)))).1 ∧
                finished.cutoffRegisters (started.assignment.arm i) =
                  some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ ∧
                (∀ j, k + 1 ≤ j → j ≤ segment.records.length →
                  ∃ suffixAccepted,
                    CollectionCheckedExecution.checkedRounds completed.final
                      ((segment.inputs.drop (k + 1)).take (j - (k + 1))) =
                        some (suffixAccepted,
                          ReferenceCollectionSegmentExtraction.endpointLedger
                            segment.context.preLedger (segment.records.take j)) ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).currentRegisters (initializer.assignment.arm i) = some ⟨
                        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                          ((segment.records.take j).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              segment.context.preLedger (initializer.assignment.arm i)))).2,
                        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                          ((segment.records.take j).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              segment.context.preLedger (initializer.assignment.arm i)))).1 -
                        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                          ((segment.records.take (j - 1)).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              segment.context.preLedger (initializer.assignment.arm i)))).1⟩ ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).increment (initializer.assignment.arm i) =
                        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                          ((segment.records.take j).map
                            (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                              segment.context.preLedger (initializer.assignment.arm i)))).1 ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).cutoffRegisters (initializer.assignment.arm i) =
                        some ⟨initializer.base i + M.val.S, M.val.q, M.val.delta⟩ ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).assignment =
                        initializer.assignment ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).sigma =
                        initializer.sigma ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).cutoff =
                        initializer.cutoff ∧
                    (ReferenceCollectionSegmentExtraction.endpointLedger
                      segment.context.preLedger (segment.records.take j)).freezeAt =
                        initializer.freezeAt) ∧
                ∃ suffixAccepted,
                  CollectionCheckedExecution.checkedRounds completed.final
                    ((segment.inputs.drop (k + 1)).take
                      (segment.records.length - (k + 1))) =
                    some (suffixAccepted, segment.final) := by
  let record := segment.records[k]'hk
  let pre := segment.context.preLedger
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
    offset segment hsegment).1
  have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed _ segment hbranch
  obtain ⟨initializer, hinitializer, hcheckedStart, hwholeRun,
      prefixExecution, hprefixRun, hprefixInitial, hprefixFinal,
      recording, started, decoded, bank, finished, hrecording, hrunRecorder,
      hstart, hreceive, hdecode, hfinish, hfinished, hinput,
      hbound, lastIndex, hsource, hlast, hcursor,
      hassignment, hsigma, hcutoff, hfreeze, hbase,
      hcutoffLower, hcutoffUpper, hcursorUpper, hprefixUnknown, hstartedUnknown,
      past, current, hpast, hlastRecord, hsupplied,
      hpastPhysical, hcurrentPhysical, hpastCurrent, hphysicalAppend,
      hfinishedCurrent, hfinishedIncrement, hfinishedCutoff⟩ :=
    ReferenceCollectionUpReplayHistory.actual_accepted_up_physical_replay_join
      initial rows selected rewards start count span active hfirst offset segment hsegment
      k hk completed hextract haccepted M hparsed i hselected
  have hstartCollection :
      CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside = .success pre := by
    simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hcheckedStart
  have hinitContext :=
    CollectionBufferProvenance.startCollectionChecked_success_context
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside pre hstartCollection
  have hrecordTake : segment.records.take (k + 1) = segment.records.take k ++ [record] := by
    exact List.take_succ_eq_append_getElem hk
  have hendpointAccepted :
      ReferenceCollectionSegmentExtraction.endpointLedger pre
        (segment.records.take (k + 1)) = completed.final := by
    rw [hrecordTake, ReferenceCollectionSegmentExtraction.endpointLedger_append]
    simp [ReferenceCollectionSegmentExtraction.endpointLedger,
      ReferenceCollectionSegmentExtraction.completed, record, hextract]
  have hlengthGood : segment.records.length = segment.inputs.length := by
    have hrel := extracted_inputs_forall₂ segment.records hgood
    exact hrel.length_eq
  obtain ⟨acceptedAtSucc, hprefixAtSucc⟩ :=
    ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
      initial rows selected rewards start count span active offset segment hsegment
      (k + 1) (by omega)
  have hfirstFold : checkedRounds pre (segment.inputs.take (k + 1)) =
      some (acceptedAtSucc, finished) := by
    rw [hendpointAccepted] at hprefixAtSucc
    simpa [hfinished] using hprefixAtSucc
  let arm := started.assignment.arm i
  let physicalBefore := (segment.records.take k).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)
  let physicalAccepted := (segment.records.take (k + 1)).map
    (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)
  have hphysicalPrefixSplit :
      physicalBefore ++
        [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record] =
          physicalAccepted := by
    simpa [physicalBefore, physicalAccepted, record] using hphysicalAppend
  have hfinishedCurrentAccepted := hfinishedCurrent
  rw [hphysicalAppend] at hfinishedCurrentAccepted
  have hfinishedIncrementAccepted := hfinishedIncrement
  rw [hphysicalAppend] at hfinishedIncrementAccepted
  have hstartInput : startRound completed.context.preLedger
      (sourceRound completed.input.round) completed.input.enabled completed.input.raw =
        .success started := by
    rw [hinput]
    simpa [ReferenceCollectionSegmentExtraction.inputOf,
      CoordinatorCollectionLedger.sourceRound] using hstart
  have hdecodeInput : decodeUp started completed.input.selectedFollower
      completed.input.parsed = .success decoded := by
    rw [hselected, hparsed]
    exact hdecode
  have hfinishedContext :=
    CollectionBufferProvenance.checkedRound_success_context
      completed.context.preLedger started decoded finished completed.input hstartInput
      (Or.inl hdecodeInput) hfinish
  have hfreezePre : started.freezeAt = pre.freezeAt := by
    exact hfreeze.trans hinitContext.2.2.2.2.1.symm
  obtain ⟨acceptedBefore, hbeforeFold⟩ :=
    ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
      initial rows selected rewards start count span active offset segment hsegment
      k (Nat.le_of_lt hk)
  have hbeforeFoldContext :=
    CollectionBufferProvenance.checkedRounds_success_preserves_context
      pre (ReferenceCollectionSegmentExtraction.endpointLedger pre
        (segment.records.take k)) (segment.inputs.take k)
      acceptedBefore hbeforeFold
  have hretainedCurrent :=
    ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
      initial rows selected rewards start count span active offset segment hsegment
      k hk completed hextract
  have hcompletedContext :
      CollectionBufferProvenance.collectionContext completed.context.preLedger =
        CollectionBufferProvenance.collectionContext pre := by
    calc
      CollectionBufferProvenance.collectionContext completed.context.preLedger =
          CollectionBufferProvenance.collectionContext
            (ReferenceCollectionSegmentExtraction.endpointLedger pre
              (segment.records.take k)) := by rw [hretainedCurrent]
      _ = CollectionBufferProvenance.collectionContext pre := hbeforeFoldContext
  have hpreInitializerContext :
      CollectionBufferProvenance.collectionContext pre =
        (initializer.assignment, initializer.sigma, initializer.cutoff,
          initializer.freezeAt, initializer.base) := by
    rcases hinitContext with ⟨ha, hs, _, hc, hf, hb⟩
    simp [CollectionBufferProvenance.collectionContext, ha, hs, hc, hf, hb]
  refine ⟨initializer, ?_⟩
  refine ⟨hinitializer, ?_⟩
  refine ⟨hcheckedStart, ?_⟩
  refine ⟨hwholeRun, ?_⟩
  refine ⟨prefixExecution, ?_⟩
  refine ⟨hprefixRun, ?_⟩
  refine ⟨hprefixInitial, ?_⟩
  refine ⟨hprefixFinal, ?_⟩
  refine ⟨recording, ?_⟩
  refine ⟨started, ?_⟩
  refine ⟨decoded, ?_⟩
  refine ⟨bank, ?_⟩
  refine ⟨finished, ?_⟩
  refine ⟨hrecording, ?_⟩
  refine ⟨hrunRecorder, ?_⟩
  refine ⟨hstart, ?_⟩
  refine ⟨hreceive, ?_⟩
  refine ⟨hdecode, ?_⟩
  refine ⟨hfinish, ?_⟩
  refine ⟨hfinished, ?_⟩
  refine ⟨hinput, ?_⟩
  refine Exists.intro hbound ?_
  refine ⟨lastIndex, ?_⟩
  refine ⟨hsource, ?_⟩
  refine ⟨hlast, ?_⟩
  refine ⟨hcursor, ?_⟩
  refine ⟨hassignment, ?_⟩
  refine ⟨by rw [hassignment], ?_⟩
  refine ⟨hsigma, ?_⟩
  refine ⟨hcutoff, ?_⟩
  refine ⟨hfreeze, ?_⟩
  refine ⟨hbase, ?_⟩
  refine ⟨hcutoffLower, ?_⟩
  refine ⟨hcutoffUpper, ?_⟩
  refine ⟨hcursorUpper, ?_⟩
  refine ⟨hprefixUnknown, ?_⟩
  refine ⟨hstartedUnknown, ?_⟩
  refine ⟨past, ?_⟩
  refine ⟨current, ?_⟩
  refine ⟨hpast, ?_⟩
  refine ⟨hlastRecord, ?_⟩
  refine ⟨hsupplied, ?_⟩
  refine ⟨hpastPhysical, ?_⟩
  refine ⟨hcurrentPhysical, ?_⟩
  refine ⟨hpastCurrent, ?_⟩
  refine ⟨hphysicalAppend, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [arm, physicalAccepted, record] using hfinishedCurrentAccepted
  · refine ⟨hfinishedIncrementAccepted, ?_⟩
    refine ⟨hfinishedCutoff, ?_⟩
    have hforall : ∀ j, k + 1 ≤ j → j ≤ segment.records.length →
        ∃ suffixAccepted,
          CollectionCheckedExecution.checkedRounds finished
            ((segment.inputs.drop (k + 1)).take (j - (k + 1))) =
              some (suffixAccepted,
                ReferenceCollectionSegmentExtraction.endpointLedger pre
                  (segment.records.take j)) ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).currentRegisters arm = some ⟨
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((segment.records.take j).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).2,
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((segment.records.take j).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1 -
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((segment.records.take (j - 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1⟩ ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).increment arm =
            (QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((segment.records.take j).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1 ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).cutoffRegisters arm =
            some ⟨initializer.base i + M.val.S, M.val.q, M.val.delta⟩ ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).assignment = initializer.assignment ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).sigma = initializer.sigma ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).cutoff = initializer.cutoff ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).freezeAt = initializer.freezeAt := by
      intro j hjLower hjUpper
      let suffixInputs := (segment.inputs.drop (k + 1)).take (j - (k + 1))
      let suffixRecords := (segment.records.drop (k + 1)).take (j - (k + 1))
      let physicalSuffix := suffixRecords.map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)
      let localSuffix := suffixInputs.map
        (fun input => CoordinatorCollectionLedger.localQueueRecord started
          input.round input.enabled input.raw arm)
      let endpoint := ReferenceCollectionSegmentExtraction.endpointLedger pre
        (segment.records.take j)
      obtain ⟨acceptedAtJ, hwholePrefix⟩ :=
        ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
          initial rows selected rewards start count span active offset segment hsegment
          j hjUpper
      have hsum : (k + 1) + (j - (k + 1)) = j := by omega
      have hsplitInputs : segment.inputs.take j =
          segment.inputs.take (k + 1) ++ suffixInputs := by
        dsimp [suffixInputs]
        calc
          segment.inputs.take j =
              segment.inputs.take ((k + 1) + (j - (k + 1))) :=
                congrArg (segment.inputs.take) hsum.symm
          _ = segment.inputs.take (k + 1) ++
                (segment.inputs.drop (k + 1)).take (j - (k + 1)) := List.take_add
      have hsplitRecords : segment.records.take j =
          segment.records.take (k + 1) ++ suffixRecords := by
        dsimp [suffixRecords]
        calc
          segment.records.take j =
              segment.records.take ((k + 1) + (j - (k + 1))) :=
                congrArg (segment.records.take) hsum.symm
          _ = segment.records.take (k + 1) ++
                (segment.records.drop (k + 1)).take (j - (k + 1)) := List.take_add
      have hsplitPhysical :
          (segment.records.take j).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) =
            physicalAccepted ++ physicalSuffix := by
        rw [hsplitRecords]
        simp [physicalAccepted, physicalSuffix, suffixRecords, List.map_append]
      obtain ⟨suffixAccepted, _, hsuffix⟩ :=
        checkedRounds_append_split pre finished endpoint
          (segment.inputs.take (k + 1)) suffixInputs acceptedAtSucc acceptedAtJ
          hfirstFold (by rw [← hsplitInputs]; exact hwholePrefix)
      have hsuffixContext :=
        CollectionBufferProvenance.checkedRounds_success_preserves_context
          finished endpoint suffixInputs suffixAccepted hsuffix
      have hendpointContext :=
        (hsuffixContext.trans hfinishedContext).trans hcompletedContext |>.trans
          hpreInitializerContext
      have hendpointAssignment : endpoint.assignment = initializer.assignment :=
        congrArg (fun context => context.1) hendpointContext
      have hendpointSigma : endpoint.sigma = initializer.sigma :=
        congrArg (fun context => context.2.1) hendpointContext
      have hendpointCutoff : endpoint.cutoff = initializer.cutoff :=
        congrArg (fun context => context.2.2.1) hendpointContext
      have hendpointFreeze : endpoint.freezeAt = initializer.freezeAt :=
        congrArg (fun context => context.2.2.2.1) hendpointContext
      have hpairedAll := extracted_inputs_forall₂ segment.records hgood
      have hpairedSuffix : List.Forall₂
          (fun physical input => ∃ item,
            ReferenceCollectionSegmentExtraction.extractRound physical = some item ∧
              input = item.input)
          suffixRecords suffixInputs := by
        dsimp [suffixRecords, suffixInputs]
        simpa [ReferenceCollectionSegmentExtraction.Segment.inputs] using
          List.forall₂_take (j - (k + 1)) (List.forall₂_drop (k + 1) hpairedAll)
      have htransitionSuffix : List.Forall₂
          (fun physical input => ∀ registers,
            QueueReplay.transition (4 * rate.n) registers
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm physical) =
              QueueReplay.transition (4 * rate.n) registers
                (CoordinatorCollectionLedger.localQueueRecord started input.round
                  input.enabled input.raw arm))
          suffixRecords suffixInputs := by
        apply List.forall₂_of_length_eq_of_get hpairedSuffix.length_eq
        intro n hnPhysical hnInput
        let physical := suffixRecords[n]
        let input := suffixInputs[n]
        have hpair := hpairedSuffix.get hnPhysical hnInput
        rcases hpair with ⟨item, hitem, hinputItem⟩
        have hitemPhysical :
            ReferenceCollectionSegmentExtraction.extractRound physical = some item := by
          simpa [physical] using hitem
        have hmemSuffix : physical ∈ suffixRecords := List.getElem_mem _
        have hmemSegment : physical ∈ segment.records :=
          List.mem_of_mem_drop (List.mem_of_mem_take hmemSuffix)
        obtain ⟨q, hq, hphysical⟩ := List.getElem_of_mem hmemSegment
        have hitemQ :
            ReferenceCollectionSegmentExtraction.extractRound segment.records[q] =
              some item := by
          have hitem' := hitemPhysical
          rw [← hphysical] at hitem'
          exact hitem'
        obtain ⟨acceptedQ, hfoldQ⟩ :=
          ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
            initial rows selected rewards start count span active offset segment hsegment
            q (Nat.le_of_lt hq)
        have hretainedQ :=
          ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
            initial rows selected rewards start count span active offset segment hsegment
            q hq item hitemQ
        have hcontextQ :=
          CollectionBufferProvenance.checkedRounds_success_preserves_context
            pre (ReferenceCollectionSegmentExtraction.endpointLedger pre
              (segment.records.take q)) (segment.inputs.take q) acceptedQ hfoldQ
        have hitemContext :
            CollectionBufferProvenance.collectionContext item.context.preLedger =
              CollectionBufferProvenance.collectionContext pre := by
          calc
            CollectionBufferProvenance.collectionContext item.context.preLedger =
                CollectionBufferProvenance.collectionContext
                  (ReferenceCollectionSegmentExtraction.endpointLedger pre
                    (segment.records.take q)) := by rw [hretainedQ]
            _ = CollectionBufferProvenance.collectionContext pre := hcontextQ
        obtain ⟨_, _, _, _, _, _, _, hitemInput, _, _⟩ :=
          ReferenceCollectionSegmentExtraction.actual_collection_round_inputs
            segment.records[q] item hitemQ
        have hinputValue : input = item.input := by simpa [input] using hinputItem
        have hroundItem : item.input.round = (segment.records[q]).input.time := by
          rw [hitemInput]
          rfl
        have hrawEnabled :=
          ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled
            segment.records[q] item hitemQ
        have hinputRound : input.round = (segment.records[q]).input.time := by
          rw [hinputValue, hroundItem]
        have hinputRaw : input.raw =
            ReferenceCollectionRawBufferHistory.rawDiagnostic segment.records[q] := by
          rw [hinputValue, hrawEnabled.1]
        have hinputEnabled : input.enabled =
            ReferenceActivePhysicalStep.collectionEnabled pre (segment.records[q]).input.time := by
          rw [hinputValue, hrawEnabled.2]
          have hsigmaItem : item.context.preLedger.sigma = pre.sigma := by
            simpa [CollectionBufferProvenance.collectionContext] using
              congrArg (fun context => context.2.1) hitemContext
          have hcutoffItem : item.context.preLedger.cutoff = pre.cutoff := by
            simpa [CollectionBufferProvenance.collectionContext] using
              congrArg (fun context => context.2.2.1) hitemContext
          have hfreezeItem : item.context.preLedger.freezeAt = pre.freezeAt := by
            simpa [CollectionBufferProvenance.collectionContext] using
              congrArg (fun context => context.2.2.2.1) hitemContext
          simp [ReferenceActivePhysicalStep.collectionEnabled,
            hsigmaItem, hcutoffItem, hfreezeItem]
        intro registers
        simpa [physical, input, ← hphysical] using (localQueue_transition_eq_physical started input pre
          segment.records[q] arm hinputRound hinputEnabled hinputRaw hfreezePre
          registers).symm
      have hmappedSuffix : List.Forall₂
          (fun physicalRecord localRecord => ∀ registers,
            QueueReplay.transition (4 * rate.n) registers physicalRecord =
              QueueReplay.transition (4 * rate.n) registers localRecord)
          physicalSuffix localSuffix := by
        change List.Forall₂
          (fun physicalRecord localRecord => ∀ registers,
            QueueReplay.transition (4 * rate.n) registers physicalRecord =
              QueueReplay.transition (4 * rate.n) registers localRecord)
          (suffixRecords.map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))
          (suffixInputs.map (fun input => CoordinatorCollectionLedger.localQueueRecord
            started input.round input.enabled input.raw arm))
        refine List.rel_map ?_ htransitionSuffix
        intro physical input h registers
        exact h registers
      have hreplaySuffix : ∀ registers,
          QueueReplay.replay (4 * rate.n) registers localSuffix =
            QueueReplay.replay (4 * rate.n) registers physicalSuffix := by
        intro registers
        exact (replay_eq_of_transition_forall₂ (4 * rate.n)
          hmappedSuffix registers).symm
      have hlastSuffix : ∀ registers retained,
          CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
              registers retained localSuffix =
            CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
              registers retained physicalSuffix := by
        intro registers retained
        exact (replayLastService_eq_of_transition_forall₂ (4 * rate.n)
          hmappedSuffix registers retained).symm
      have hcontinuation :=
        CollectionKnownQueueContinuation.checked_acceptance_then_checked_suffix_one_replay
          completed.context.preLedger started decoded finished endpoint
          (sourceRound completed.input.round) completed.input.enabled completed.input.raw
          i M suffixInputs suffixAccepted hstartInput hdecode hfinish hsuffix
      obtain ⟨hboundK, lastIndexK, hsourceK, pastK, currentK,
          hpastK, hlastK, _, hcurrentK, hincrementK, hcutoffK,
          _, _⟩ := hcontinuation
      have hboundEq : hboundK = hbound := Subsingleton.elim _ _
      have hcompletedRound : completed.input.round = record.input.time := by
        rw [hinput]
        rfl
      have hlastIndexEq : lastIndexK = lastIndex := by
        apply Fin.ext
        have hsourceK' : lastIndexK.val + 1 = completed.input.round.val + 1 := by
          simpa [CoordinatorCollectionLedger.sourceRound] using hsourceK
        have hsourceJ : sourceRound lastIndex = sourceRound completed.input.round := by
          rw [hlast, hcompletedRound]
        have hsourceJ' : lastIndex.val + 1 = completed.input.round.val + 1 := by
          simpa [CoordinatorCollectionLedger.sourceRound] using hsourceJ
        omega
      have hpastK' := hpastK
      rw [hboundEq] at hpastK'
      have hpastSome : some pastK = some past := by
        calc
          some pastK = CoordinatorCollectionLedger.replayRecords? started arm
              (CoordinatorCollectionLedger.calendarIndices p.T
                (started.cutoff - 1) (started.cursor - started.cutoff) hbound) := hpastK'.symm
          _ = some past := hpast
      have hpastEq : pastK = past := Option.some.inj hpastSome
      have hlastK' :
          CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] =
            some [currentK] := by
        simpa [hlastIndexEq] using hlastK
      have hcurrentEq : currentK = current := by
        have hlistSome : some [currentK] = some [current] :=
          (hlastK'.symm.trans hlastRecord)
        have hlist := Option.some.inj hlistSome
        simpa using hlist
      have hacceptedRecords : pastK ++ [currentK] = physicalAccepted := by
        calc
          pastK ++ [currentK] = past ++ [current] := by rw [hpastEq, hcurrentEq]
          _ = physicalAccepted := by simpa [physicalAccepted, arm, record] using hpastCurrent
      let acceptanceReplay := QueueReplay.replay (4 * rate.n) (0, M.val.q)
        (pastK ++ [currentK])
      let acceptedService := acceptanceReplay.1 -
        (QueueReplay.replay (4 * rate.n) (0, M.val.q) pastK).1
      have hacceptanceReplay : acceptanceReplay =
          QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted := by
        simp only [acceptanceReplay]
        rw [hacceptedRecords]
      have hacceptedService : acceptedService =
          (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted).1 -
            (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalBefore).1 := by
        simp only [acceptedService, acceptanceReplay]
        rw [hacceptedRecords, hpastEq, hpastPhysical]
      have hfullReplay :
          QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((pastK ++ [currentK]) ++
                CollectionKnownQueueContinuation.inputQueueRecords started arm suffixInputs) =
            QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((segment.records.take j).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)) := by
        calc
          QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((pastK ++ [currentK]) ++
                CollectionKnownQueueContinuation.inputQueueRecords started arm suffixInputs) =
            QueueReplay.replay (4 * rate.n)
              (QueueReplay.replay (4 * rate.n) (0, M.val.q) (pastK ++ [currentK]))
              (CollectionKnownQueueContinuation.inputQueueRecords started arm suffixInputs) :=
                QueueReplay.replay_append _ _ _ _
          _ = QueueReplay.replay (4 * rate.n)
                (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted)
                physicalSuffix := by
                  rw [hacceptedRecords]
                  have hlocal : CollectionKnownQueueContinuation.inputQueueRecords
                      started arm suffixInputs = localSuffix := by
                    simp [localSuffix, CollectionKnownQueueContinuation.inputQueueRecords]
                  rw [hlocal]
                  exact hreplaySuffix _
          _ = QueueReplay.replay (4 * rate.n) (0, M.val.q)
                (physicalAccepted ++ physicalSuffix) :=
                  (QueueReplay.replay_append _ _ _ _).symm
          _ = _ := by rw [hsplitPhysical]
      have hlastAcceptedReplay := replayLastService_append_difference
        (4 * rate.n) (0, M.val.q) physicalBefore
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record) physicalSuffix
      have hlastTransport :
          CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
              acceptanceReplay acceptedService localSuffix =
            CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
              (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted)
              ((QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted).1 -
                (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalBefore).1)
              physicalSuffix := by
        calc
          _ = CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
                acceptanceReplay acceptedService physicalSuffix := hlastSuffix _ _
          _ = CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
                (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted)
                ((QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalAccepted).1 -
                  (QueueReplay.replay (4 * rate.n) (0, M.val.q) physicalBefore).1)
                physicalSuffix := by rw [← hacceptedService, ← hacceptanceReplay]
      have hlastTransport' := hlastTransport
      rw [← hphysicalPrefixSplit] at hlastTransport'
      have hlastAppend := hlastTransport'.trans hlastAcceptedReplay
      have hd : j - (k + 1) ≤ (segment.records.drop (k + 1)).length := by
        rw [List.length_drop]
        omega
      have hprevious :
          (if physicalSuffix = [] then physicalBefore
            else physicalAccepted ++ physicalSuffix.dropLast) =
            (segment.records.take (j - 1)).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := by
        by_cases hdzero : j - (k + 1) = 0
        · have hjEq : j = k + 1 := by omega
          simp [physicalSuffix, suffixRecords, physicalBefore, hjEq]
        · have hdpos : 0 < j - (k + 1) := Nat.pos_of_ne_zero hdzero
          have hdropLast : suffixRecords.dropLast =
              (segment.records.drop (k + 1)).take (j - (k + 1) - 1) :=
            dropLast_take_eq_take_pred _ _ hd hdpos
          have hnotEmpty : suffixRecords ≠ [] := by
            intro he
            have hlen := congrArg List.length he
            simp [suffixRecords, List.length_take] at hlen
            omega
          have hphysicalNotEmpty : physicalSuffix ≠ [] := by
            simpa [physicalSuffix] using hnotEmpty
          have hsumPrev :
              (k + 1) + (j - (k + 1) - 1) = j - 1 := by omega
          have hphysicalSuffixDropLast : physicalSuffix.dropLast =
              ((segment.records.drop (k + 1)).take (j - (k + 1) - 1)).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := by
            have hdropMapped := congrArg
              (List.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))
              hdropLast
            simpa [physicalSuffix, suffixRecords, List.map_dropLast] using hdropMapped
          have hprevRecords : segment.records.take (j - 1) =
              segment.records.take (k + 1) ++
                (segment.records.drop (k + 1)).take (j - (k + 1) - 1) := by
            rw [← hsumPrev]
            exact List.take_add
          rw [ite_eq_right hphysicalNotEmpty, hprevRecords, List.map_append]
          change physicalAccepted ++ physicalSuffix.dropLast =
            physicalAccepted ++
              ((segment.records.drop (k + 1)).take (j - (k + 1) - 1)).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)
          rw [← hphysicalSuffixDropLast]
      have hlastPhysical :
          CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
              acceptanceReplay acceptedService
                (CollectionKnownQueueContinuation.inputQueueRecords started arm suffixInputs) =
            (QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((segment.records.take j).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1 -
            (QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((segment.records.take (j - 1)).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1 := by
        calc
          _ = CollectionKnownQueueContinuation.replayLastService (4 * rate.n)
                acceptanceReplay acceptedService localSuffix := by
                  simp [localSuffix, CollectionKnownQueueContinuation.inputQueueRecords]
          _ = _ := by
            rw [hlastAppend, hphysicalPrefixSplit, ← hsplitPhysical, hprevious]
      have hfinalCurrent : endpoint.currentRegisters arm = some ⟨
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((segment.records.take j).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).2,
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((segment.records.take j).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1 -
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((segment.records.take (j - 1)).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1⟩ := by
        rw [hcurrentK, hfullReplay, hlastPhysical]
      have hfinalIncrement : endpoint.increment arm =
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((segment.records.take j).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1 := by
        rw [hincrementK, hfullReplay]
      have hfinalCutoff : endpoint.cutoffRegisters arm =
          some ⟨initializer.base i + M.val.S, M.val.q, M.val.delta⟩ := by
        simpa [hbase] using hcutoffK
      exact ⟨suffixAccepted, hsuffix, hfinalCurrent, hfinalIncrement,
        hfinalCutoff, hendpointAssignment, hendpointSigma, hendpointCutoff,
        hendpointFreeze⟩
    have hforallInit : ∀ j, k + 1 ≤ j → j ≤ segment.records.length →
        ∃ suffixAccepted,
          CollectionCheckedExecution.checkedRounds completed.final
            ((segment.inputs.drop (k + 1)).take (j - (k + 1))) =
              some (suffixAccepted,
                ReferenceCollectionSegmentExtraction.endpointLedger pre
                  (segment.records.take j)) ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).currentRegisters (initializer.assignment.arm i) = some ⟨
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((segment.records.take j).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre
                    (initializer.assignment.arm i)))).2,
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((segment.records.take j).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre
                    (initializer.assignment.arm i)))).1 -
              (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                ((segment.records.take (j - 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre
                    (initializer.assignment.arm i)))).1⟩ ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).increment (initializer.assignment.arm i) =
            (QueueReplay.replay (4 * rate.n) (0, M.val.q)
              ((segment.records.take j).map
                (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre
                  (initializer.assignment.arm i)))).1 ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).cutoffRegisters (initializer.assignment.arm i) =
            some ⟨initializer.base i + M.val.S, M.val.q, M.val.delta⟩ ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).assignment = initializer.assignment ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).sigma = initializer.sigma ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).cutoff = initializer.cutoff ∧
          (ReferenceCollectionSegmentExtraction.endpointLedger pre
            (segment.records.take j)).freezeAt = initializer.freezeAt := by
      intro j hjLower hjUpper
      obtain ⟨suffixAccepted, hfold, hcurrent, hincrement, hcutoffRegister,
        hassignmentEnd, hsigmaEnd, hcutoffEnd, hfreezeEnd⟩ :=
        hforall j hjLower hjUpper
      refine ⟨suffixAccepted, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [← hfinished]
        exact hfold
      · simpa [arm, hassignment] using hcurrent
      · simpa [arm, hassignment] using hincrement
      · simpa [arm, hassignment] using hcutoffRegister
      · exact hassignmentEnd
      · exact hsigmaEnd
      · exact hcutoffEnd
      · exact hfreezeEnd
    refine ⟨hforallInit, ?_⟩
    obtain ⟨suffixAccepted, hfinalFold, _, _, _, _, _, _⟩ :=
      hforallInit segment.records.length (by omega) (by rfl)
    refine ⟨suffixAccepted, ?_⟩
    simpa [ReferenceCollectionSegmentExtraction.Segment.final] using hfinalFold

end Bandits.Support.ReferenceCollectionAcceptedQueueContinuation

end
