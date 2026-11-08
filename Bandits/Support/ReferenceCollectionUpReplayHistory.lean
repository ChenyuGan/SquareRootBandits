/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionRawBufferHistory
public import Bandits.Support.ReferenceCollectionPrefixLedgerHistory

import Lean.Elab.Tactic.Omega

/-!
# Actual accepted-UP physical replay history

The accepted UP replay records are identified with the literal physical
records of the same actual collection segment, including its accepted current
round exactly once. The statement keeps the original run inputs and exposes
the actual checked prefix and actual recorder/decoder calls.

Mathematical evidence: `sources/zip4/manuscript/06_interruptions.tex:40-70,80-100,246-283`
and `sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`. These are
internal execution identities; they do not assert truthful returned fields,
global recorder correctness, or a regret conclusion.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionUpReplayHistory

open ConstructorDimensions
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.CollectionBufferProvenance
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.OrdinaryMessageCodec
open Bandits.Support.ReferenceCollectionSegmentExtraction
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceCollectionRawBufferHistory
open Bandits.Support.ReferenceCollectionPrefixLedgerHistory

variable {p : ConstructorDimensions.Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

private theorem completed_length_of_all_extracted
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hall : ∀ record ∈ records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true) :
    (ReferenceCollectionSegmentExtraction.completed records).length = records.length := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      have hhead := hall record (by simp)
      have htail : ∀ record ∈ rest,
          (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true := by
        intro record hmem
        exact hall record (List.mem_cons_of_mem _ hmem)
      cases hextract : ReferenceCollectionSegmentExtraction.extractRound record with
      | none => simp [hextract] at hhead
      | some completed =>
          have hlength := ih htail
          simp only [ReferenceCollectionSegmentExtraction.completed,
            List.filterMap_cons, hextract, List.length_cons]
          simpa only [ReferenceCollectionSegmentExtraction.completed, Nat.succ_eq_add_one] using
            congrArg Nat.succ hlength

private theorem take_succ_eq_take_append_getElem
    {α : Type} (records : List α) (k : ℕ) (hk : k < records.length) :
    records.take (k + 1) = records.take k ++ [records[k]'hk] := by
  induction k generalizing records with
  | zero =>
      cases records with
      | nil => simp at hk
      | cons record rest => rfl
  | succ k ih =>
      cases records with
      | nil => simp at hk
      | cons record rest =>
          have hk' : k < rest.length := by simp at hk; omega
          change record :: rest.take (k + 1) =
            record :: (rest.take k ++ [rest[k]'hk'])
          exact congrArg (List.cons record) (ih rest hk')

private theorem calendarIndices_congr
    (T start₁ start₂ length₁ length₂ : ℕ)
    (hstart : start₁ = start₂) (hlength : length₁ = length₂)
    (hbound₁ : start₁ + length₁ ≤ T) (hbound₂ : start₂ + length₂ ≤ T) :
    CoordinatorCollectionLedger.calendarIndices T start₁ length₁ hbound₁ =
      CoordinatorCollectionLedger.calendarIndices T start₂ length₂ hbound₂ := by
  cases hstart
  cases hlength
  have hproof : hbound₁ = hbound₂ := Subsingleton.elim _ _
  cases hproof
  rfl

private theorem replayRecords?_some_length
    (ledger : CoordinatorCollectionLedger.Ledger p rate.eta.val rate.eta.property
      (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale)
    (arm : Fin p.K) (indices : List (Fin p.T)) (records : List (Bool × ℕ))
    (hrecords : CoordinatorCollectionLedger.replayRecords? ledger arm indices = some records) :
    records.length = indices.length := by
  induction indices generalizing records with
  | nil =>
      change some [] = some records at hrecords
      cases Option.some.inj hrecords
      rfl
  | cons index rest ih =>
      cases henabled : ledger.enabledHistory index with
      | none =>
          simp [CoordinatorCollectionLedger.replayRecords?, henabled] at hrecords
      | some enabled =>
          cases htail : CoordinatorCollectionLedger.replayRecords? ledger arm rest with
          | none =>
              simp [CoordinatorCollectionLedger.replayRecords?, henabled, htail] at hrecords
          | some tail =>
              have hcons :
                  (enabled && decide (CoordinatorCollectionLedger.sourceRound index <
                    ledger.freezeAt), CoordinatorCollectionLedger.bufferedArrival ledger arm index) :: tail =
                    records := by
                simpa [CoordinatorCollectionLedger.replayRecords?, henabled, htail] using hrecords
              rw [← hcons]
              have hlength := ih tail htail
              simp [hlength]

private theorem suppliedReplayRecords?_map
    (allInputs selectedInputs : List
      (CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val)))
    (arm : Fin p.K) (freezeAt : ℕ)
    (hmem : ∀ input ∈ selectedInputs, input ∈ allInputs)
    (hfind : ∀ input ∈ selectedInputs,
      CollectionBufferProvenance.findRoundInput? allInputs input.round = some input) :
    CollectionBufferProvenance.suppliedReplayRecords? allInputs arm freezeAt
        (selectedInputs.map CollectionCheckedExecution.RoundInput.round) =
      some (selectedInputs.map
        (fun input => CollectionBufferProvenance.suppliedReplayRecord input arm freezeAt)) := by
  induction selectedInputs with
  | nil => rfl
  | cons input rest ih =>
      have hheadMem : input ∈ allInputs := hmem input (by simp)
      have htailMem : ∀ input ∈ rest, input ∈ allInputs := by
        intro input hinput
        exact hmem input (by simp [hinput])
      have hheadFind := hfind input (by simp)
      have htailFind : ∀ input ∈ rest,
          CollectionBufferProvenance.findRoundInput? allInputs input.round = some input := by
        intro input hinput
        exact hfind input (by simp [hinput])
      simp [CollectionBufferProvenance.suppliedReplayRecords?, hheadFind,
        ih htailMem htailFind]

private theorem suppliedReplayRecord_eq_physicalQueueRecord
    (pre : ReferenceActivePhysicalStep.Ledger rate) (arm : Fin p.K)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed)
    (hcontext : CollectionBufferProvenance.collectionContext completed.context.preLedger =
      CollectionBufferProvenance.collectionContext pre) :
    CollectionBufferProvenance.suppliedReplayRecord completed.input arm pre.freezeAt =
      ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record := by
  obtain ⟨hraw, henabled⟩ :=
    ReferenceCollectionRawBufferHistory.actual_completed_input_raw_and_enabled
      record completed hextract
  have hround :=
    (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
      record completed hextract).2.1
  have hsigma : completed.context.preLedger.sigma = pre.sigma := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.1) hcontext
  have hcutoff : completed.context.preLedger.cutoff = pre.cutoff := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.2.1) hcontext
  have hfreeze : completed.context.preLedger.freezeAt = pre.freezeAt := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.2.2.1) hcontext
  have henabled' : completed.input.enabled =
      ReferenceActivePhysicalStep.collectionEnabled pre record.input.time := by
    rw [henabled]
    simp [ReferenceActivePhysicalStep.collectionEnabled, hsigma, hcutoff, hfreeze]
  rw [CollectionBufferProvenance.suppliedReplayRecord,
    ReferenceCollectionRawBufferHistory.physicalQueueRecord,
    hround, hraw, henabled']
  rfl

private theorem inputReplayRecord_map_eq_physicalQueueRecord_map
    (pre : ReferenceActivePhysicalStep.Ledger rate) (arm : Fin p.K)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hall : ∀ record ∈ records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true)
    (hcontext : ∀ record ∈ records,
      ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
          CollectionBufferProvenance.collectionContext completed.context.preLedger =
            CollectionBufferProvenance.collectionContext pre) :
    (ReferenceCollectionSegmentExtraction.inputs records).map
        (fun input => CollectionBufferProvenance.suppliedReplayRecord input arm pre.freezeAt) =
      records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := by
  induction records with
  | nil => rfl
  | cons record rest ih =>
      obtain ⟨completed, hextract, hcompletedContext⟩ := hcontext record (by simp)
      have htail : ∀ record ∈ rest,
          (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true := by
        intro record hmem
        exact hall record (by simp [hmem])
      have htailContext : ∀ record ∈ rest,
          ∃ completed,
            ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
              CollectionBufferProvenance.collectionContext completed.context.preLedger =
                CollectionBufferProvenance.collectionContext pre := by
        intro record hmem
        exact hcontext record (by simp [hmem])
      have hhead := suppliedReplayRecord_eq_physicalQueueRecord pre arm record
        completed hextract hcompletedContext
      simp only [ReferenceCollectionSegmentExtraction.inputs,
        ReferenceCollectionSegmentExtraction.completed, List.filterMap_cons,
        hextract, List.map_cons]
      congr 1
      change List.map (fun input => CollectionBufferProvenance.suppliedReplayRecord
          input arm pre.freezeAt) (ReferenceCollectionSegmentExtraction.inputs rest) =
        List.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) rest
      exact ih htail htailContext

private theorem suppliedReplayRecords?_eq_physicalQueueRecords
    (pre : ReferenceActivePhysicalStep.Ledger rate) (arm : Fin p.K)
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (hall : ∀ record ∈ records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true)
    (hcontext : ∀ record ∈ records,
      ∃ completed,
        ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
          CollectionBufferProvenance.collectionContext completed.context.preLedger =
            CollectionBufferProvenance.collectionContext pre)
    (hchron : CollectionCheckedExecution.chronologicalFrom pre.cursor
      (ReferenceCollectionSegmentExtraction.inputs records)) :
    CollectionBufferProvenance.suppliedReplayRecords?
        (ReferenceCollectionSegmentExtraction.inputs records) arm pre.freezeAt
        ((ReferenceCollectionSegmentExtraction.inputs records).map
          CollectionCheckedExecution.RoundInput.round) =
      some (records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)) := by
  have hfind : ∀ input ∈ ReferenceCollectionSegmentExtraction.inputs records,
      CollectionBufferProvenance.findRoundInput?
          (ReferenceCollectionSegmentExtraction.inputs records) input.round = some input := by
    intro input hinput
    exact CollectionBufferProvenance.chronologicalFrom_findRoundInput?_of_mem
      pre.cursor (ReferenceCollectionSegmentExtraction.inputs records) hchron input hinput
  calc
    CollectionBufferProvenance.suppliedReplayRecords?
        (ReferenceCollectionSegmentExtraction.inputs records) arm pre.freezeAt
        ((ReferenceCollectionSegmentExtraction.inputs records).map
          CollectionCheckedExecution.RoundInput.round) =
      some ((ReferenceCollectionSegmentExtraction.inputs records).map
        (fun input => CollectionBufferProvenance.suppliedReplayRecord input arm pre.freezeAt)) :=
      suppliedReplayRecords?_map _ _ arm pre.freezeAt (by intro input h; exact h) hfind
    _ = some (records.map (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)) := by
      rw [inputReplayRecord_map_eq_physicalQueueRecord_map pre arm records hall hcontext]

/-- Join one accepted UP replay to the exact physical records of its actual
segment. Earlier accepted or rejected UPs remain in the checked prefix. The
conditional inputs are only the actual run boundary and branch selectors;
no recorder law, cutoff truth, or global queue invariant is assumed. -/
theorem actual_accepted_up_physical_replay_join
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
      let record := segment.records[k]'hk
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
            record.output.coordinator.recording = some recording ∧
            CoordinatorRecorderComplementBridge.run
              (ReferenceActivePhysicalStep.collectionRecordingInput
                (ReferenceActivePhysicalStep.prepare record.input) completed.context.payload
                completed.context.started completed.context.weights) = some recording ∧
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
                sourceRound lastIndex = started.cursor ∧
                lastIndex = record.input.time ∧
                started.cursor - started.cutoff = k ∧
                started.assignment = initializer.assignment ∧
                started.sigma = initializer.sigma ∧
                started.cutoff = initializer.cutoff ∧
                started.freezeAt = initializer.freezeAt ∧
                started.baseScore = initializer.base ∧
                1 ≤ started.cutoff ∧ started.cutoff ≤ started.cursor ∧
                started.cursor ≤ p.T ∧
                prefixExecution.final.currentRegisters arm = none ∧
                started.currentRegisters arm = none ∧
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
                      [lastIndex]) =
                  some (past ++ [current]) ∧
                past = (segment.records.take k).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger arm) ∧
                current = ReferenceCollectionRawBufferHistory.physicalQueueRecord
                  segment.context.preLedger arm record ∧
                past ++ [current] = (segment.records.take (k + 1)).map
                  (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger arm) ∧
                (segment.records.take k).map
                    (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                      segment.context.preLedger arm) ++
                  [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                    segment.context.preLedger arm record] =
                  (segment.records.take (k + 1)).map
                    (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                      segment.context.preLedger arm) ∧
                finished.currentRegisters arm =
                  some ⟨(QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((segment.records.take k).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm) ++
                      [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm record])).2,
                    (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                      ((segment.records.take k).map
                        (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                          segment.context.preLedger arm) ++
                        [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                          segment.context.preLedger arm record])).1 -
                    (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                      ((segment.records.take k).map
                        (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                          segment.context.preLedger arm))).1⟩ ∧
                finished.increment arm =
                  (QueueReplay.replay (4 * rate.n) (0, M.val.q)
                    ((segment.records.take k).map
                      (ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm) ++
                      [ReferenceCollectionRawBufferHistory.physicalQueueRecord
                        segment.context.preLedger arm record])).1 ∧
                finished.cutoffRegisters arm =
                  some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
  let record := segment.records[k]'hk
  let pre := segment.context.preLedger
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
    offset segment hsegment).1
  have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed _ segment hbranch
  have hkLe : k ≤ segment.records.length := by omega
  have hkSucc : k + 1 ≤ segment.records.length := by omega
  obtain ⟨initializer, hinitializer, hcheckedStart, hwholeRun⟩ :=
    ReferenceCollectionRawBufferHistory.run_collection_raw_buffer_execution
      initial rows selected rewards start count span active hfirst offset segment hsegment
  obtain ⟨recording, started, decoded, bank, finished, hrecording, hrunRecorder,
      hstart, hreceive, hdecode, hfinish, hfinished, hinput⟩ :=
    ReferenceCollectionPrefixLedgerHistory.actual_accepted_round_calls
      record completed hextract haccepted M hparsed i hselected
  have hstartCollection :
      CoordinatorCollectionLedger.startCollectionChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside = .success pre := by
    simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hcheckedStart
  obtain ⟨prefixAccepted, hprefixFold⟩ :=
    ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
      initial rows selected rewards start count span active offset segment hsegment k hkLe
  let prefixFinal := ReferenceCollectionSegmentExtraction.endpointLedger pre
    (segment.records.take k)
  let prefixExecution : CollectionCheckedExecution.Execution p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale :=
    ⟨pre, prefixAccepted, prefixFinal⟩
  have hprefixRun :
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside (segment.inputs.take k) =
          .success prefixExecution := by
    simp [CollectionCheckedExecution.startAndRunChecked, hstartCollection, hprefixFold,
      prefixExecution, prefixFinal, pre]
  have hprefixContext :=
    CollectionBufferProvenance.checkedRounds_success_preserves_context pre prefixFinal
      (segment.inputs.take k) prefixAccepted hprefixFold
  have hretained :=
    ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
      initial rows selected rewards start count span active offset segment hsegment k hk
      completed hextract
  have hround :=
    (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
      record completed hextract).2.1
  have hrawInput : completed.input.raw =
      CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recording := by
    rw [hinput]
    rfl
  have henabledInput : completed.input.enabled =
      ReferenceActivePhysicalStep.collectionEnabled completed.context.preLedger
        record.input.time := by
    rw [hinput]
    rfl
  have hstartPrefix :
      CoordinatorCollectionLedger.startRound prefixFinal
        (CoordinatorCollectionLedger.sourceRound completed.input.round)
        completed.input.enabled completed.input.raw = .success started := by
    dsimp only [prefixFinal, pre]
    rw [← hretained]
    rw [henabledInput, hrawInput]
    simpa [CoordinatorCollectionLedger.sourceRound, hround] using hstart
  have hinputsTakeK :=
    ReferenceCollectionPrefixLedgerHistory.run_collection_segment_prefix_inputs_take
      initial rows selected rewards start count span active offset segment hsegment k
  have hinputsTakeSucc :=
    ReferenceCollectionPrefixLedgerHistory.run_collection_segment_prefix_inputs_take
      initial rows selected rewards start count span active offset segment hsegment (k + 1)
  have hrecordTake : segment.records.take (k + 1) = segment.records.take k ++ [record] := by
    exact take_succ_eq_take_append_getElem segment.records k hk
  have hinputsAppend : segment.inputs.take (k + 1) =
      segment.inputs.take k ++ [completed.input] := by
    calc
      segment.inputs.take (k + 1) =
          ReferenceCollectionSegmentExtraction.inputs (segment.records.take (k + 1)) := hinputsTakeSucc
      _ = ReferenceCollectionSegmentExtraction.inputs (segment.records.take k) ++
            [completed.input] := by
          rw [hrecordTake]
          have hextractRecord :
              ReferenceCollectionSegmentExtraction.extractRound record = some completed := by
            simpa [record] using hextract
          simp [ReferenceCollectionSegmentExtraction.inputs,
            ReferenceCollectionSegmentExtraction.completed, hextractRecord]
      _ = segment.inputs.take k ++ [completed.input] := by rw [← hinputsTakeK]
  have hrecordExtracted : ∀ r ∈ segment.records.take (k + 1),
      (ReferenceCollectionSegmentExtraction.extractRound r).isSome = true := by
    intro r hr
    exact hgood r (List.mem_of_mem_take hr)
  have hprefixRecordsGood : ∀ r ∈ segment.records.take k,
      (ReferenceCollectionSegmentExtraction.extractRound r).isSome = true := by
    intro r hr
    exact hgood r (List.mem_of_mem_take hr)
  have hprefixSuccRecordsGood : ∀ r ∈ segment.records.take (k + 1),
      (ReferenceCollectionSegmentExtraction.extractRound r).isSome = true := by
    intro r hr
    exact hgood r (List.mem_of_mem_take hr)
  have hprefixRecordLength : (segment.records.take k).length = k := by
    simp [List.length_take, Nat.min_eq_left hkLe]
  have hprefixSuccRecordLength : (segment.records.take (k + 1)).length = k + 1 := by
    simp [List.length_take, Nat.min_eq_left hkSucc]
  have hinputLen : (segment.inputs.take k).length = k := by
    rw [hinputsTakeK]
    simpa [ReferenceCollectionSegmentExtraction.inputs] using
      (completed_length_of_all_extracted (segment.records.take k) hprefixRecordsGood).trans
        hprefixRecordLength
  have hinputSuccLen : (segment.inputs.take (k + 1)).length = k + 1 := by
    rw [hinputsTakeSucc]
    simpa [ReferenceCollectionSegmentExtraction.inputs] using
      (completed_length_of_all_extracted (segment.records.take (k + 1)) hprefixSuccRecordsGood).trans
        hprefixSuccRecordLength
  have hinitContext :=
    CollectionBufferProvenance.startCollectionChecked_success_context
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside pre hstartCollection
  have hstartContext :=
    CollectionBufferProvenance.startRound_success_context prefixFinal started
      (CoordinatorCollectionLedger.sourceRound completed.input.round)
      completed.input.enabled completed.input.raw hstartPrefix
  have hstartedContext :
      CollectionBufferProvenance.collectionContext started =
        CollectionBufferProvenance.collectionContext pre := by
    calc
      CollectionBufferProvenance.collectionContext started =
          CollectionBufferProvenance.collectionContext prefixFinal := hstartContext
      _ = CollectionBufferProvenance.collectionContext pre := hprefixContext
  have hstartedAssignmentPre : started.assignment = pre.assignment := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.1) hstartedContext
  have hstartedSigmaPre : started.sigma = pre.sigma := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.1) hstartedContext
  have hstartedCutoffPre : started.cutoff = pre.cutoff := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.2.1) hstartedContext
  have hstartedFreezePre : started.freezeAt = pre.freezeAt := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.2.2.1) hstartedContext
  have hstartedBasePre : started.baseScore = pre.baseScore := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.2.2.2.2) hstartedContext
  have hstartedAssignment : started.assignment = initializer.assignment :=
    hstartedAssignmentPre.trans hinitContext.1
  have hstartedSigma : started.sigma = initializer.sigma :=
    hstartedSigmaPre.trans hinitContext.2.1
  have hstartedCutoffInitializer : started.cutoff = initializer.cutoff :=
    hstartedCutoffPre.trans hinitContext.2.2.2.1
  have hstartedCutoff : started.cutoff = pre.cursor := by
    rw [hstartedCutoffInitializer, hinitContext.2.2.1]
  have hstartedFreeze : started.freezeAt = initializer.freezeAt :=
    hstartedFreezePre.trans hinitContext.2.2.2.2.1
  have hstartedBase : started.baseScore = initializer.base :=
    hstartedBasePre.trans hinitContext.2.2.2.2.2
  have hstartedAssignmentPrefix : started.assignment = prefixFinal.assignment := by
    simpa [CollectionBufferProvenance.collectionContext] using
      congrArg (fun c => c.1) hstartContext
  have hprefixChronology :=
    CollectionCheckedExecution.startAndRunChecked_success_chronology p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside (segment.inputs.take k) prefixExecution hprefixRun
  have hprefixCursor : prefixFinal.cursor = pre.cursor + k := by
    simpa [prefixExecution, hinputLen] using hprefixChronology.1
  have hstartCursor := CollectionCheckedExecution.startRound_success_cursor prefixFinal
    started (CoordinatorCollectionLedger.sourceRound completed.input.round)
    completed.input.enabled completed.input.raw hstartPrefix
  have hstartTime := CollectionCheckedExecution.startRound_success_time prefixFinal
    started (CoordinatorCollectionLedger.sourceRound completed.input.round)
    completed.input.enabled completed.input.raw hstartPrefix
  have hstartedCursor : started.cursor = pre.cursor + k := by
    calc
      started.cursor = CoordinatorCollectionLedger.sourceRound completed.input.round := hstartCursor
      _ = prefixFinal.cursor := hstartTime
      _ = pre.cursor + k := hprefixCursor
  have hcursorDifference : started.cursor - started.cutoff = k := by
    omega
  have hdecodeBounds :=
    CollectionBufferProvenance.decodeUp_success_input_bounds started decoded i M hdecode
  have hcutoffPositive : 1 ≤ started.cutoff := hdecodeBounds.1
  have hcutoffLe : started.cutoff ≤ started.cursor := hdecodeBounds.2.1
  have hcursorLe : started.cursor ≤ p.T := hdecodeBounds.2.2
  have hboundPast : pre.cursor - 1 + (segment.inputs.take k).length ≤ p.T := by
    rw [hinputLen]
    omega
  have hboundAll : pre.cursor - 1 + (segment.inputs.take (k + 1)).length ≤ p.T := by
    rw [hinputSuccLen]
    omega
  have hcalendarPast :=
    ReferenceCollectionPrefixLedgerHistory.run_collection_segment_prefix_calendar_indices
      initial rows selected rewards start count span active offset segment hsegment k hkLe hboundPast
  have hcalendarAll :=
    ReferenceCollectionPrefixLedgerHistory.run_collection_segment_prefix_calendar_indices
      initial rows selected rewards start count span active offset segment hsegment
      (k + 1) hkSucc hboundAll
  obtain ⟨_, _, _, _, _, _, _, hstartedUnknownOnce, _, _, _⟩ :=
    CollectionCheckedExecution.checked_acceptance_finish_once prefixFinal started decoded
      finished (CoordinatorCollectionLedger.sourceRound completed.input.round)
      completed.input.enabled completed.input.raw i M hstartPrefix hdecode hfinish
  have hprefixUnknown : prefixFinal.currentRegisters (prefixFinal.assignment.arm i) = none := by
    have hreflect := CollectionBufferProvenance.startRound_success_unknown_reflects
      prefixFinal started (CoordinatorCollectionLedger.sourceRound completed.input.round)
      completed.input.enabled completed.input.raw (started.assignment.arm i)
      hstartPrefix hstartedUnknownOnce
    rw [hstartedAssignmentPrefix] at hreflect
    exact hreflect
  have hunknownExecution : prefixExecution.final.currentRegisters
      (prefixExecution.final.assignment.arm i) = none := by
    simpa [prefixExecution, prefixFinal] using hprefixUnknown
  have hdecodeRecords :=
    CollectionBufferProvenance.successful_decode_records_are_replayRecords
      initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
      initializer.base initializer.outside (segment.inputs.take k) prefixExecution
      completed.input started decoded finished i M hprefixRun hunknownExecution
      hstartPrefix hdecode hfinish
  obtain ⟨hbound, lastIndex, hlastSource, past, current, hpast, hlast,
      hsuppplied, _, hcurrent, hincrement, hcutoff⟩ := hdecodeRecords
  let arm := started.assignment.arm i
  have hdecoderPrefixIndices :
      CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff) hbound =
        CoordinatorCollectionLedger.calendarIndices p.T (pre.cursor - 1)
          (segment.inputs.take k).length hboundPast := by
    exact calendarIndices_congr p.T (started.cutoff - 1) (pre.cursor - 1)
      (started.cursor - started.cutoff) (segment.inputs.take k).length
      (by omega) (by rw [hcursorDifference, hinputLen]) hbound hboundPast
  have hcalendarPastInputs :
      CoordinatorCollectionLedger.calendarIndices p.T (pre.cursor - 1)
          (segment.inputs.take k).length hboundPast =
        (segment.inputs.take k).map CollectionCheckedExecution.RoundInput.round := hcalendarPast
  have hcalendarAllInputs :
      CoordinatorCollectionLedger.calendarIndices p.T (pre.cursor - 1)
          (segment.inputs.take (k + 1)).length hboundAll =
        (segment.inputs.take (k + 1)).map CollectionCheckedExecution.RoundInput.round := hcalendarAll
  have hround :=
    (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
      record completed hextract).2.1
  have hlastIndex : lastIndex = record.input.time := by
    apply Fin.ext
    have hcurrentSource : record.input.time.val + 1 = started.cursor := by
      calc
        record.input.time.val + 1 =
            CoordinatorCollectionLedger.sourceRound completed.input.round := by
              rw [← hround]
              rfl
        _ = started.cursor := hstartCursor.symm
    dsimp [CoordinatorCollectionLedger.sourceRound] at hlastSource hcurrentSource ⊢
    omega
  have hlastInputRound : lastIndex = completed.input.round := by
    calc
      lastIndex = record.input.time := hlastIndex
      _ = completed.input.round := hround.symm
  have hindicesAppendAll :
      CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff) hbound ++ [lastIndex] =
        (segment.inputs.take (k + 1)).map CollectionCheckedExecution.RoundInput.round := by
    calc
      CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff) hbound ++ [lastIndex] =
        CoordinatorCollectionLedger.calendarIndices p.T (pre.cursor - 1)
          (segment.inputs.take k).length hboundPast ++ [lastIndex] :=
            congrArg (fun xs => xs ++ [lastIndex]) hdecoderPrefixIndices
      _ = (segment.inputs.take k).map CollectionCheckedExecution.RoundInput.round ++
            [completed.input.round] := by
          rw [hcalendarPastInputs]
          simp [hlastInputRound]
      _ = (segment.inputs.take (k + 1)).map CollectionCheckedExecution.RoundInput.round := by
          simp [hinputsAppend, List.map_append]
  have hindices :
      CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
          (started.cursor - started.cutoff) hbound ++ [lastIndex] =
        (segment.inputs.take k ++ [completed.input]).map
          CollectionCheckedExecution.RoundInput.round := by
    rw [hinputsAppend] at hindicesAppendAll
    exact hindicesAppendAll
  have hchronAll :=
    ReferenceCollectionPrefixLedgerHistory.run_collection_segment_prefix_chronology
      initial rows selected rewards start count span active offset segment hsegment
      (k + 1) hkSucc
  have hchronPhysical : CollectionCheckedExecution.chronologicalFrom pre.cursor
      (ReferenceCollectionSegmentExtraction.inputs (segment.records.take (k + 1))) := by
    rw [← hinputsTakeSucc]
    exact hchronAll
  have hrecordContext : ∀ r ∈ segment.records.take (k + 1),
      ∃ c, ReferenceCollectionSegmentExtraction.extractRound r = some c ∧
        CollectionBufferProvenance.collectionContext c.context.preLedger =
          CollectionBufferProvenance.collectionContext pre := by
    intro r hr
    obtain ⟨j, hj, hget⟩ := List.mem_iff_getElem.mp hr
    have hjLe : j ≤ k := by simp only [List.length_take] at hj; omega
    have hjSeg : j < segment.records.length := by omega
    have hindexRecord : (segment.records.take (k + 1))[j] = segment.records[j]'hjSeg := by
      simp [List.getElem_take]
    have hrecordEq : r = segment.records[j]'hjSeg := hget.symm.trans hindexRecord
    have hsome := hgood r (List.mem_of_mem_take hr)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    have hcIndex :
        ReferenceCollectionSegmentExtraction.extractRound (segment.records[j]'hjSeg) = some c := by
      simpa [hrecordEq] using hc
    have hretainedAtJ :=
      ReferenceCollectionPrefixLedgerHistory.retained_completed_preledger
        initial rows selected rewards start count span active offset segment hsegment
        j hjSeg c hcIndex
    obtain ⟨acceptedAtJ, hfoldAtJ⟩ :=
      ReferenceCollectionPrefixLedgerHistory.run_segment_prefix_checked
        initial rows selected rewards start count span active offset segment hsegment j
        (by omega)
    have hcontextAtJ :=
      CollectionBufferProvenance.checkedRounds_success_preserves_context pre
        (ReferenceCollectionSegmentExtraction.endpointLedger pre
          (segment.records.take j)) (segment.inputs.take j) acceptedAtJ hfoldAtJ
    exact ⟨c, hc, by
      calc
        CollectionBufferProvenance.collectionContext c.context.preLedger =
            CollectionBufferProvenance.collectionContext
              (ReferenceCollectionSegmentExtraction.endpointLedger pre
                (segment.records.take j)) := congrArg
                  CollectionBufferProvenance.collectionContext hretainedAtJ
        _ = CollectionBufferProvenance.collectionContext pre := hcontextAtJ⟩
  have hrecordExtracted : ∀ r ∈ segment.records.take (k + 1),
      (ReferenceCollectionSegmentExtraction.extractRound r).isSome = true := by
    intro r hr
    exact hgood r (List.mem_of_mem_take hr)
  have hphysicalSupplied :=
    suppliedReplayRecords?_eq_physicalQueueRecords pre arm
      (segment.records.take (k + 1)) hrecordExtracted hrecordContext hchronPhysical
  have hinputList : segment.inputs.take k ++ [completed.input] =
      ReferenceCollectionSegmentExtraction.inputs (segment.records.take (k + 1)) := by
    calc
      segment.inputs.take k ++ [completed.input] = segment.inputs.take (k + 1) :=
        hinputsAppend.symm
      _ = ReferenceCollectionSegmentExtraction.inputs (segment.records.take (k + 1)) :=
        hinputsTakeSucc
  have hphysicalSuppliedFull :
      CollectionBufferProvenance.suppliedReplayRecords?
          (segment.inputs.take k ++ [completed.input]) arm pre.freezeAt
          ((segment.inputs.take k ++ [completed.input]).map
            CollectionCheckedExecution.RoundInput.round) =
        some ((segment.records.take (k + 1)).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)) := by
    have hphysicalSupplied' := hphysicalSupplied
    rw [← hinputList] at hphysicalSupplied'
    exact hphysicalSupplied'
  have hdecodeSuppliedPhysical :
      CollectionBufferProvenance.suppliedReplayRecords?
          (segment.inputs.take k ++ [completed.input]) arm pre.freezeAt
          ((CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hbound) ++ [lastIndex]) =
        some ((segment.records.take (k + 1)).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)) := by
    rw [hindices]
    exact hphysicalSuppliedFull
  have hsuppliedActual :
      CollectionBufferProvenance.suppliedReplayRecords?
          (segment.inputs.take k ++ [completed.input]) arm pre.freezeAt
          ((CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hbound) ++ [lastIndex]) =
        some (past ++ [current]) := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix,
      hstartedFreezePre, hindices] using hsuppplied
  have hphysicalList : past ++ [current] =
      (segment.records.take (k + 1)).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) :=
    Option.some.inj (hsuppliedActual.symm.trans hdecodeSuppliedPhysical)
  have hmapSplit :
      (segment.records.take (k + 1)).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) =
        (segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
          [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record] := by
    rw [hrecordTake]
    simp [List.map_append]
  have hwholeSplit := hphysicalList.trans hmapSplit
  have hpastStarted :
      CoordinatorCollectionLedger.replayRecords? started arm
          (CoordinatorCollectionLedger.calendarIndices p.T
            (started.cutoff - 1) (started.cursor - started.cutoff) hbound) = some past := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hpast
  have hlastStarted :
      CoordinatorCollectionLedger.replayRecords? started arm [lastIndex] = some [current] := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hlast
  have hsupppliedStarted :
      CollectionBufferProvenance.suppliedReplayRecords?
          (segment.inputs.take k ++ [completed.input]) arm started.freezeAt
          ((CoordinatorCollectionLedger.calendarIndices p.T (started.cutoff - 1)
            (started.cursor - started.cutoff) hbound) ++ [lastIndex]) =
        some (past ++ [current]) := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hsuppplied
  have hcurrentStarted : finished.currentRegisters arm =
      some ⟨(QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [current])).2,
        (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [current])).1 -
          (QueueReplay.replay (4 * rate.n) (0, M.val.q) past).1⟩ := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hcurrent
  have hincrementStarted : finished.increment arm =
      (QueueReplay.replay (4 * rate.n) (0, M.val.q) (past ++ [current])).1 := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hincrement
  have hcutoffStarted : finished.cutoffRegisters arm =
      some ⟨started.baseScore i + M.val.S, M.val.q, M.val.delta⟩ := by
    simpa [arm, prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hcutoff
  have hpastLen : past.length = k := by
    calc
      past.length = (CoordinatorCollectionLedger.calendarIndices p.T
          (started.cutoff - 1) (started.cursor - started.cutoff) hbound).length :=
            replayRecords?_some_length started arm _ past hpastStarted
      _ = started.cursor - started.cutoff :=
            CoordinatorCollectionLedger.calendarIndices_length p.T _ _ hbound
      _ = k := hcursorDifference
  have hphysicalPastLen :
      ((segment.records.take k).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)).length = k := by
    simp only [List.length_map, List.length_take]
    omega
  have htakeLeft : (past ++ [current]).take k = past := by
    simp [hpastLen]
  have htakeRight :
      ((segment.records.take k).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
          [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record]).take k =
        (segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := by
    rw [List.take_append]
    have hprefixTake :
        ((segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)).take k =
          (segment.records.take k).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) :=
      List.take_of_length_le (by omega)
    have hcurrentTake :
        ([ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record]).take
          (k - ((segment.records.take k).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm)).length) = [] := by
      rw [hphysicalPastLen]
      simp
    rw [hprefixTake, hcurrentTake]
    simp
  have hpastPhysical : past = (segment.records.take k).map
      (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := by
    calc
      past = (past ++ [current]).take k := htakeLeft.symm
      _ = ((segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
            [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record]).take k :=
          congrArg (fun records => records.take k) hwholeSplit
      _ = (segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := htakeRight
  have hcurrentPhysical : current =
      ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record := by
    rw [hpastPhysical] at hwholeSplit
    have hsingle := List.append_cancel_left hwholeSplit
    injection hsingle
  have hconcatPhysical :
      (segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
        [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record] =
      (segment.records.take (k + 1)).map
        (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) := hmapSplit.symm
  have hfinishedCurrentPhysical : finished.currentRegisters arm =
      some ⟨(QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((segment.records.take k).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
            [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record])).2,
        (QueueReplay.replay (4 * rate.n) (0, M.val.q)
          ((segment.records.take k).map
            (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
            [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record])).1 -
          (QueueReplay.replay (4 * rate.n) (0, M.val.q)
            ((segment.records.take k).map
              (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm))).1⟩ := by
    simpa [hpastPhysical, hcurrentPhysical] using hcurrentStarted
  have hfinishedIncrementPhysical : finished.increment arm =
      (QueueReplay.replay (4 * rate.n) (0, M.val.q)
        ((segment.records.take k).map
          (ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm) ++
          [ReferenceCollectionRawBufferHistory.physicalQueueRecord pre arm record])).1 := by
    simpa [hpastPhysical, hcurrentPhysical] using hincrementStarted
  refine ⟨initializer, hinitializer, hcheckedStart, hwholeRun,
    prefixExecution, hprefixRun, rfl, rfl,
    recording, started, decoded, bank, finished, hrecording,
    (by simpa [record] using hrunRecorder),
    (by simpa [record] using hstart),
    (by simpa [record] using hreceive), hdecode, hfinish, hfinished,
    (by simpa [record] using hinput), ?_⟩
  dsimp only [arm]
  refine ⟨hbound, lastIndex, hlastSource, hlastIndex, hcursorDifference,
    hstartedAssignment, hstartedSigma, hstartedCutoffInitializer,
    hstartedFreeze, hstartedBase, hcutoffPositive, hcutoffLe, hcursorLe,
    ?_, ?_, past, current, hpastStarted, hlastStarted, hsupppliedStarted,
    hpastPhysical, hcurrentPhysical, hphysicalList, hconcatPhysical,
    hfinishedCurrentPhysical, hfinishedIncrementPhysical, hcutoffStarted⟩
  · simpa [prefixExecution, prefixFinal, hstartedAssignmentPrefix] using hprefixUnknown
  · simpa [arm] using hstartedUnknownOnce
end Bandits.Support.ReferenceCollectionUpReplayHistory

end
