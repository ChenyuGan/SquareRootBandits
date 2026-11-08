/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionSegmentExtraction
public import Bandits.Support.CollectionBufferProvenance
public import Bandits.Support.ReferenceCoordinatorCollectionRecording

/-!
# Physical collection arrivals and raw-buffer history

The source evidence is `sources/zip4/manuscript/05_binary_transport.tex:354-396`,
`sources/zip4/manuscript/06_interruptions.tex:80-100,246-269,277-294`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:46-64`. These are
internal physical-history results; they do not establish global queue, score,
or regret identities.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionRawBufferHistory

open ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CollectionCheckedExecution
open Bandits.Support.OrdinaryMessageCodec

variable {p : Parameters} {rate : ReferenceActivePhysicalStep.RateInput p}

/-- The literal raw diagnostic stored on a physical record. A zero arrival
with an arm remains present, while `none` records actual absence. -/
def rawDiagnostic
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (Fin p.K × ℕ) :=
  record.output.coordinator.recording.bind fun output =>
    output.gateArm.map fun arm => (arm, output.rawArrival)

/-- The physical queue input projected from an existing collection record.
The marker and arrival are kept separate, and the frozen tail supplies a zero
arrival while leaving the physical record intact. -/
def physicalQueueRecord (pre : ReferenceActivePhysicalStep.Ledger rate)
    (arm : Fin p.K)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Bool × ℕ :=
  (ReferenceActivePhysicalStep.collectionEnabled pre record.input.time &&
      decide (record.input.time.val + 1 < pre.freezeAt),
    if record.input.time.val + 1 < pre.freezeAt then
      localArrival (rawDiagnostic record) arm else 0)

/-- The extractor's checked input keeps the actual recorder gate/raw pair and
the literal collection enable bit from the physical row. -/
theorem actual_completed_input_raw_and_enabled
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed) :
    completed.input.raw = rawDiagnostic record ∧
      completed.input.enabled = ReferenceActivePhysicalStep.collectionEnabled
        completed.context.preLedger record.input.time := by
  obtain ⟨recording, started, decoded, bank, hrecording, _, _, hinput, _, _⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_inputs record completed hextract
  have hrecordingStep :
      (ReferenceActivePhysicalStep.step record.input).coordinator.recording = some recording := by
    simpa only [record.output_eq] using hrecording
  constructor
  · calc
      completed.input.raw =
          (ReferenceCollectionSegmentExtraction.inputOf record.input completed.context.preLedger
            recording started).raw := congrArg CollectionCheckedExecution.RoundInput.raw hinput
      _ = recording.gateArm.map (fun arm => (arm, recording.rawArrival)) :=
        ReferenceCollectionSegmentExtraction.inputOf_raw_gate record.input
          completed.context.preLedger started recording
      _ = rawDiagnostic record := by
        simp [rawDiagnostic, record.output_eq, hrecordingStep]
  · rw [hinput]
    rfl

/-- The successful extraction names the exact physical recorder output used by
the checked input. This is a proposition-valued projection of the actual
round, not a recorder-success premise. -/
theorem actual_completed_input_recording
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed) :
    ∃ output,
      record.output.coordinator.recording = some output ∧
      completed.input.raw = output.gateArm.map (fun arm => (arm, output.rawArrival)) ∧
      completed.input.enabled = ReferenceActivePhysicalStep.collectionEnabled
        completed.context.preLedger record.input.time := by
  obtain ⟨output, started, decoded, bank, hrecording, _, _, hinput, _, _⟩ :=
    ReferenceCollectionSegmentExtraction.actual_collection_round_inputs record completed hextract
  refine ⟨output, hrecording, ?_, ?_⟩
  · calc
      completed.input.raw =
          (ReferenceCollectionSegmentExtraction.inputOf record.input completed.context.preLedger
            output started).raw := congrArg CollectionCheckedExecution.RoundInput.raw hinput
      _ = output.gateArm.map (fun arm => (arm, output.rawArrival)) :=
        ReferenceCollectionSegmentExtraction.inputOf_raw_gate record.input
          completed.context.preLedger started output
  · rw [hinput]
    rfl

private theorem retained_completed_input
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hgood : ∀ record ∈ segment.records,
      (ReferenceCollectionSegmentExtraction.extractRound record).isSome = true)
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hrecord : record ∈ segment.records) :
    ∃ completed, ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      completed.input ∈ segment.inputs ∧
      completed.input.round = record.input.time ∧
      completed.input.raw = rawDiagnostic record ∧
      completed.input.enabled = ReferenceActivePhysicalStep.collectionEnabled
        completed.context.preLedger record.input.time := by
  cases hextract : ReferenceCollectionSegmentExtraction.extractRound record with
  | none => have hfalse := hgood record hrecord; simp [hextract] at hfalse
  | some completed =>
      have hround := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
        record completed hextract).2.1
      have hrawEnabled := actual_completed_input_raw_and_enabled record completed hextract
      have hmemCompleted : completed ∈
          ReferenceCollectionSegmentExtraction.completed segment.records :=
        List.mem_filterMap.mpr ⟨record, hrecord, hextract⟩
      have hmemInput : completed.input ∈ segment.inputs := by
        change completed.input ∈
          (ReferenceCollectionSegmentExtraction.completed segment.records).map
            ReferenceCollectionSegmentExtraction.CompletedRound.input
        exact List.mem_map.mpr ⟨completed, hmemCompleted, rfl⟩
      exact ⟨completed, rfl, hmemInput, hround, hrawEnabled.1, hrawEnabled.2⟩

private theorem retained_record_of_input
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (input : CollectionCheckedExecution.RoundInput (p := p) (eta := rate.eta.val))
    (hinput : input ∈ segment.inputs) :
    ∃ record ∈ segment.records, ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      completed.input = input := by
  change input ∈
    (ReferenceCollectionSegmentExtraction.completed segment.records).map
      ReferenceCollectionSegmentExtraction.CompletedRound.input at hinput
  obtain ⟨completed, hcompleted, hinputEq⟩ := List.mem_map.mp hinput
  obtain ⟨record, hrecord, hextract⟩ := List.mem_filterMap.mp hcompleted
  refine ⟨record, hrecord, completed, hextract, ?_⟩
  exact hinputEq

private theorem run_segment_record_time_injective
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment)
    (left right : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hleft : left ∈ segment.records) (hright : right ∈ segment.records)
    (htime : left.input.time = right.input.time) : left = right := by
  let run := ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    run.records offset segment hsegment).1
  have hpartition := ReferenceCollectionSegmentExtraction.segment_partition
    (run.records.drop offset) segment hbranch
  have hleftDrop : left ∈ run.records.drop offset := by
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hleft)
  have hrightDrop : right ∈ run.records.drop offset := by
    rw [← hpartition]
    exact List.mem_append.mpr (Or.inl hright)
  have hleftRun : left ∈ run.records := List.mem_of_mem_drop hleftDrop
  have hrightRun : right ∈ run.records := List.mem_of_mem_drop hrightDrop
  have hrunTimes := ReferenceActivePhysicalHorizon.run_time_values
    initial rows selected rewards start count span active
  have htimesNodup : (run.records.map fun record => record.input.time.val).Nodup := by
    rw [hrunTimes]
    simp [ReferenceActivePhysicalHorizon.calendar, List.nodup_range']
  apply List.inj_on_of_nodup_map htimesNodup hleftRun hrightRun
  exact congrArg Fin.val htime

private theorem segment_entry_choice
    (records : List (ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)))
    (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segment records = some segment) :
    ReferenceCollectionSegmentExtraction.choice segment.entry.input = some segment.context := by
  cases records with
  | nil => simp [ReferenceCollectionSegmentExtraction.segment] at hsegment
  | cons entry rest =>
      unfold ReferenceCollectionSegmentExtraction.segment at hsegment
      cases hchoice : ReferenceCollectionSegmentExtraction.choice entry.input with
      | none => simp [hchoice] at hsegment
      | some context =>
          simp only [hchoice, Option.map_some] at hsegment
          split at hsegment <;> cases Option.some.inj hsegment <;> exact hchoice


theorem run_collection_raw_buffer_execution
    (initial : ReferenceActivePhysicalStep.State p rate)
    (rows : CompletePublicTable.CompleteRows p) (selected : Fin (M p))
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (start count : ℕ) (span : start + count ≤ p.T)
    (active : ReferenceActivePhysicalHorizon.allActiveAtStart initial start)
    (hfirst : initial.coordinator = .first)
    (offset : ℕ) (segment : ReferenceCollectionSegmentExtraction.Segment rate)
    (hsegment : ReferenceCollectionSegmentExtraction.segmentAt
      (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
      offset = some segment) :
    ∃ initializer : ReferenceCollectionSegmentExtraction.Initializer p,
      segment.context.initializer = some initializer ∧
      initializer.checkedStart rate = .success segment.context.preLedger ∧
      CollectionCheckedExecution.startAndRunChecked p rate.eta.val rate.eta.property
        (ReferenceUpReception.sourceCap_forLedger rate) rate.n rate.n_scale
        initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
        initializer.base initializer.outside segment.inputs =
          .success ⟨segment.context.preLedger, segment.accepted, segment.final⟩ := by
  obtain ⟨initializer, hinitializer, hrun⟩ :=
    ReferenceCollectionSegmentExtraction.run_collection_initialized_segment_at
      initial rows selected rewards start count span active hfirst offset segment hsegment
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
    offset segment hsegment).1
  have hchoice := segment_entry_choice _ segment hbranch
  have hchecked := ReferenceCollectionSegmentExtraction.choice_initializer
    segment.entry.input segment.context initializer hchoice hinitializer
  exact ⟨initializer, hinitializer, hchecked, hrun⟩

/-- The successful checked collection fold identifies every positive raw-buffer
cell with its unique retained physical recorder row before the actual freeze
boundary. The checked initializer, full fold, retained enable history, and
empty frozen/out-of-interval cells all come from the accepted physical segment.
No accepted-UP exclusion is used. -/
theorem run_collection_raw_buffer_history
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
    (arm : Fin p.K) (hunknown : segment.final.currentRegisters arm = none)
    (round : Fin p.T) (amount : ℕ) :
    (segment.final.rawBuffer arm round = some amount ↔
      ∃ record ∈ segment.records, record.input.time = round ∧
        ∃ output,
          record.output.coordinator.recording = some output ∧
          output.gateArm = some arm ∧ output.rawArrival = amount ∧
          0 < amount ∧ round.val + 1 < segment.context.preLedger.freezeAt) ∧
    (∀ record ∈ segment.records, ∃ completed,
      ReferenceCollectionSegmentExtraction.extractRound record = some completed ∧
      segment.final.enabledHistory completed.input.round = some completed.input.enabled) ∧
    (∀ r, CoordinatorCollectionLedger.sourceRound r <
        segment.context.preLedger.cursor → segment.final.rawBuffer arm r = none) ∧
    (∀ r, segment.context.preLedger.freezeAt ≤
        CoordinatorCollectionLedger.sourceRound r → segment.final.rawBuffer arm r = none) ∧
    (∀ r, segment.final.cursor ≤ CoordinatorCollectionLedger.sourceRound r →
        segment.final.rawBuffer arm r = none) ∧
    (∀ left right, left ∈ segment.records → right ∈ segment.records →
      left.input.time = right.input.time → left = right) := by
  obtain ⟨initializer, hinitializer, hchecked, hrun⟩ :=
    run_collection_raw_buffer_execution initial rows selected rewards start count span
      active hfirst offset segment hsegment
  let execution : CollectionCheckedExecution.Execution p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n
      rate.n_scale := ⟨segment.context.preLedger, segment.accepted, segment.final⟩
  have hRun : CollectionCheckedExecution.startAndRunChecked p rate.eta.val
      rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate) rate.n
      rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
      initializer.freezeAt initializer.base initializer.outside segment.inputs =
      .success execution := by
    simpa [execution] using hrun
  have hbuffer := CollectionBufferProvenance.startAndRunChecked_success_unknown_buffer
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside segment.inputs execution arm hRun
    (by simpa [execution] using hunknown)
  rcases hbuffer with ⟨_, hinitialCursor, _, _, _, _, _, henables,
    _, hformula, hfreezeEmpty, houtsideEmpty, _⟩
  have hinitContext := CollectionBufferProvenance.startCollectionChecked_success_context
    initializer.assignment initializer.sigma initializer.cutoff initializer.freezeAt
    initializer.base initializer.outside segment.context.preLedger (by
      simpa [ReferenceCollectionSegmentExtraction.Initializer.checkedStart] using hchecked)
  rcases hinitContext with ⟨_, _, hpreCursor, _, hpreFreeze, _⟩
  have hbranch := (ReferenceCollectionSegmentExtraction.segmentAt_branch
    (ReferenceActivePhysicalHorizon.run initial rows selected rewards start count span active).records
    offset segment hsegment).1
  have hgood := ReferenceCollectionSegmentExtraction.segment_all_completed
    _ segment hbranch
  have hchron := CollectionCheckedExecution.startAndRunChecked_success_input_chronology
    p rate.eta.val rate.eta.property (ReferenceUpReception.sourceCap_forLedger rate)
    rate.n rate.n_scale initializer.assignment initializer.sigma initializer.cutoff
    initializer.freezeAt initializer.base initializer.outside segment.inputs execution hRun
  have hcell := hformula round
  have hfreezeBoundary : segment.context.preLedger.freezeAt = initializer.freezeAt := hpreFreeze
  have hiff : segment.final.rawBuffer arm round = some amount ↔
      ∃ record ∈ segment.records, record.input.time = round ∧
        ∃ output,
          record.output.coordinator.recording = some output ∧
          output.gateArm = some arm ∧ output.rawArrival = amount ∧
          0 < amount ∧ round.val + 1 < segment.context.preLedger.freezeAt := by
    constructor
    · intro hsome
      rw [hcell] at hsome
      cases hfind : CollectionBufferProvenance.findRoundInput? segment.inputs round with
      | none => simp [hfind] at hsome
      | some input =>
          have ⟨hinputMem, hinputRound⟩ :=
            CollectionBufferProvenance.findRoundInput?_spec segment.inputs round input hfind
          cases hraw : input.raw with
          | none => simp [hfind, hraw] at hsome
          | some pair =>
              rcases pair with ⟨rawArm, rawAmount⟩
              by_cases hcondition : rawArm = arm ∧ 0 < rawAmount ∧
                  CoordinatorCollectionLedger.sourceRound round < initializer.freezeAt
              · simp [hfind, hraw, hcondition] at hsome
                have hamount : rawAmount = amount := hsome
                obtain ⟨record, hrecord, completed, hextract, hcompletedInput⟩ :=
                  retained_record_of_input segment input hinputMem
                have hcompletedRound :=
                  (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
                    record completed hextract).2.1
                have hround : record.input.time = round := by
                  calc
                    record.input.time = completed.input.round := hcompletedRound.symm
                    _ = input.round := congrArg CollectionCheckedExecution.RoundInput.round
                      hcompletedInput
                    _ = round := hinputRound
                obtain ⟨output, hrecording, hrawInput, _⟩ :=
                  actual_completed_input_recording record completed hextract
                have hrawEq : completed.input.raw = input.raw :=
                  congrArg CollectionCheckedExecution.RoundInput.raw hcompletedInput
                have hgate : output.gateArm.map (fun a => (a, output.rawArrival)) =
                    some (rawArm, rawAmount) := by
                  calc
                    output.gateArm.map (fun a => (a, output.rawArrival)) = completed.input.raw :=
                      hrawInput.symm
                    _ = input.raw := hrawEq
                    _ = some (rawArm, rawAmount) := hraw
                cases hg : output.gateArm with
                | none => simp [hg] at hgate
                | some actualArm =>
                    simp [hg] at hgate
                    rcases hgate with ⟨hactualArm, hactualAmount⟩
                    have hgateArm : output.gateArm = some arm := by
                      rw [hg, hactualArm.trans hcondition.1]
                    have harrival : output.rawArrival = amount :=
                      hactualAmount.trans hamount
                    have hpositiveAmount : 0 < amount := by omega
                    refine ⟨record, hrecord, hround, output, hrecording, hgateArm,
                      harrival, hpositiveAmount, ?_⟩
                    simpa [CoordinatorCollectionLedger.sourceRound, hfreezeBoundary] using
                      hcondition.2.2
              · simp [hfind, hraw, hcondition] at hsome
    · rintro ⟨record, hrecord, hround, output, hrecording, hgate, harrival,
        hpositive, hbefore⟩
      have ⟨completed, hextract, hinputMem, hcompletedRound, hraw, _⟩ :=
        retained_completed_input segment hgood record hrecord
      have hfind : CollectionBufferProvenance.findRoundInput? segment.inputs
          completed.input.round = some completed.input :=
        CollectionBufferProvenance.chronologicalFrom_findRoundInput?_of_mem
          execution.initial.cursor segment.inputs hchron completed.input hinputMem
      have hfindRound : CollectionBufferProvenance.findRoundInput? segment.inputs round =
          some completed.input := by
        have hr : completed.input.round = round := hcompletedRound.trans hround
        rw [← hr]
        exact hfind
      have hrawInput : completed.input.raw = some (arm, amount) := by
        calc
          completed.input.raw = rawDiagnostic record := hraw
          _ = output.gateArm.map (fun a => (a, output.rawArrival)) := by
            simp [rawDiagnostic, hrecording]
          _ = some (arm, amount) := by simp [hgate, harrival]
      have hbeforeInit : CoordinatorCollectionLedger.sourceRound round < initializer.freezeAt := by
        simpa [CoordinatorCollectionLedger.sourceRound, hfreezeBoundary] using hbefore
      rw [hcell, hfindRound]
      simp [hrawInput, hbeforeInit, hpositive]
  have hbeforeInitialEmpty : ∀ r,
      CoordinatorCollectionLedger.sourceRound r < segment.context.preLedger.cursor →
        segment.final.rawBuffer arm r = none := by
    intro r hbefore
    have hinitialToPreCursor : execution.initial.cursor = segment.context.preLedger.cursor := by
      calc
        execution.initial.cursor = initializer.cutoff := hinitialCursor
        _ = segment.context.preLedger.cursor := hpreCursor.symm
    exact houtsideEmpty r (Or.inl (by rw [hinitialToPreCursor]; exact hbefore))
  refine ⟨hiff, ?_, hbeforeInitialEmpty, ?_, ?_, ?_⟩
  · intro record hrecord
    obtain ⟨completed, hextract, hinputMem, _, _, _⟩ :=
      retained_completed_input segment hgood record hrecord
    exact ⟨completed, hextract, henables completed.input hinputMem⟩
  · intro r hafter
    exact hfreezeEmpty r (by simpa [hfreezeBoundary] using hafter)
  · intro r hafter
    exact houtsideEmpty r (Or.inr hafter)
  · intro left right hleft hright htime
    exact run_segment_record_time_injective initial rows selected rewards start count
      span active offset segment hsegment left right hleft hright htime

/-- On one actual retained collection round, ordinary and unoccupied follower
statuses are explicit local inputs. The recorder, collection marker, and
physical floor are derived from the retained extraction and actual dispatch. -/
theorem actual_collection_record_queueInput
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (completed : ReferenceCollectionSegmentExtraction.CompletedRound rate)
    (hextract : ReferenceCollectionSegmentExtraction.extractRound record = some completed)
    (states : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memories : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hordinary : ∀ i,
      ((ReferenceActivePhysicalStep.prepare record.input).followers.followers i).configuration =
        .ordinary (states i) (memories i))
    (hunoccupied : ∀ i, (states i).status = .unoccupied)
    (arm : Fin p.K) :
    ∃ output,
      record.output.coordinator.recording = some output ∧
      rawDiagnostic record = output.gateArm.map (fun j => (j, output.rawArrival)) ∧
      completed.input.raw = rawDiagnostic record ∧
      completed.input.enabled = ReferenceActivePhysicalStep.collectionEnabled
        completed.context.preLedger record.input.time ∧
      (∃ enabled,
        enabled = ReferenceActivePhysicalStep.collectionEnabled
          completed.context.preLedger record.input.time ∧
        physicalQueueRecord completed.context.preLedger arm record =
          (enabled && decide (record.input.time.val + 1 < completed.context.preLedger.freezeAt),
            if record.input.time.val + 1 < completed.context.preLedger.freezeAt then
              localArrival
                (output.gateArm.map fun j =>
                  (j, Nat.floor ((D p : ℝ) * rate.eta.val *
                    RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                      (record.input.rewards record.input.time j) /
                    CanonicalRecordingRates.xi p rate.eta.val
                      completed.context.payload.anchor j))) arm
            else 0)) := by
  classical
  have hinput := actual_completed_input_raw_and_enabled record completed hextract
  have hchoice := (ReferenceCollectionSegmentExtraction.actual_collection_round_checked
    record completed hextract).1
  cases hrecording : record.output.coordinator.recording with
  | none =>
      unfold ReferenceCollectionSegmentExtraction.extractRound at hextract
      cases hc : ReferenceCollectionSegmentExtraction.choice record.input with
      | none => simp [hc] at hextract
      | some c => simp [hc, ReferenceCollectionSegmentExtraction.extractWith,
          hrecording] at hextract
  | some actualOutput =>
      have hstepRecord :
          (ReferenceActivePhysicalStep.step record.input).coordinator.recording =
            some actualOutput := by
        simpa only [record.output_eq] using hrecording
      cases hdispatch : (ReferenceActivePhysicalStep.prepare record.input).coordinator with
      | live registers owned base outcome =>
          cases outcome with
          | cutoffChosen dispatched hstart newLedger hinit hcand hdomain hclock hpending hnone selection =>
              have hsel : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection ≠ none := by
                rw [hdispatch]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt]
              have hbranch : ReferenceCollectionSegmentExtraction.choice record.input =
                  some ⟨registers.payload, ReferenceActivePhysicalStep.sharedLedger newLedger,
                    dispatched.startResult,
                    (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights,
                    some (ReferenceCollectionSegmentExtraction.cutoffInitializer
                      (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                      (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                      base record.input.time)⟩ := by
                simp [ReferenceCollectionSegmentExtraction.choice,
                  ReferenceCollectionSegmentExtraction.choiceOfCut,
                  ReferenceActivePhysicalStep.DispatchCut.selection,
                  ReferenceActivePhysicalStep.selectionAt, hdispatch]
              have hctx := Option.some.inj (hchoice.symm.trans hbranch)
              change CoordinatorStartRoundCutoffDispatch.Output
                (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time) base at dispatched
              change CoordinatorPhaseClock.startRound p rate.eta.val
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).time
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).priorClock
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).clockPending =
                    .ok dispatched.startResult at hstart
              change dispatched.collectionInitialization = .success (some newLedger) at hinit
              change newLedger = CoordinatorStartRoundCutoffDispatch.collectionStartLedger
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                  base record.input.time at hcand
              change CoordinatorStartRoundCutoffDispatch.initializationDomainValid
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
                  (ReferenceActivePhysicalStep.liveOwnedAt registers owned record.input.time)
                  base record.input.time at hdomain
              change CoordinatorRoundDispatch.ArmSelection registers.payload
                  dispatched.startResult record.input.time
                  (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights
                  record.input.row at selection
              have hC := ReferenceCoordinatorCollectionRecording.cutoff_recording_identification
                  registers owned base dispatched hstart newLedger hinit hcand hdomain hclock
                  hpending hnone selection hdispatch states memories hordinary hunoccupied
              obtain ⟨⟨collectionOutput, _, hstep, hgate, hraw⟩, henabled⟩ := hC
              have hsame : collectionOutput = actualOutput :=
                Option.some.inj (hstep.symm.trans hstepRecord)
              subst collectionOutput
              have hdiag : rawDiagnostic record =
                  actualOutput.gateArm.map (fun j => (j, actualOutput.rawArrival)) := by
                simp [rawDiagnostic, hrecording]
              have hfloor : actualOutput.rawArrival =
                  match actualOutput.gateArm with
                  | none => 0
                  | some j => Nat.floor ((D p : ℝ) * rate.eta.val *
                      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                        (record.input.rewards record.input.time j) /
                      CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor j) := by
                have hraw' := hraw
                rw [← hgate] at hraw'
                change actualOutput.rawArrival =
                  (match actualOutput.gateArm with
                  | none => 0
                  | some j => Nat.floor ((D p : ℝ) * rate.eta.val *
                      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                        (record.input.rewards record.input.time j) /
                      CanonicalRecordingRates.xi p rate.eta.val registers.payload.anchor j)) at hraw'
                exact hraw'
              refine ⟨actualOutput, rfl, hdiag, hinput.1, hinput.2, ?_⟩
              refine ⟨ReferenceActivePhysicalStep.collectionEnabled
                (ReferenceActivePhysicalStep.sharedLedger newLedger) record.input.time, ?_, ?_⟩
              · simp [hctx]
              · rw [hctx]
                cases hbefore : decide (record.input.time.val + 1 <
                    (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt) with
                | false =>
                    have hbefore' : ¬ record.input.time.val + 1 <
                        (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt :=
                      of_decide_eq_false hbefore
                    simp [physicalQueueRecord, hbefore']
                | true =>
                    have hbefore' : record.input.time.val + 1 <
                        (ReferenceActivePhysicalStep.sharedLedger newLedger).freezeAt :=
                      of_decide_eq_true hbefore
                    cases hgateArm : actualOutput.gateArm with
                    | none => simp [physicalQueueRecord, hdiag, hbefore', hgateArm, localArrival]
                    | some markerArm =>
                        simp [physicalQueueRecord, hdiag, hbefore', hgateArm, hfloor, localArrival]
          | _ => simp [ReferenceCollectionSegmentExtraction.choice,
              ReferenceCollectionSegmentExtraction.choiceOfCut, hdispatch] at hchoice
      | collection payload ledger clock cutoff outcome =>
          cases outcome with
          | continuing core snapshot boundary scores =>
              have hsel : (ReferenceActivePhysicalStep.prepare record.input).coordinator.selection ≠ none := by
                rw [hdispatch]
                simp [ReferenceActivePhysicalStep.DispatchCut.selection]
              have hbranch : ReferenceCollectionSegmentExtraction.choice record.input =
                  some ⟨payload, ledger, snapshot.clockStarted,
                    CoordinatorCollectionInteractive.PreObservationInputs.weights
                      (ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff)
                      snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq, none⟩ := by
                simp [ReferenceCollectionSegmentExtraction.choice,
                  ReferenceCollectionSegmentExtraction.choiceOfCut,
                  ReferenceActivePhysicalStep.DispatchCut.selection,
                  hdispatch]
              have hctx := Option.some.inj (hchoice.symm.trans hbranch)
              have hC := ReferenceCoordinatorCollectionRecording.continuing_collection_recording_identification
                  payload ledger clock cutoff core snapshot boundary scores hdispatch
                  states memories hordinary hunoccupied
              obtain ⟨⟨collectionOutput, _, hstep, hgate, hraw⟩, henabled⟩ := hC
              have hsame : collectionOutput = actualOutput :=
                Option.some.inj (hstep.symm.trans hstepRecord)
              subst collectionOutput
              have hdiag : rawDiagnostic record =
                  actualOutput.gateArm.map (fun j => (j, actualOutput.rawArrival)) := by
                simp [rawDiagnostic, hrecording]
              have hfloor : actualOutput.rawArrival =
                  match actualOutput.gateArm with
                  | none => 0
                  | some j => Nat.floor ((D p : ℝ) * rate.eta.val *
                      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                        (record.input.rewards record.input.time j) /
                      CanonicalRecordingRates.xi p rate.eta.val payload.anchor j) := by
                have hraw' := hraw
                rw [← hgate] at hraw'
                change actualOutput.rawArrival =
                  (match actualOutput.gateArm with
                  | none => 0
                  | some j => Nat.floor ((D p : ℝ) * rate.eta.val *
                      RealRewardGridCount.realRewardGridValue (D p) (D_pos p)
                        (record.input.rewards record.input.time j) /
                      CanonicalRecordingRates.xi p rate.eta.val payload.anchor j)) at hraw'
                exact hraw'
              refine ⟨actualOutput, rfl, hdiag, hinput.1, hinput.2, ?_⟩
              refine ⟨ReferenceActivePhysicalStep.collectionEnabled ledger record.input.time, ?_, ?_⟩
              · simp [hctx]
              · rw [hctx]
                cases hbefore : decide (record.input.time.val + 1 < ledger.freezeAt) with
                | false =>
                    have hbefore' : ¬ record.input.time.val + 1 < ledger.freezeAt :=
                      of_decide_eq_false hbefore
                    simp [physicalQueueRecord, hbefore']
                | true =>
                    have hbefore' : record.input.time.val + 1 < ledger.freezeAt :=
                      of_decide_eq_true hbefore
                    cases hgateArm : actualOutput.gateArm with
                    | none => simp [physicalQueueRecord, hdiag, hbefore', hgateArm, localArrival]
                    | some markerArm =>
                        simp [physicalQueueRecord, hdiag, hbefore', hgateArm, hfloor, localArrival]
          | _ => simp [ReferenceCollectionSegmentExtraction.choice,
              ReferenceCollectionSegmentExtraction.choiceOfCut, hdispatch] at hchoice
      | _ => simp [ReferenceCollectionSegmentExtraction.choice,
          ReferenceCollectionSegmentExtraction.choiceOfCut, hdispatch] at hchoice

end Bandits.Support.ReferenceCollectionRawBufferHistory

end
