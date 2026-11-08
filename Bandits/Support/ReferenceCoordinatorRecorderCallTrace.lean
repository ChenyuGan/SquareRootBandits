/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActiveHorizonMeasurability
public import Bandits.Support.ReferenceCoordinatorLiveRecording
public import Bandits.Support.ReferenceCoordinatorCollectionRecording

/-!
# Actual coordinator recorder-call and diagnostic trace

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-295,355-426`,
`sources/zip4/manuscript/04_slow_fast_learner.tex:157-174`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:16-64`,
`sources/zip4/manuscript/05_binary_transport.tex:354-396`, and
`sources/zip4/manuscript/08_main_theorem.tex:29-42`.

The trace augments the existing actual record code with the coordinator's
selected local call view, its schedule and service bits, and its retained
recorder result. It leaves follower-side arrivals and physical queues
unresolved. The original code remains the first projection of every run
observation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalHorizon
open Bandits.Support.ReferenceActiveHorizonMeasurability
open Bandits.Support.ReferenceLiveDispatchOutputMeasurability
open Bandits.Support.ReferenceCollectionServiceTailMeasurability
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation

namespace Bandits.Support.ReferenceCoordinatorRecorderCallTrace

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput

variable {p : Parameters} {rate : RateInput p}

local instance cutoffOptionMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

local instance propDecidable (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

/-- The lossless selected coordinator choice retained by the actual record. -/
def selection (code : RoundRecordCode (p := p) (rate := rate)) :
    Option (ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :=
  code.2.2.1.1

/-- The complete retained coordinator tail, including its original failure,
recorder, and UP diagnostic fields. -/
def tail (code : RoundRecordCode (p := p) (rate := rate)) :
    ReferenceCollectionServiceTailMeasurability.CollectionTailCode p rate :=
  code.2.2.1.2.2.2.2

/-- The actual recorder result stored by the coordinator tail. Absence remains
`none`; it is never replaced by a synthetic zero output. -/
def recording (code : RoundRecordCode (p := p) (rate := rate)) :
    Option (CoordinatorRecordingOperation.Output p) :=
  (tail code).2.2.2.1

/-- The literal local live-assignment interval test on the retained payload
and cutoff. -/
def live (code : RoundRecordCode (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) : Bool :=
  decide (selected.1.payload.sigma.val + 1 ≤ code.1 + 1 ∧
    code.1 + 1 < CoordinatorLocalArmChoice.cutoffRound selected.1.cutoff)

/-- The literal local freeze test on the retained assignment start and
original started clock. -/
def enabled (code : RoundRecordCode (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) : Bool :=
  decide (¬ (0 < selected.1.payload.sigma.val + 1 ∧
    code.1 + 1 ≥ selected.2.1.clock.g))

/-- One actual coordinator selection cell. No selection means there was no
recorder call, while a selected call with a failed recorder retains `none`. -/
def cell (code : RoundRecordCode (p := p) (rate := rate)) :=
  (selection code).map fun selected =>
    (selected, live code selected, enabled code selected, recording code)

/-- The coordinator's arm-indexed raw diagnostic; gate failure is represented
by no output, while a successful gated zero remains distinguishable. -/
def coordinatorRaw (code : RoundRecordCode (p := p) (rate := rate))
    (arm : Fin p.K) : Option ℕ :=
  (recording code).map fun output =>
    if output.gateArm = some arm then output.rawArrival else 0

/-- Build the exact recorder input represented by a retained selection and
the original record root. The observation remains grid-typed. -/
def inputFromSelection
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :
    CoordinatorRecordingOperation.Input p :=
  CoordinatorRecorderComplementBridge.recorderInput {
    currentWeights := selected.1.complementWeights
    time := record.input.time
    gridBoundary := selected.2.1.clock.g
    row := record.input.rows record.input.selected
    ownArm := selected.2.2
    observation := roundRecordCodeFeedback (roundRecordCode record)
      (ActiveRoundActions.coordinator p.two_le_m)
    mode := if live (roundRecordCode record) selected then
      .live (decide (selected.2.1.pending = ∅)) else .collection }

/-- Reconstruct the canonical optional recorder input, without executing the
recorder operation or any physical transition. -/
def inputFromCode
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (CoordinatorRecordingOperation.Input p) :=
  (selection (roundRecordCode record)).map (inputFromSelection record)

/-- Project the actual dependent preparation and exhaust its computed phase
constructor. Only the five real chosen constructors invoke a recorder; every
other constructor has no post-choice call. -/
def actualBranchInput
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    Option (CoordinatorRecordingOperation.Input p) := by
  let prepared := record.output.preparation
  match prepared.coordinator with
  | .first (.chosen installed _) =>
      exact some (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.liveRecordingInput prepared installed.registers
          installed.startRoundResult))
  | .live registers _ _ (.continuingChosen dispatched _ _ _) =>
      exact some (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.liveRecordingInput prepared
          (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time)
          dispatched.startResult))
  | .live registers _ _ (.cutoffChosen dispatched _ ledger _ _ _ _ _ _ _) =>
      exact some (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared registers.payload
          dispatched.startResult
          (ReferenceActivePhysicalStep.liveRegistersAt registers record.input.time).complementWeights))
  | .collection payload ledger clock cutoff (.continuing _ snapshot _ _) =>
      let source := ReferenceActivePhysicalStep.collectionInput record.input payload ledger clock cutoff
      exact some (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.collectionRecordingInput prepared payload
          snapshot.clockStarted
          (CoordinatorCollectionInteractive.PreObservationInputs.weights source
            snapshot.inputsValid.ledger_valid snapshot.inputsValid.assignment_eq)))
  | .collection _ _ _ _ (.laterChosen _ _ started _ _ _ _ _ _ installed _) =>
      exact some (CoordinatorRecorderComplementBridge.recorderInput
        (ReferenceActivePhysicalStep.liveRecordingInput prepared installed.registers started))
  | _ => exact none

/-- The input decoder applied to an actual record is exactly the canonical
selection map of the actual dependent dispatcher, retaining every encoded
view field. -/
theorem inputFromCode_actualSelection
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    inputFromCode record = (record.output.preparation.coordinator.selection.map
      (fun selected => inputFromSelection record
        (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected))) := by
  let prepared := record.output.preparation
  have hprep : prepared = ReferenceActivePhysicalStep.prepare record.input := by
    dsimp [prepared]
    simpa [ReferenceActivePhysicalStep.step] using
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
        output.preparation) record.output_eq
  have hselection : selection (roundRecordCode record) =
      prepared.coordinator.selection.map
        ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
    calc
      selection (roundRecordCode record) =
          (ReferenceActivePhysicalStep.dispatch record.input).selection.map
            ReferenceLiveDispatchOutputMeasurability.encodeSelection :=
        (roundRecordCode_front record).1
      _ = prepared.coordinator.selection.map
            ReferenceLiveDispatchOutputMeasurability.encodeSelection := by
        rw [hprep]
        rfl
  simp only [prepared, inputFromCode, hselection, Option.map_map,
    Function.comp_def]

/-- A selected actual dispatcher branch decodes to the exact literal input
built from its retained selected choice. No success fact about the recorder or
any later successor is needed for this input identity. -/
theorem inputFromCode_of_selected
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (selected : ReferenceActivePhysicalStep.Selection record.input)
    (hselected : (ReferenceActivePhysicalStep.dispatch record.input).selection =
      some selected) :
    inputFromCode record = some (inputFromSelection record
      (ReferenceLiveDispatchOutputMeasurability.encodeSelection selected)) := by
  have hprep : record.output.preparation =
      ReferenceActivePhysicalStep.prepare record.input := by
    simpa [ReferenceActivePhysicalStep.step] using
      congrArg (fun output : ReferenceActivePhysicalStep.RoundOutput record.input =>
        output.preparation) record.output_eq
  rw [inputFromCode_actualSelection, hprep]
  simp [ReferenceActivePhysicalStep.prepare, hselected]

/-- The canonical enable bit is the actual retained-start comparison: the
source assignment start is positive for every retained payload. -/
theorem enabled_eq_time_before_startGrid
    (code : RoundRecordCode (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate) :
    enabled code selected = decide (code.1 + 1 < selected.2.1.clock.g) := by
  unfold enabled
  apply Bool.decide_congr
  omega

/-- When the retained record coordinate is the original typed round time,
the literal code bit is exactly the source local live test. -/
theorem live_eq_assignmentIsLive
    (code : RoundRecordCode (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (time : Fin p.T) (hcode : code.1 = time.val) :
    live code selected = decide
      (CoordinatorLocalArmChoice.assignmentIsLive selected.1.payload
        selected.1.cutoff time) := by
  simp [live, CoordinatorLocalArmChoice.assignmentIsLive,
    CoordinatorLocalArmChoice.assignmentStart, CoordinatorLocalArmChoice.sourceRound,
    hcode]

/-- The stored coordinator observation is exactly the diagnostic decoded from
the original whole-step code. -/
theorem recording_eq_actualDiagnostics
    (record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)) :
    recording (roundRecordCode record) = record.coordinatorDiagnostics.recording := by
  have h := (roundRecordCode_reconstructs record).2.1
  change (ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation
    (roundRecordCode record).2.2.1.2.2.2.2).recording = _
  have hrecording := congrArg ReferenceActivePhysicalStep.CoordinatorObservation.recording h
  simpa [ReferenceCollectionServiceTailMeasurability.decodeCollectionObservation] using hrecording

/-- On an actual live owned coordinate, the retained raw diagnostic is the
same gate-indexed amount consumed by the live service pass. -/
theorem coordinatorRaw_eq_complementArrival
    (code : RoundRecordCode (p := p) (rate := rate))
    (selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate)
    (j : CanonicalFastSampling.FastArm selected.1.payload.slowSet) :
    coordinatorRaw code j.1 = (recording code).map
      (fun output => CoordinatorLiveServiceFinish.complementArrival
        selected.1.payload output j) := by
  cases hrecord : recording code with
  | none => simp [coordinatorRaw, hrecord]
  | some output =>
      simp [coordinatorRaw, CoordinatorLiveServiceFinish.complementArrival, hrecord]

/-- The same retained output gives the collection ledger's literal local
arrival. A missing gate remains zero at that downstream queue coordinate. -/
theorem coordinatorRaw_eq_collectionLocalArrival
    (code : RoundRecordCode (p := p) (rate := rate)) (arm : Fin p.K) :
    coordinatorRaw code arm = (recording code).map
      (fun output => CoordinatorCollectionLedger.localArrival
        (CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder output) arm) := by
  cases hrecord : recording code with
  | none => simp [coordinatorRaw, hrecord]
  | some output =>
      cases hgate : output.gateArm <;>
        simp [coordinatorRaw, CoordinatorCollectionLedger.localArrival,
          CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder, hrecord, hgate]

private theorem measurable_selection : Measurable (selection (p := p) (rate := rate)) :=
  measurable_fst.comp (measurable_fst.comp
    (measurable_snd.comp (measurable_snd.comp measurable_id)))

private theorem measurable_selectionSigma :
    Measurable (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      selected.1.payload.sigma.val) := by
  have hview : Measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)) := comap_measurable _
  have hpayload : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        selected.1.payload) :=
    measurable_fst.comp (hview.comp measurable_fst)
  have hpayloadObservation : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        LaterAssignmentStartMeasurability.payloadObservation selected.1.payload) :=
    (comap_measurable _).comp hpayload
  have hsigma : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        (LaterAssignmentStartMeasurability.payloadObservation selected.1.payload).2.1) :=
    measurable_fst.comp (measurable_snd.comp hpayloadObservation)
  exact (measurable_of_countable (fun t : Fin p.T => t.val)).comp hsigma

private theorem measurable_selectionCutoff :
    Measurable (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      CoordinatorLocalArmChoice.cutoffRound selected.1.cutoff) := by
  have hview : Measurable
      (ReferenceDownReceptionMeasurability.choiceTimeViewObservation
        (p := p) (rate := rate)) := comap_measurable _
  have hcutoff : Measurable
      (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
        (ReferenceDownReceptionMeasurability.choiceTimeViewObservation selected.1).2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (hview.comp measurable_fst)))
  exact (measurable_of_countable (CoordinatorLocalArmChoice.cutoffRound (p := p))).comp
    hcutoff

private theorem measurable_selectionGridBoundary :
    Measurable (fun selected : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate =>
      selected.2.1.clock.g) :=
  (measurable_of_countable (fun started : CoordinatorPhaseClock.StartRoundResult p =>
    started.clock.g)).comp (measurable_fst.comp (measurable_snd.comp measurable_id))

private theorem measurable_liveCellBit : Measurable
    (fun pair : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        RoundRecordCode (p := p) (rate := rate) => live pair.2 pair.1) := by
  have hargs : Measurable (fun pair :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        RoundRecordCode (p := p) (rate := rate) =>
      (pair.1.1.payload.sigma.val,
        (pair.2.1, CoordinatorLocalArmChoice.cutoffRound pair.1.1.cutoff))) := by
    exact ((measurable_selectionSigma (p := p) (rate := rate)).comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_selectionCutoff (p := p) (rate := rate)).comp measurable_fst))
  have hdecision : Measurable (fun values : ℕ × (ℕ × ℕ) =>
      decide (values.1 + 1 ≤ values.2.1 + 1 ∧ values.2.1 + 1 < values.2.2)) :=
    measurable_of_countable _
  exact hdecision.comp hargs

private theorem measurable_enabledCellBit : Measurable
    (fun pair : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        RoundRecordCode (p := p) (rate := rate) => enabled pair.2 pair.1) := by
  have hargs : Measurable (fun pair :
      ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        RoundRecordCode (p := p) (rate := rate) =>
      (pair.1.1.payload.sigma.val,
        (pair.2.1, pair.1.2.1.clock.g))) := by
    exact ((measurable_selectionSigma (p := p) (rate := rate)).comp measurable_fst).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_selectionGridBoundary (p := p) (rate := rate)).comp measurable_fst))
  have hdecision : Measurable (fun values : ℕ × (ℕ × ℕ) =>
      decide (¬ (0 < values.1 + 1 ∧ values.2.1 + 1 ≥ values.2.2))) :=
    measurable_of_countable _
  exact hdecision.comp hargs

theorem measurable_cell : Measurable (cell (p := p) (rate := rate)) := by
  have htail : Measurable (tail (p := p) (rate := rate)) := by
    exact measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
        (measurable_snd.comp (measurable_snd.comp measurable_id))))))
  have hrecordingCode : Measurable (recording (p := p) (rate := rate)) := by
    exact measurable_fst.comp (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp htail)))
  have hrecording : Measurable
      (fun pair : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        RoundRecordCode (p := p) (rate := rate) => recording pair.2) := by
    exact hrecordingCode.comp measurable_snd
  have hentry : Measurable
      (fun pair : ReferenceLiveDispatchOutputMeasurability.SelectionData p rate ×
        RoundRecordCode (p := p) (rate := rate) =>
          (pair.1, live pair.2 pair.1, enabled pair.2 pair.1, recording pair.2)) := by
    exact measurable_fst.prodMk
      ((measurable_liveCellBit (p := p) (rate := rate)).prodMk
        ((measurable_enabledCellBit (p := p) (rate := rate)).prodMk hrecording))
  exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
    (fun pair => (pair.1, live pair.2 pair.1, enabled pair.2 pair.1, recording pair.2))
    hentry (selection (p := p) (rate := rate))
    (measurable_selection (p := p) (rate := rate))

/-- The trace for a fixed, actual active horizon. The first component is the
unchanged horizon observation; the second maps every actual record in order. -/
def runRecorderTrace (start count : ℕ) (hspan : start + count ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :=
  let observed := runObservation start count hspan input
  (observed, observed.2.map cell)

/-- The same actual trace over H's varying-calendar input subtype. -/
def calendarRunRecorderTrace
    (input : CalendarRunInput (p := p) (rate := rate)) :=
  let observed := calendarRunObservation input
  (observed, observed.2.map cell)

/-- The varying-calendar lift keeps the same actual chronological round list
as H's fixed-calendar observation on the corresponding original run input. -/
theorem calendarRunRecorderTrace_actualRecords
    (input : CalendarRunInput (p := p) (rate := rate)) :
    (calendarRunRecorderTrace input).2 =
      (runOfInput input.val.1 input.val.2.1 input.property.1
        ⟨input.val.2.2, input.property.2⟩).records.map
          (fun record => cell (roundRecordCode record)) := by
  simp [calendarRunRecorderTrace, calendarRunObservation_eq_actual,
    runObservation]

/-- The trace preserves the complete original horizon code verbatim. -/
theorem runRecorderTrace_originalCode (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :
    (runRecorderTrace start count hspan input).1 = runObservation start count hspan input := rfl

/-- Every actual round record contributes exactly one call cell in its
original chronological position. -/
theorem runRecorderTrace_actualRecords (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :
    (runRecorderTrace start count hspan input).2 =
      (runOfInput start count hspan input).records.map
        (fun record => cell (roundRecordCode record)) := by
  simp [runRecorderTrace, runObservation]

/-- The mapped call trace retains exactly one cell for every physical round.
Its successful/failed selection status never filters the actual calendar. -/
theorem runRecorderTrace_recordCount (start count : ℕ)
    (hspan : start + count ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :
    (runRecorderTrace start count hspan input).2.length = count := by
  simp only [runRecorderTrace, List.length_map]
  exact runObservation_recordCount start count hspan input

/-- A zero-count trace preserves the same initial/final horizon code and has
an empty record list, including the terminal start coordinate `start = T`. -/
theorem runRecorderTrace_zero (start : ℕ) (hspan : start + 0 ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :
    runRecorderTrace start 0 hspan input =
      ((ReferenceActivePhysicalStepMeasurability.encodeState input.val.1,
          ([] : List (RoundRecordCode (p := p) (rate := rate)))), []) := by
  simp [runRecorderTrace, runObservation, runOfInput,
    ReferenceActivePhysicalHorizon.run_zero_final,
    ReferenceActivePhysicalHorizon.run_zero_records]

/-- The successor trace appends the exact actual step record once, after the
previous chronological records, even when that step's output records a
failure. -/
theorem runRecorderTrace_successor (start count : ℕ)
    (hspan : start + (count + 1) ≤ p.T)
    (input : ActiveRunInput (p := p) (rate := rate) start) :
    (runRecorderTrace start (count + 1) hspan input).2 =
      (runRecorderTrace start count (by omega) input).2 ++
        [cell (roundRecordCode ⟨
          ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
            input.val.2.2.1 input.val.2.2.2 start input.property
            (runOfInput start count (by omega) input)
            ⟨start + count, by omega, by omega⟩,
          ReferenceActivePhysicalStep.step
            (ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
              input.val.2.2.1 input.val.2.2.2 start input.property
              (runOfInput start count (by omega) input)
              ⟨start + count, by omega, by omega⟩), rfl⟩)] := by
  have hrecords := ReferenceActivePhysicalHorizon.foldRound_equations
    input.val.1 input.val.2.1 input.val.2.2.1 input.val.2.2.2 start input.property
    (runOfInput start count (by omega) input) ⟨start + count, by omega, by omega⟩
  have hrunEq : runOfInput start (count + 1) hspan input =
      ReferenceActivePhysicalHorizon.foldRound input.val.1 input.val.2.1
        input.val.2.2.1 input.val.2.2.2 start input.property
        (runOfInput start count (by omega) input) ⟨start + count, by omega, by omega⟩ :=
    ReferenceActivePhysicalHorizon.run_successor_step input.val.1 input.val.2.1
      input.val.2.2.1 input.val.2.2.2 start count hspan input.property
  have hrecordsEq : (runOfInput start (count + 1) hspan input).records =
      (runOfInput start count (by omega) input).records ++
        [⟨ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
            input.val.2.2.1 input.val.2.2.2 start input.property
            (runOfInput start count (by omega) input)
            ⟨start + count, by omega, by omega⟩,
          ReferenceActivePhysicalStep.step
            (ReferenceActivePhysicalHorizon.roundInputAt input.val.1 input.val.2.1
              input.val.2.2.1 input.val.2.2.2 start input.property
              (runOfInput start count (by omega) input)
              ⟨start + count, by omega, by omega⟩), rfl⟩] := by
    rw [hrunEq]
    exact hrecords.2
  simp only [runRecorderTrace, runObservation, List.map_map, Function.comp_def]
  rw [hrecordsEq]
  simp

/-- The original actual code and the mapped call cells are jointly Borel on
the original full-row, selected-index, and reward-table input. -/
theorem measurable_runRecorderTrace (start count : ℕ) (hspan : start + count ≤ p.T) :
    Measurable (runRecorderTrace (p := p) (rate := rate) start count hspan) := by
  have hcode := measurable_runObservation (p := p) (rate := rate) start count hspan
  have hrecords := measurable_snd.comp hcode
  have hcells := measurable_list_map
    (records := fun input : ActiveRunInput (p := p) (rate := rate) start =>
      (runObservation start count hspan input).2)
    hrecords (cell (p := p) (rate := rate)) measurable_cell
  exact hcode.prodMk hcells

/-- The actual varying-calendar trace is Borel by the existing countable
calendar gluing and the same literal measurable cell map. -/
theorem measurable_calendarRunRecorderTrace :
    Measurable (calendarRunRecorderTrace (p := p) (rate := rate)) := by
  have hcode := measurable_calendarRunObservation (p := p) (rate := rate)
  have hrecords := measurable_snd.comp hcode
  have hcells := measurable_list_map
    (records := fun input : CalendarRunInput (p := p) (rate := rate) =>
      (calendarRunObservation input).2)
    hrecords (cell (p := p) (rate := rate)) measurable_cell
  exact hcode.prodMk hcells

end Bandits.Support.ReferenceCoordinatorRecorderCallTrace

end
