/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorCollectionUpRoundStep

/-!
# Interactive coordinator collection round

This module splits the accepted one-round coordinator collection operation at
the point before its own rounded feedback is read. Preparation uses the
existing phase clock and actual coordinator arm choice. Observation continues
the same operation through the existing recorder, collection ledger, row-based
UP receiver, and both finish operations.

Sources: `sources/zip4/manuscript/06_interruptions.tex:37-70,235-297`,
`sources/zip4/manuscript/05_binary_transport.tex:352-429`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The projection is only a view of the accepted operation's fields. It adds no
protocol state, feedback law, sender-authenticity claim, global-run claim, or
measurability result.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorCollectionInteractive

open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingOperation
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorUpMeasurability
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.ActiveRoundActions
open Bandits.Support.ReferencePrelaunchFollower
open Bandits.Support.PublicDiscreteDraws

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The exact incoming accepted fields other than the coordinator's own
rounded observation. The continuous row, clock, ledger, payload, base scores,
decoder bank, and indices remain the original carried values. -/
structure PreObservationInputs (p : Parameters) where
  etaReal : ℝ
  etaPositive : 0 < etaReal
  n : ℕ
  n_cast_identity : (n : ℝ) = etaReal * (ConstructorDimensions.D p : ℝ)
  payload : AssignmentStartPayload.Input p (⟨etaReal, etaPositive⟩ : LearningRate)
  baseScores : Fin (p.m - 1) → ℕ
  ledger : CoordinatorCollectionLedger.Ledger p etaReal etaPositive
    (payloadSourceCap payload) n n_cast_identity
  clock : CoordinatorPhaseClock.ClockRegisters p
  upDecoderBank : CoordinatorUpReception.UpDecoderBank p
  cutoffIndex : Fin p.T
  time : Fin p.T
  row : CompletePublicTable.CompleteRow p

namespace PreObservationInputs

variable (x : PreObservationInputs p)

/-- The arm-indexed complement weights from the exact accepted carried state. -/
def weights (hvalid : CoordinatorCollectionLedger.validLedger x.ledger)
    (hassignment : ∀ i : Fin (p.m - 1),
      x.ledger.assignment.arm i = x.payload.assignment.assigned i) :=
  CoordinatorCollectionUpRoundStep.complementWeights x.ledger x.payload
    hvalid hassignment

end PreObservationInputs

/-- Attach only the newly observed finite rounded feedback to the accepted
input. -/
def attachOwnObservation (x : PreObservationInputs p)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    CoordinatorCollectionUpRoundStep.Inputs p :=
  { etaReal := x.etaReal
    etaPositive := x.etaPositive
    n := x.n
    n_cast_identity := x.n_cast_identity
    payload := x.payload
    baseScores := x.baseScores
    ledger := x.ledger
    clock := x.clock
    upDecoderBank := x.upDecoderBank
    cutoffIndex := x.cutoffIndex
    time := x.time
    row := x.row
    ownObservation := ownObservation }

@[simp] theorem attachOwnObservation_cutoffIndex (x : PreObservationInputs p)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    (attachOwnObservation x ownObservation).cutoffIndex = x.cutoffIndex := rfl

/-- Forgetting feedback from an accepted input retains every other field. -/
def projectPreObservation (x : CoordinatorCollectionUpRoundStep.Inputs p) :
    PreObservationInputs p :=
  { etaReal := x.etaReal
    etaPositive := x.etaPositive
    n := x.n
    n_cast_identity := x.n_cast_identity
    payload := x.payload
    baseScores := x.baseScores
    ledger := x.ledger
    clock := x.clock
    upDecoderBank := x.upDecoderBank
    cutoffIndex := x.cutoffIndex
    time := x.time
    row := x.row }

@[simp] theorem attach_projectPreObservation
    (x : CoordinatorCollectionUpRoundStep.Inputs p) :
    attachOwnObservation (projectPreObservation x) x.ownObservation = x := by
  cases x
  simp [attachOwnObservation, projectPreObservation]

@[simp] theorem project_attachOwnObservation (x : PreObservationInputs p)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    projectPreObservation (attachOwnObservation x ownObservation) = x := by
  cases x
  simp [attachOwnObservation, projectPreObservation]

/-- The observation-free domain consists of the original `InputsValid`
operation-domain and state-matching fields. None of its fields mentions a
current observation or a claimed successful operation. -/
structure PreInputsValid {p : Parameters} (x : PreObservationInputs p) where
  ledger_valid : CoordinatorCollectionLedger.validLedger x.ledger
  ledger_ready : x.ledger.phase = CoordinatorCollectionLedger.Phase.ready
  pending_nonempty : x.ledger.pending.Nonempty
  assignment_eq : ∀ i : Fin (p.m - 1),
    x.ledger.assignment.arm i = x.payload.assignment.assigned i
  base_score_eq : x.ledger.baseScore = x.baseScores
  clock_parameter_valid :
    CoordinatorPhaseClock.proposalParameterValid p x.etaReal
  clock_registers_valid :
    CoordinatorPhaseClock.clockRegistersValid p x.etaReal x.clock
  clock_start_time_valid :
    CoordinatorPhaseClock.startRoundTimeValid p x.time x.clock
  clock_sigma_eq : x.clock.sigma = some x.payload.sigma
  clock_cutoff_eq : x.clock.u = some x.cutoffIndex
  ledger_sigma_eq : x.ledger.sigma =
    CoordinatorRecorderComplementBridge.sourceStart x.payload
  ledger_cutoff_eq : x.ledger.cutoff =
    CoordinatorCollectionUpRoundStep.sourceCutoff x.cutoffIndex
  ledger_freeze_eq : x.ledger.freezeAt = x.clock.g
  ledger_cursor_eq : x.ledger.cursor =
    CoordinatorCollectionUpRoundStep.sourceRound x.time
  decoder_bank_valid :
    CoordinatorUpReception.decoderBankCheck p x.upDecoderBank = true
  choice_valid : CoordinatorLocalArmChoice.ChoiceInputsValid x.payload
    (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
    x.time (PreObservationInputs.weights x ledger_valid assignment_eq)

namespace PreInputsValid

variable {x : PreObservationInputs p}

/-- Restore the accepted input-domain structure after attaching any finite
observation. -/
theorem toInputsValid (h : PreInputsValid x)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    CoordinatorCollectionUpRoundStep.InputsValid
      (attachOwnObservation x ownObservation) :=
  { ledger_valid := h.ledger_valid
    ledger_ready := h.ledger_ready
    pending_nonempty := h.pending_nonempty
    assignment_eq := h.assignment_eq
    base_score_eq := h.base_score_eq
    clock_parameter_valid := h.clock_parameter_valid
    clock_registers_valid := h.clock_registers_valid
    clock_start_time_valid := h.clock_start_time_valid
    clock_sigma_eq := h.clock_sigma_eq
    clock_cutoff_eq := h.clock_cutoff_eq
    ledger_sigma_eq := h.ledger_sigma_eq
    ledger_cutoff_eq := h.ledger_cutoff_eq
    ledger_freeze_eq := h.ledger_freeze_eq
    ledger_cursor_eq := h.ledger_cursor_eq
    decoder_bank_valid := h.decoder_bank_valid
    choice_valid := h.choice_valid }

/-- Recover the observation-free checks from the original accepted domain. -/
theorem ofInputsValid {x : PreObservationInputs p}
    {ownObservation : Fin (ConstructorDimensions.D p + 1)}
    (h : CoordinatorCollectionUpRoundStep.InputsValid
      (attachOwnObservation x ownObservation)) : PreInputsValid x :=
  { ledger_valid := h.ledger_valid
    ledger_ready := h.ledger_ready
    pending_nonempty := h.pending_nonempty
    assignment_eq := h.assignment_eq
    base_score_eq := h.base_score_eq
    clock_parameter_valid := h.clock_parameter_valid
    clock_registers_valid := h.clock_registers_valid
    clock_start_time_valid := h.clock_start_time_valid
    clock_sigma_eq := h.clock_sigma_eq
    clock_cutoff_eq := h.clock_cutoff_eq
    ledger_sigma_eq := h.ledger_sigma_eq
    ledger_cutoff_eq := h.ledger_cutoff_eq
    ledger_freeze_eq := h.ledger_freeze_eq
    ledger_cursor_eq := h.ledger_cursor_eq
    decoder_bank_valid := h.decoder_bank_valid
    choice_valid := h.choice_valid }

end PreInputsValid

/-- The original and observation-free domains agree for every actual rounded
observation. -/
theorem preInputsValid_iff_attachedInputsValid
    (x : PreObservationInputs p)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    PreInputsValid x ↔
      CoordinatorCollectionUpRoundStep.InputsValid
        (attachOwnObservation x ownObservation) :=
  ⟨fun h => h.toInputsValid ownObservation,
    fun h => PreInputsValid.ofInputsValid h⟩

/-- The exact pre-choice result retained by preparation. Its clock and arm
are certified by the same accepted operations used by `run`. -/
structure PreparedSnapshot {p : Parameters} (x : PreObservationInputs p) where
  inputsValid : PreInputsValid x
  clockStarted : CoordinatorPhaseClock.StartRoundResult p
  clockStarted_eq : CoordinatorPhaseClock.startRound p x.etaReal x.time
    x.clock x.ledger.pending = .ok clockStarted
  clockStarted_frame : clockStarted.clock = x.clock ∧
    clockStarted.pending = x.ledger.pending ∧
    clockStarted.ledgerCommand = none ∧ clockStarted.assignmentStart = none
  arm : Fin p.K
  armChoice_eq : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
    clockStarted.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
    x.time (PreObservationInputs.weights x inputsValid.ledger_valid inputsValid.assignment_eq)
    x.row = some arm

/-- Preparation has only the accepted clock, branch, and arm-choice failure
sites. -/
inductive PrepareResult {p : Parameters} (x : PreObservationInputs p) where
  | failed (reason : CoordinatorCollectionUpRoundStep.Failure)
  | prepared (snapshot : PreparedSnapshot x)

/-- Run the exact existing phase-clock `startRound`, its no-command branch
check, and the exact existing coordinator arm choice. No observation value is
available to this operation. -/
def prepare {p : Parameters} (x : PreObservationInputs p)
    (h : PreInputsValid x) : PrepareResult x := by
  classical
  match hclockStart : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending with
  | .error reason => exact .failed (.clockStart reason)
  | .ok clockStarted =>
    if hbranch : clockStarted.clock = x.clock ∧
        clockStarted.pending = x.ledger.pending ∧
        clockStarted.ledgerCommand = none ∧ clockStarted.assignmentStart = none then
      let weights := PreObservationInputs.weights x h.ledger_valid h.assignment_eq
      match hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
          clockStarted.pending
          (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
          x.time weights x.row with
      | none => exact .failed .armChoiceDomain
      | some arm =>
        exact .prepared {
          inputsValid := h
          clockStarted := clockStarted
          clockStarted_eq := hclockStart
          clockStarted_frame := hbranch
          arm := arm
          armChoice_eq := hchoice }
    else
      exact .failed .wrongClockBranch

namespace PreparedSnapshot

variable {p : Parameters} {x : PreObservationInputs p}
  (s : PreparedSnapshot x)

/-- The retained start proof is also the exact accepted start proof after
attaching any observation. -/
theorem clockStarted_eq_attached
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    CoordinatorPhaseClock.startRound p
      (attachOwnObservation x ownObservation).etaReal
      (attachOwnObservation x ownObservation).time
      (attachOwnObservation x ownObservation).clock
      (attachOwnObservation x ownObservation).ledger.pending = .ok s.clockStarted := by
  simpa [attachOwnObservation] using s.clockStarted_eq

/-- The no-command start branch is the same after attaching feedback. -/
theorem clockStarted_frame_attached
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    s.clockStarted.clock = (attachOwnObservation x ownObservation).clock ∧
      s.clockStarted.pending =
        (attachOwnObservation x ownObservation).ledger.pending ∧
      s.clockStarted.ledgerCommand = none ∧
      s.clockStarted.assignmentStart = none := by
  simpa [attachOwnObservation] using s.clockStarted_frame

/-- The retained arm remains exactly the accepted choice after attaching any
own observation. -/
theorem armChoice_eq_attached
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    CoordinatorLocalArmChoice.coordinatorArmChoice
      (attachOwnObservation x ownObservation).payload s.clockStarted.pending
      (some (CoordinatorCollectionUpRoundStep.localCutoff
        (attachOwnObservation x ownObservation).cutoffIndex))
      (attachOwnObservation x ownObservation).time
      (CoordinatorCollectionUpRoundStep.Inputs.weights
        (x := attachOwnObservation x ownObservation)
        (s.inputsValid.toInputsValid ownObservation).ledger_valid
        (s.inputsValid.toInputsValid ownObservation).assignment_eq)
      (attachOwnObservation x ownObservation).row = some s.arm := by
  simpa [attachOwnObservation, PreInputsValid.toInputsValid,
    PreObservationInputs.weights,
    CoordinatorCollectionUpRoundStep.Inputs.weights] using s.armChoice_eq

end PreparedSnapshot

/-- Continue from the same prepared clock and arm using only the newly
supplied own observation. Recorder, ledger, row-selected receiver, and finish
calls follow the accepted run order. -/
def observe {p : Parameters} {x : PreObservationInputs p}
    (prepared : PreparedSnapshot x)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    CoordinatorCollectionUpRoundStep.Result
      (attachOwnObservation x ownObservation) := by
  classical
  let input := attachOwnObservation x ownObservation
  let inputValid := prepared.inputsValid.toInputsValid ownObservation
  let arm := prepared.arm
  let clockStarted := prepared.clockStarted
  match hrecorder : CoordinatorRecorderComplementBridge.run
      (CoordinatorCollectionUpRoundStep.InputsValid.recorderInput
        (x := input) inputValid arm) with
  | none => exact .failed .recorderDomain
  | some recorder =>
    let enabled := CoordinatorCollectionUpRoundStep.InputsValid.sourceLearningEnabled input
    let raw := CoordinatorCollectionUpRoundStep.InputsValid.rawInputOfRecorder recorder
    match hstart : CoordinatorCollectionLedger.startRound input.ledger
        (CoordinatorCollectionUpRoundStep.sourceRound input.time) enabled raw with
    | .invalid => exact .failed .ledgerStartDomain
    | .rejected _ => exact .failed .ledgerStartDomain
    | .success ledgerStarted =>
      let receptionInput := CoordinatorUpMeasurability.receptionInputAtRow input.row
        (CoordinatorCollectionUpRoundStep.InputsValid.upInputs
          (x := input) ledgerStarted) input.time
      match hreception : CoordinatorUpMeasurability.receiveUpAtRow input.row
          (CoordinatorCollectionUpRoundStep.InputsValid.upInputs
            (x := input) ledgerStarted) input.time with
      | .invalid => exact .failed .upReceptionDomain
      | .success (ledgerDecoded, bankAfter) =>
        match hfinish : CoordinatorCollectionLedger.finishRound ledgerDecoded with
        | .invalid => exact .failed .ledgerFinishDomain
        | .rejected _ => exact .failed .ledgerFinishDomain
        | .success ledgerFinished =>
          match hclockFinish : CoordinatorPhaseClock.finishRound p input.etaReal
              input.time clockStarted.clock ledgerFinished.pending input.row with
          | .error reason => exact .failed (.clockFinish reason)
          | .ok clockFinished =>
            exact .completed {
              inputsValid := inputValid
              clockStarted := clockStarted
              clockStarted_eq := by
                simpa [input, attachOwnObservation] using
                  prepared.clockStarted_eq_attached ownObservation
              clockStarted_frame := by
                simpa [input, attachOwnObservation] using
                  prepared.clockStarted_frame_attached ownObservation
              arm := arm
              armChoice_eq := by
                simpa [input, attachOwnObservation] using
                  prepared.armChoice_eq_attached ownObservation
              recorder := recorder
              recorder_eq := hrecorder
              enabled := enabled
              enabled_eq := rfl
              rawInput := raw
              rawInput_eq := rfl
              ledgerStarted := ledgerStarted
              ledgerStart_eq := hstart
              receptionInput := receptionInput
              receptionInput_eq := rfl
              reception := .success (ledgerDecoded, bankAfter)
              reception_eq := hreception
              ledgerDecoded := ledgerDecoded
              reception_outcome := .inl rfl
              reception_not_invalid := by simp
              decoderBankAfter := bankAfter
              ledgerFinished := ledgerFinished
              ledgerFinish_eq := hfinish
              clockFinished := clockFinished
              clockFinish_eq := hclockFinish }
      | .rejected (ledgerDecoded, bankAfter) =>
        match hfinish : CoordinatorCollectionLedger.finishRound ledgerDecoded with
        | .invalid => exact .failed .ledgerFinishDomain
        | .rejected _ => exact .failed .ledgerFinishDomain
        | .success ledgerFinished =>
          match hclockFinish : CoordinatorPhaseClock.finishRound p input.etaReal
              input.time clockStarted.clock ledgerFinished.pending input.row with
          | .error reason => exact .failed (.clockFinish reason)
          | .ok clockFinished =>
            exact .completed {
              inputsValid := inputValid
              clockStarted := clockStarted
              clockStarted_eq := by
                simpa [input, attachOwnObservation] using
                  prepared.clockStarted_eq_attached ownObservation
              clockStarted_frame := by
                simpa [input, attachOwnObservation] using
                  prepared.clockStarted_frame_attached ownObservation
              arm := arm
              armChoice_eq := by
                simpa [input, attachOwnObservation] using
                  prepared.armChoice_eq_attached ownObservation
              recorder := recorder
              recorder_eq := hrecorder
              enabled := enabled
              enabled_eq := rfl
              rawInput := raw
              rawInput_eq := rfl
              ledgerStarted := ledgerStarted
              ledgerStart_eq := hstart
              receptionInput := receptionInput
              receptionInput_eq := rfl
              reception := .rejected (ledgerDecoded, bankAfter)
              reception_eq := hreception
              ledgerDecoded := ledgerDecoded
              reception_outcome := .inr rfl
              reception_not_invalid := by simp
              decoderBankAfter := bankAfter
              ledgerFinished := ledgerFinished
              ledgerFinish_eq := hfinish
              clockFinished := clockFinished
              clockFinish_eq := hclockFinish }

/-- Compose observation-free preparation with observation-time execution. -/
def runInteractive {p : Parameters} (x : PreObservationInputs p)
    (h : PreInputsValid x)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    CoordinatorCollectionUpRoundStep.Result
      (attachOwnObservation x ownObservation) :=
  match prepare x h with
  | .failed reason => .failed reason
  | .prepared snapshot => observe snapshot ownObservation

/-- Every genuine pre-input reaches the existing collection start branch and
has a defined actual arm choice. The observation parameter is used only to
reuse the accepted `InputsValid` clock theorem; neither operation reads it. -/
theorem prepare_ne_failed {p : Parameters} (x : PreObservationInputs p)
    (h : PreInputsValid x)
    (ownObservation : Fin (ConstructorDimensions.D p + 1))
    (reason : CoordinatorCollectionUpRoundStep.Failure) :
    prepare x h ≠ .failed reason := by
  classical
  let started : CoordinatorPhaseClock.StartRoundResult p :=
    ⟨x.clock,
      CoordinatorPhaseClock.clockRegistersValid_gridDomain p x.etaReal x.clock
        h.clock_registers_valid,
      x.ledger.pending, none, none⟩
  have hstartEq : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending = .ok started := by
    simpa [started, attachOwnObservation, PreInputsValid.toInputsValid] using
      (CoordinatorCollectionUpRoundStep.InputsValid.startRound_frame
        (h.toInputsValid ownObservation))
  have hframe : started.clock = x.clock ∧
      started.pending = x.ledger.pending ∧
      started.ledgerCommand = none ∧ started.assignmentStart = none :=
    ⟨rfl, rfl, rfl, rfl⟩
  have hchoiceNe :
      CoordinatorLocalArmChoice.coordinatorArmChoice x.payload started.pending
        (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
        x.time (PreObservationInputs.weights x h.ledger_valid h.assignment_eq)
        x.row ≠ none := by
    unfold CoordinatorLocalArmChoice.coordinatorArmChoice
    unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
    simp only [dif_pos h.choice_valid]
    split
    · simp
    · split
      · simp
      · split <;> simp
  intro hfail
  unfold prepare at hfail
  split at hfail
  · rename_i clockFailure hclockStart
    have hfalse : Except.error clockFailure = Except.ok started :=
      hclockStart.symm.trans hstartEq
    cases hfalse
  · rename_i clockStarted hclockStart
    have hstarted : clockStarted = started :=
      Except.ok.inj (hclockStart.symm.trans hstartEq)
    split at hfail
    · rename_i hbranch
      have hchoiceNe' := hchoiceNe
      have hpending : clockStarted.pending = started.pending :=
        congrArg CoordinatorPhaseClock.StartRoundResult.pending hstarted
      rw [← hpending] at hchoiceNe'
      dsimp at hfail
      split at hfail
      · rename_i hchoice
        exact False.elim (hchoiceNe' hchoice)
      · rename_i arm hchoice
        cases hfail
    · rename_i hbranch
      have hframe' : clockStarted.clock = x.clock ∧
          clockStarted.pending = x.ledger.pending ∧
          clockStarted.ledgerCommand = none ∧
          clockStarted.assignmentStart = none := by
        rw [hstarted]
        exact hframe
      exact False.elim (hbranch hframe')

/-- Interactive preparation and observation reconstruct the exact accepted
one-round result, including failure reason and every field of a completed
dependent trace. -/
theorem runInteractive_eq_run {p : Parameters} (x : PreObservationInputs p)
    (h : PreInputsValid x)
    (ownObservation : Fin (ConstructorDimensions.D p + 1)) :
    runInteractive x h ownObservation =
      CoordinatorCollectionUpRoundStep.run
        (attachOwnObservation x ownObservation) (h.toInputsValid ownObservation) := by
  classical
  let started : CoordinatorPhaseClock.StartRoundResult p :=
    ⟨x.clock,
      CoordinatorPhaseClock.clockRegistersValid_gridDomain p x.etaReal x.clock
        h.clock_registers_valid,
      x.ledger.pending, none, none⟩
  have hstart : CoordinatorPhaseClock.startRound p x.etaReal x.time
      x.clock x.ledger.pending = .ok started := by
    simpa [started, attachOwnObservation, PreInputsValid.toInputsValid] using
      (CoordinatorCollectionUpRoundStep.InputsValid.startRound_frame
        (h.toInputsValid ownObservation))
  have hbranch : started.clock = x.clock ∧
      started.pending = x.ledger.pending ∧ started.ledgerCommand = none ∧
      started.assignmentStart = none := ⟨rfl, rfl, rfl, rfl⟩
  let weights := PreObservationInputs.weights x h.ledger_valid h.assignment_eq
  let chosen := CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
    x.ledger.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
    x.time (PreObservationInputs.weights x h.ledger_valid h.assignment_eq) x.row
  have hchosen : chosen ≠ none := by
    unfold chosen CoordinatorLocalArmChoice.coordinatorArmChoice
    unfold CoordinatorLocalArmChoice.coordinatorArmChoiceCore
    simp only [dif_pos h.choice_valid]
    split
    · simp
    · split
      · simp
      · split <;> simp
  cases hchoice : chosen with
  | none => exact False.elim (hchosen hchoice)
  | some arm =>
    have hchoiceRaw : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
        x.ledger.pending
        (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
        x.time (PreObservationInputs.weights x h.ledger_valid h.assignment_eq) x.row =
        some arm := by
      simpa [chosen] using hchoice
    have hchoiceRun : CoordinatorLocalArmChoice.coordinatorArmChoice x.payload
        x.ledger.pending
        (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
        x.time (CoordinatorCollectionUpRoundStep.complementWeights x.ledger
          x.payload h.ledger_valid h.assignment_eq) x.row = some arm := by
      simpa [PreObservationInputs.weights] using hchoiceRaw
    let snapshot : PreparedSnapshot x :=
      { inputsValid := h
        clockStarted := started
        clockStarted_eq := hstart
        clockStarted_frame := hbranch
        arm := arm
        armChoice_eq := by simpa [started] using hchoiceRaw }
    have hprepare : prepare x h = .prepared snapshot := by
      unfold prepare
      split
      · rename_i clockFailure hclockStart
        have hfalse : Except.error clockFailure = Except.ok started :=
          hclockStart.symm.trans hstart
        cases hfalse
      · rename_i clockStarted hclockStart
        have hclockStarted : clockStarted = started :=
          Except.ok.inj (hclockStart.symm.trans hstart)
        subst clockStarted
        split
        · rename_i hbranch'
          simp only [started]
          split
          · rename_i hnone
            have hnoneRaw : chosen = none := by
              simpa [chosen, PreObservationInputs.weights] using hnone
            exact False.elim (hchosen hnoneRaw)
          · rename_i arm' hsome
            have hsomeRaw : CoordinatorLocalArmChoice.coordinatorArmChoice
                x.payload x.ledger.pending
                (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
                x.time (CoordinatorCollectionUpRoundStep.complementWeights x.ledger
                  x.payload h.ledger_valid h.assignment_eq) x.row = some arm' := by
              simpa [PreObservationInputs.weights] using hsome
            have harmeq : arm' = arm :=
              Option.some.inj (hsomeRaw.symm.trans hchoiceRun)
            subst arm'
            rfl
        · rename_i hbranch'
          exact False.elim (hbranch' hbranch)
    have hstartAttached : CoordinatorPhaseClock.startRound p
        (attachOwnObservation x ownObservation).etaReal
        (attachOwnObservation x ownObservation).time
        (attachOwnObservation x ownObservation).clock
        (attachOwnObservation x ownObservation).ledger.pending = .ok started := by
      simpa [attachOwnObservation] using hstart
    have hbranchAttached : started.clock =
        (attachOwnObservation x ownObservation).clock ∧
        started.pending = (attachOwnObservation x ownObservation).ledger.pending ∧
        started.ledgerCommand = none ∧ started.assignmentStart = none := by
      simpa [attachOwnObservation] using hbranch
    have hchoiceAttached : CoordinatorLocalArmChoice.coordinatorArmChoice
        (attachOwnObservation x ownObservation).payload started.pending
        (some (CoordinatorCollectionUpRoundStep.localCutoff
          (attachOwnObservation x ownObservation).cutoffIndex))
        (attachOwnObservation x ownObservation).time
        (CoordinatorCollectionUpRoundStep.Inputs.weights
          (x := attachOwnObservation x ownObservation)
          (h.toInputsValid ownObservation).ledger_valid
          (h.toInputsValid ownObservation).assignment_eq)
        (attachOwnObservation x ownObservation).row = some arm := by
      simpa [attachOwnObservation, PreInputsValid.toInputsValid,
        started, PreObservationInputs.weights,
        CoordinatorCollectionUpRoundStep.Inputs.weights] using hchoiceRaw
    unfold runInteractive
    simp only [hprepare]
    unfold CoordinatorCollectionUpRoundStep.run
    split
    · rename_i clockFailure hclockStart
      have hfalse : Except.error clockFailure = Except.ok started :=
        hclockStart.symm.trans hstartAttached
      cases hfalse
    · rename_i clockStarted hclockStart
      have hclockStarted : clockStarted = started :=
        Except.ok.inj (hclockStart.symm.trans hstartAttached)
      subst clockStarted
      split
      · rename_i hbranch'
        simp only [attachOwnObservation, started,
          PreInputsValid.toInputsValid,
          CoordinatorCollectionUpRoundStep.Inputs.weights]
        split
        · rename_i hnone
          have hnoneRaw : chosen = none := by
            simpa [chosen, PreObservationInputs.weights,
              PreInputsValid.toInputsValid,
              CoordinatorCollectionUpRoundStep.Inputs.weights] using hnone
          exact False.elim (hchosen hnoneRaw)
        · rename_i arm' hsome
          have hsomeRaw : CoordinatorLocalArmChoice.coordinatorArmChoice
              (attachOwnObservation x ownObservation).payload started.pending
              (some (CoordinatorCollectionUpRoundStep.localCutoff
                (attachOwnObservation x ownObservation).cutoffIndex))
              (attachOwnObservation x ownObservation).time
              (CoordinatorCollectionUpRoundStep.Inputs.weights
                (x := attachOwnObservation x ownObservation)
                (h.toInputsValid ownObservation).ledger_valid
                (h.toInputsValid ownObservation).assignment_eq)
              (attachOwnObservation x ownObservation).row = some arm' := hsome
          have harmeq : arm' = arm :=
            Option.some.inj (hsomeRaw.symm.trans hchoiceAttached)
          subst arm'
          unfold observe
          rfl
      · rename_i hbranch'
        exact False.elim (hbranch' hbranchAttached)

/-- The accepted arm-choice function factors through the declared current
control of the original complete row. Preparation uses this same function and
retains all other pre-observation fields unchanged. -/
theorem armChoice_eq_of_same_current_control
    (x : PreObservationInputs p) (h : PreInputsValid x)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hcontrol : row₁.2 x.time = row₂.2 x.time) :
    CoordinatorLocalArmChoice.coordinatorArmChoice x.payload x.ledger.pending
      (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
      x.time (PreObservationInputs.weights x h.ledger_valid h.assignment_eq) row₁ =
    CoordinatorLocalArmChoice.coordinatorArmChoice x.payload x.ledger.pending
      (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
      x.time (PreObservationInputs.weights x h.ledger_valid h.assignment_eq) row₂ :=
  CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
    x.payload x.ledger.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff x.cutoffIndex))
    x.time (PreObservationInputs.weights x h.ledger_valid h.assignment_eq)
    row₁ row₂ hcontrol

end Bandits.Support.CoordinatorCollectionInteractive

end
