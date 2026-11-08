/-
Copyright (c) 2026 Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.CoordinatorCollectionUpRoundStep

/-!
# Exact fixed-register code for the accepted coordinator collection round

This module codes the result of the existing `CoordinatorCollectionUpRoundStep.run`
with its incoming registers fixed and its entire original complete row and own
grid observation varying jointly. The code retains every runtime result and
failure tag; proof certificates are reconstructed from the actual checked
operation equations.

The source order is `StartRound`, arm choice, one recorder, ledger start and
known-queue service/raw buffering, the actual selected UP decode and acceptance,
ledger finish, then clock finish (`sources/zip4/manuscript/06_interruptions.tex:37-70,235-296`,
`sources/zip4/manuscript/05_binary_transport.tex:352-429`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`). This internal
fixed-register result establishes no physical own-feedback generation,
adaptive freshness, chronological run, sender authenticity, or manuscript
closure.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.CoordinatorCollectionRunMeasurabilityRepair

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.CoordinatorCollectionUpRoundStep
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.CoordinatorLocalArmChoice
open Bandits.Support.CoordinatorRecorderComplementBridge
open Bandits.Support.CoordinatorRecordingMeasurability
open Bandits.Support.CoordinatorUpReception
open Bandits.Support.CoordinatorUpMeasurability
open Bandits.Support.AffineBatchDecoder
open Bandits.Support.AffineChannelLaw
open Bandits.Support.OrdinaryMessageCodec

abbrev Parameters := ConstructorDimensions.Parameters

variable {p : Parameters}

/-- The measurable domain varies the complete original row together with the
coordinator's own finite denominator-`D` observation. -/
abbrev RunDomain (p : Parameters) :=
  CompletePublicTable.CompleteRow p × Fin (ConstructorDimensions.D p + 1)

/-- Replace only the row and own observation of fixed incoming registers. -/
def inputAt (base : Inputs p) (value : RunDomain p) : Inputs p :=
  { etaReal := base.etaReal
    etaPositive := base.etaPositive
    n := base.n
    n_cast_identity := base.n_cast_identity
    payload := base.payload
    baseScores := base.baseScores
    ledger := base.ledger
    clock := base.clock
    upDecoderBank := base.upDecoderBank
    cutoffIndex := base.cutoffIndex
    time := base.time
    row := value.1
    ownObservation := value.2 }

/-- The accepted validity predicate contains no row or observation field, so
the original checked registers transfer unchanged across the whole domain. -/
theorem inputAt_inputsValid_iff (base : Inputs p) (value : RunDomain p) :
    CoordinatorCollectionUpRoundStep.InputsValid (inputAt base value) ↔
      CoordinatorCollectionUpRoundStep.InputsValid base := by
  constructor
  · intro hv
    exact {
      ledger_valid := hv.ledger_valid
      ledger_ready := hv.ledger_ready
      pending_nonempty := hv.pending_nonempty
      assignment_eq := hv.assignment_eq
      base_score_eq := hv.base_score_eq
      clock_parameter_valid := hv.clock_parameter_valid
      clock_registers_valid := hv.clock_registers_valid
      clock_start_time_valid := hv.clock_start_time_valid
      clock_sigma_eq := hv.clock_sigma_eq
      clock_cutoff_eq := hv.clock_cutoff_eq
      ledger_sigma_eq := hv.ledger_sigma_eq
      ledger_cutoff_eq := hv.ledger_cutoff_eq
      ledger_freeze_eq := hv.ledger_freeze_eq
      ledger_cursor_eq := hv.ledger_cursor_eq
      decoder_bank_valid := hv.decoder_bank_valid
      choice_valid := hv.choice_valid }
  · intro hv
    exact {
      ledger_valid := hv.ledger_valid
      ledger_ready := hv.ledger_ready
      pending_nonempty := hv.pending_nonempty
      assignment_eq := hv.assignment_eq
      base_score_eq := hv.base_score_eq
      clock_parameter_valid := hv.clock_parameter_valid
      clock_registers_valid := hv.clock_registers_valid
      clock_start_time_valid := hv.clock_start_time_valid
      clock_sigma_eq := hv.clock_sigma_eq
      clock_cutoff_eq := hv.clock_cutoff_eq
      ledger_sigma_eq := hv.ledger_sigma_eq
      ledger_cutoff_eq := hv.ledger_cutoff_eq
      ledger_freeze_eq := hv.ledger_freeze_eq
      ledger_cursor_eq := hv.ledger_cursor_eq
      decoder_bank_valid := hv.decoder_bank_valid
      choice_valid := hv.choice_valid }

/-- Transfer the fixed incoming validity proof to a varying complete row and
the same round's finite own observation. -/
theorem inputAt_inputsValid (base : Inputs p) (value : RunDomain p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    CoordinatorCollectionUpRoundStep.InputsValid (inputAt base value) :=
  inputAt_inputsValid_iff base value |>.2 h

/-- `StartRound` is the first literal source operation and returns the fixed
incoming clock and pending queue for every varying row and own observation. -/
theorem actualStartRound_fixed (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) :
    CoordinatorPhaseClock.startRound p (inputAt base value).etaReal
      (inputAt base value).time (inputAt base value).clock
      (inputAt base value).ledger.pending =
      .ok ⟨(inputAt base value).clock,
        CoordinatorPhaseClock.clockRegistersValid_gridDomain p
          (inputAt base value).etaReal (inputAt base value).clock
          (inputAt_inputsValid base value h).clock_registers_valid,
        (inputAt base value).ledger.pending, none, none⟩ :=
  InputsValid.startRound_frame (inputAt_inputsValid base value h)

/-- The exact incoming dependent ledger type shared by all varying inputs. -/
abbrev InputLedger (x : Inputs p) :=
  CoordinatorCollectionLedger.Ledger p x.etaReal x.etaPositive
    (payloadSourceCap x.payload) x.n x.n_cast_identity

/-- The exact input type passed to the accepted row-facing UP receiver. -/
abbrev InputReception (x : Inputs p) :=
  CoordinatorUpReception.ReceptionInput p x.etaReal x.etaPositive
    (payloadSourceCap x.payload) x.n x.n_cast_identity

/-- The clock register code contains every literal clock field. -/
def clockRegistersCode (clock : CoordinatorPhaseClock.ClockRegisters p) :=
  (clock.sigma, (clock.u, (clock.g, clock.lastProposal)))

theorem clockRegistersCode_injective :
    Function.Injective (clockRegistersCode (p := p)) := by
  intro a b h
  cases a with
  | mk asigma au ag alast =>
    cases b with
    | mk bsigma bu bg blast =>
      simp only [clockRegistersCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      rfl

instance clockRegistersCountable :
    Countable (CoordinatorPhaseClock.ClockRegisters p) :=
  clockRegistersCode_injective.countable

/-- The checked clock failure code keeps the constructor and its reason. -/
def clockFailureCode (failure : CoordinatorPhaseClock.ClockFailure) : Fin 8 :=
  match failure with
  | .invalidProposalParameter => 0
  | .invalidClockRegisters => 1
  | .incompatibleStartTime => 2
  | .missingPriorProposal => 3
  | .stalePriorProposal => 4
  | .invalidNewGridBoundary => 5
  | .noLiveAssignment => 6
  | .incompatibleFinishTime => 7

theorem clockFailureCode_injective :
    Function.Injective clockFailureCode := by
  intro a b h
  cases a <;> cases b <;> simp [clockFailureCode] at h ⊢

instance clockFailureCountable :
    Countable CoordinatorPhaseClock.ClockFailure :=
  clockFailureCode_injective.countable

/-- The assignment-start kind has its three literal constructors. -/
def assignmentStartKindCode : CoordinatorPhaseClock.AssignmentStartKind → Fin 3
  | .first => 0
  | .renewal => 1
  | .corrected => 2

theorem assignmentStartKindCode_injective :
    Function.Injective assignmentStartKindCode := by
  intro a b h
  cases a <;> cases b <;> simp [assignmentStartKindCode] at h ⊢

instance assignmentStartKindCountable :
    Countable CoordinatorPhaseClock.AssignmentStartKind :=
  assignmentStartKindCode_injective.countable

/-- The source command and assignment instruction fields are countable. -/
instance assignmentStartInstructionCountable :
    Countable (CoordinatorPhaseClock.AssignmentStartInstruction p) := by
  let code := fun i : CoordinatorPhaseClock.AssignmentStartInstruction p =>
    (i.time, i.kind)
  have hcode : Function.Injective code := by
    intro a b hab
    cases a with
    | mk atime akind =>
      cases b with
      | mk btime bkind =>
        simp only [code, Prod.mk.injEq] at hab
        rcases hab with ⟨rfl, rfl⟩
        rfl
  exact hcode.countable

def collectionLedgerCommandCode
    (command : CoordinatorPhaseClock.CollectionLedgerCommand p) : Bool × Fin p.T :=
  match command with
  | .initializeAt t => (false, t)
  | .accumulateLocalServiceAt t => (true, t)

theorem collectionLedgerCommandCode_injective :
    Function.Injective (collectionLedgerCommandCode (p := p)) := by
  intro a b h
  cases a with
  | initializeAt t₁ =>
    cases b with
    | initializeAt t₂ =>
      have ht : t₁ = t₂ := congrArg Prod.snd h
      cases ht
      rfl
    | accumulateLocalServiceAt t₂ =>
      have hf : false = true := congrArg Prod.fst h
      cases hf
  | accumulateLocalServiceAt t₁ =>
    cases b with
    | initializeAt t₂ =>
      have hf : true = false := congrArg Prod.fst h
      cases hf
    | accumulateLocalServiceAt t₂ =>
      have ht : t₁ = t₂ := congrArg Prod.snd h
      cases ht
      rfl

instance collectionLedgerCommandCountable :
    Countable (CoordinatorPhaseClock.CollectionLedgerCommand p) := by
  exact collectionLedgerCommandCode_injective.countable

/-- Start-round results are coded by their literal fields; the grid-domain
certificate is omitted and recovered by proof irrelevance. -/
def startRoundResultCode (result : CoordinatorPhaseClock.StartRoundResult p) :=
  (result.clock, (result.pending, (result.ledgerCommand, result.assignmentStart)))

theorem startRoundResultCode_injective :
    Function.Injective (startRoundResultCode (p := p)) := by
  intro a b h
  cases a with
  | mk ac ag ap al ai =>
    cases b with
    | mk bc bg bp bl bi =>
      simp only [startRoundResultCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl⟩
      rfl

instance startRoundResultCountable :
    Countable (CoordinatorPhaseClock.StartRoundResult p) :=
  startRoundResultCode_injective.countable

/-- Finish-round results have no certificate fields, so this is their exact
literal code. -/
def finishRoundResultCode (result : CoordinatorPhaseClock.FinishRoundResult p) :=
  (result.clock, (result.pending, result.ledgerCommand))

theorem finishRoundResultCode_injective :
    Function.Injective (finishRoundResultCode (p := p)) := by
  intro a b h
  cases a with
  | mk ac ap al =>
    cases b with
    | mk bc bp bl =>
      simp only [finishRoundResultCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl

instance finishRoundResultCountable :
    Countable (CoordinatorPhaseClock.FinishRoundResult p) :=
  finishRoundResultCode_injective.countable

/-- The exact code for a completed run. It stores the accepted finite recorder
code and the complete UP input/result, including the selected decoder's raw
word, parsed UP record, post-decode ledger, and whole updated bank. -/
structure CompletedRunCode (eta : ℝ) (heta : 0 < eta)
    (hcap : CoordinatorCollectionLedger.sourceLearningCap p eta)
    (n : ℕ) (hn : (n : ℝ) = eta * (ConstructorDimensions.D p : ℝ)) where
  clockStarted : CoordinatorPhaseClock.StartRoundResult p
  arm : Fin p.K
  recorderCode : CoordinatorRecordingMeasurability.OutputCode p
  enabled : Bool
  rawInput : Option (Fin p.K × ℕ)
  ledgerStarted : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn
  receptionInput : CoordinatorUpReception.ReceptionInput p eta heta hcap n hn
  reception : CoordinatorCollectionLedger.Checked
    (CoordinatorCollectionLedger.Ledger p eta heta hcap n hn ×
    CoordinatorUpReception.UpDecoderBank p)
  ledgerDecoded : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn
  decoderBankAfter : CoordinatorUpReception.UpDecoderBank p
  ledgerFinished : CoordinatorCollectionLedger.Ledger p eta heta hcap n hn
  clockFinished : CoordinatorPhaseClock.FinishRoundResult p
  rawDecoderOutput : Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  parsedDecoderOutput : Option (OrdinaryMessageCodec.UpRecord
    (CoordinatorCollectionLedger.codecParams p eta))

/-- The completed runtime code with the fixed numeric register indices of an
incoming input. Varying its row and observation does not change this type. -/
abbrev CompletedCode (x : Inputs p) :=
  CompletedRunCode (p := p) x.etaReal x.etaPositive
    (payloadSourceCap x.payload) x.n x.n_cast_identity

/-- A lossless tuple view of every runtime field in a completed code. -/
def completedCodeFields {x : Inputs p} (c : CompletedCode x) :=
  (((c.clockStarted, c.arm), (c.recorderCode, c.enabled)),
    ((c.rawInput, c.ledgerStarted), (c.receptionInput, c.reception)),
    ((c.ledgerDecoded, c.decoderBankAfter), (c.ledgerFinished, c.clockFinished)),
    (c.rawDecoderOutput, c.parsedDecoderOutput))

theorem completedCodeFields_injective {x : Inputs p} :
    Function.Injective (completedCodeFields (p := p) (x := x)) := by
  intro a b h
  cases a with
  | mk ac aa ar ae ari als ai arec ad ab alf acf araw aparsed =>
    cases b with
    | mk bc ba br be bri bls bi brec bd bb blf bcf braw bparsed =>
      simp only [completedCodeFields, Prod.mk.injEq] at h
      rcases h with ⟨⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
        ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩,
        ⟨rfl, rfl⟩⟩
      rfl

instance completedCodeCountable {x : Inputs p} : Countable (CompletedCode x) :=
  completedCodeFields_injective.countable

/-- The one output type for the accepted dependent result. Failure constructors
are retained verbatim; the success payload is a countable exact runtime code. -/
abbrev RunOutputCode (x : Inputs p) := Sum Failure (CompletedCode x)

/-- Every local failure constructor and clock reason has a distinct countable
code. -/
def failureCode (failure : Failure) : Option CoordinatorPhaseClock.ClockFailure × Fin 8 :=
  match failure with
  | .clockStart reason => (some reason, 0)
  | .wrongClockBranch => (none, 1)
  | .armChoiceDomain => (none, 2)
  | .recorderDomain => (none, 3)
  | .ledgerStartDomain => (none, 4)
  | .upReceptionDomain => (none, 5)
  | .ledgerFinishDomain => (none, 6)
  | .clockFinish reason => (some reason, 7)

theorem failureCode_injective : Function.Injective failureCode := by
  intro a b h
  cases a with
  | clockStart ra =>
    cases b with
    | clockStart rb =>
      simp [failureCode] at h
      cases h
      rfl
    | clockFinish rb => simp [failureCode] at h
    | wrongClockBranch => simp [failureCode] at h
    | armChoiceDomain => simp [failureCode] at h
    | recorderDomain => simp [failureCode] at h
    | ledgerStartDomain => simp [failureCode] at h
    | upReceptionDomain => simp [failureCode] at h
    | ledgerFinishDomain => simp [failureCode] at h
  | clockFinish ra =>
    cases b with
    | clockStart rb => simp [failureCode] at h
    | clockFinish rb =>
      simp [failureCode] at h
      cases h
      rfl
    | wrongClockBranch => simp [failureCode] at h
    | armChoiceDomain => simp [failureCode] at h
    | recorderDomain => simp [failureCode] at h
    | ledgerStartDomain => simp [failureCode] at h
    | upReceptionDomain => simp [failureCode] at h
    | ledgerFinishDomain => simp [failureCode] at h
  | wrongClockBranch => cases b <;> simp [failureCode] at h ⊢
  | armChoiceDomain => cases b <;> simp [failureCode] at h ⊢
  | recorderDomain => cases b <;> simp [failureCode] at h ⊢
  | ledgerStartDomain => cases b <;> simp [failureCode] at h ⊢
  | upReceptionDomain => cases b <;> simp [failureCode] at h ⊢
  | ledgerFinishDomain => cases b <;> simp [failureCode] at h ⊢

instance failureCountable : Countable Failure := failureCode_injective.countable

instance runOutputCodeCountable {x : Inputs p} : Countable (RunOutputCode x) := by
  infer_instance

/-- Encode the actual successful dependent trace, omitting only its Prop
certificates. -/
def encodeTrace {x : Inputs p} (trace : Trace x) : CompletedCode x where
  clockStarted := trace.clockStarted
  arm := trace.arm
  recorderCode := CoordinatorRecordingMeasurability.encodeOutput trace.recorder
  enabled := trace.enabled
  rawInput := trace.rawInput
  ledgerStarted := trace.ledgerStarted
  receptionInput := trace.receptionInput
  reception := trace.reception
  ledgerDecoded := trace.ledgerDecoded
  decoderBankAfter := trace.decoderBankAfter
  ledgerFinished := trace.ledgerFinished
  clockFinished := trace.clockFinished
  rawDecoderOutput := (CoordinatorUpReception.decoderTransition trace.receptionInput).2
  parsedDecoderOutput := CoordinatorUpReception.parsedDecoderOutput trace.receptionInput

/-- Encode the existing `Result`; no second collection operation is defined. -/
def encodeResult {x : Inputs p} : Result x → RunOutputCode x
  | .failed reason => .inl reason
  | .completed trace => .inr (encodeTrace trace)

/-- Run the accepted operation after varying only the original complete row
and same-round own observation. -/
def runAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p) :
    Result (inputAt base value) :=
  CoordinatorCollectionUpRoundStep.run (inputAt base value)
    (inputAt_inputsValid base value h)

/-- The exact countable output code of the existing accepted run. -/
def runOutputCodeAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) : RunOutputCode base :=
  encodeResult (x := inputAt base value) (runAt base h value)

/-- Glue a countable-valued branch code to jointly measurable fibers. The
fiber code is a literal intermediate register, not an adaptedness premise. -/
theorem measurable_of_countable_cases {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [Countable β] [MeasurableSingletonClass β]
    [MeasurableSpace γ] [Countable γ] [MeasurableSingletonClass γ]
    (code : α → β) (hcode : Measurable code)
    (fiber : β → α → γ)
    (hfiber : ∀ b, Measurable (fun x => fiber b x)) :
    Measurable (fun x => fiber (code x) x) := by
  apply measurable_to_countable'
  intro target
  change MeasurableSet {x | fiber (code x) x = target}
  have hpre : {x | fiber (code x) x = target} =
      ⋃ b, {x | code x = b} ∩ {x | fiber b x = target} := by
    ext x
    simp
  rw [hpre]
  exact MeasurableSet.iUnion fun b =>
    (measurableSet_eq_fun hcode measurable_const).inter
      (measurableSet_eq_fun (hfiber b) measurable_const)

/-- The actual accepted arm-choice register after `StartRound`. The fixed
valid input makes `StartRound` retain the incoming pending set; only its full
row current control varies here. -/
def armChoiceAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) : Option (Fin p.K) :=
  CoordinatorLocalArmChoice.coordinatorArmChoice base.payload base.ledger.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff base.cutoffIndex))
    base.time
    (Inputs.weights (x := base) h.ledger_valid h.assignment_eq)
    (inputAt base value).row

/-- Arm choice is jointly measurable over the entire original row and the
same round's typed own observation. -/
theorem measurable_armChoiceAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable (armChoiceAt base h : RunDomain p → Option (Fin p.K)) := by
  exact (CoordinatorLocalArmChoice.measurable_coordinatorArmChoice base.payload
    base.ledger.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff base.cutoffIndex))
    base.time (Inputs.weights (x := base) h.ledger_valid h.assignment_eq)).comp
      measurable_fst

/-- The actual accepted recorder output on a fixed source-selected arm,
jointly varying the complete row and own observation. -/
def recorderAtFixedArm (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (arm : Fin p.K) (value : RunDomain p) :
    Option (CoordinatorRecordingOperation.Output p) :=
  CoordinatorRecordingOperation.run
    (CoordinatorRecordingMeasurability.inputAt
      (CoordinatorRecorderComplementBridge.recorderInput
        (InputsValid.recorderInput (x := base) h arm))
      (value.1, (arm, value.2)))

/-- Fixed-arm recorder measurability uses the accepted joint recorder theorem
on the entire complete row and own observation. -/
theorem measurable_recorderAtFixedArm (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (arm : Fin p.K) :
    Measurable (fun value : RunDomain p => recorderAtFixedArm base h arm value) := by
  let bridgeBase := InputsValid.recorderInput (x := base) h arm
  let operationBase := CoordinatorRecorderComplementBridge.recorderInput bridgeBase
  have hvalue : Measurable (fun value : RunDomain p =>
      (value.1, (arm, value.2)) :
      RunDomain p → CoordinatorRecordingMeasurability.RecorderDomain p) := by
    exact measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  exact (CoordinatorRecordingMeasurability.measurable_run operationBase).comp hvalue

/-- The source-order recorder result, including the arm-choice failure
branch, after the accepted arm-choice computation. -/
def recorderAtChoice (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) :
    Option (CoordinatorRecordingOperation.Output p) :=
  match armChoiceAt base h value with
  | none => none
  | some arm => recorderAtFixedArm base h arm value

/-- The single recorder call is measurable after finite decomposition of the
actual earlier arm code. -/
theorem measurable_recorderAtChoice (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable (recorderAtChoice base h : RunDomain p →
      Option (CoordinatorRecordingOperation.Output p)) := by
  change Measurable (fun value : RunDomain p =>
    match armChoiceAt base h value with
    | none => none
    | some arm => recorderAtFixedArm base h arm value)
  refine measurable_of_countable_cases (code := armChoiceAt base h)
    (hcode := measurable_armChoiceAt base h)
    (fiber := fun arm value =>
      match arm with
      | none => none
      | some i => recorderAtFixedArm base h i value) ?_
  intro arm
  cases arm with
  | none => exact measurable_const
  | some i => exact measurable_recorderAtFixedArm base h i

/-- The checked ledger-start result after the actual recorder, retaining a
separate outer `none` for the earlier arm or recorder failure. -/
def ledgerStartAfterRecorder (base : Inputs p)
    (recorder : Option (CoordinatorRecordingOperation.Output p)) :
    Option (CoordinatorCollectionLedger.Checked (InputLedger base)) :=
  match recorder with
  | none => none
  | some output => some (CoordinatorCollectionLedger.startRound base.ledger
      (CoordinatorCollectionUpRoundStep.sourceRound base.time)
      (InputsValid.sourceLearningEnabled base)
      (InputsValid.rawInputOfRecorder output))

/-- The ledger-start stage output is an explicit countable code; this local
instance does not introduce another global ledger-countability instance. -/
instance ledgerStartStageMeasurableSpace (base : Inputs p) :
    MeasurableSpace (Option (CoordinatorCollectionLedger.Checked
      (InputLedger base))) := ⊤

/-- Ledger service, including invalid or rejected local checks, is measurable
as the deterministic next operation on the finite recorder code. -/
theorem measurable_ledgerStartAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable (fun value : RunDomain p =>
      ledgerStartAfterRecorder base (recorderAtChoice base h value)) := by
  have hstage : Measurable (ledgerStartAfterRecorder base) := Measurable.of_discrete
  exact hstage.comp (measurable_recorderAtChoice base h)

/-- Sound certificates for a completed output code. These propositions are
precisely the accepted source-ordered operation equations used to reconstruct
the dependent trace. -/
structure CompletedCodeSound (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) (c : CompletedCode base) : Prop where
  start_eq : CoordinatorPhaseClock.startRound p (inputAt base value).etaReal
    (inputAt base value).time (inputAt base value).clock
    (inputAt base value).ledger.pending = .ok c.clockStarted
  start_frame : c.clockStarted.clock = (inputAt base value).clock ∧
    c.clockStarted.pending = (inputAt base value).ledger.pending ∧
    c.clockStarted.ledgerCommand = none ∧ c.clockStarted.assignmentStart = none
  arm_eq : CoordinatorLocalArmChoice.coordinatorArmChoice
    (inputAt base value).payload c.clockStarted.pending
    (some (CoordinatorCollectionUpRoundStep.localCutoff
      (inputAt base value).cutoffIndex)) (inputAt base value).time
    (Inputs.weights (x := inputAt base value)
      (inputAt_inputsValid base value h).ledger_valid
      (inputAt_inputsValid base value h).assignment_eq)
    (inputAt base value).row = some c.arm
  recorder_eq : CoordinatorRecorderComplementBridge.run
    (InputsValid.recorderInput (x := inputAt base value)
      (inputAt_inputsValid base value h) c.arm) =
        some (CoordinatorRecordingMeasurability.decodeOutput c.recorderCode)
  enabled_eq : c.enabled = InputsValid.sourceLearningEnabled (inputAt base value)
  rawInput_eq : c.rawInput = InputsValid.rawInputOfRecorder
    (CoordinatorRecordingMeasurability.decodeOutput c.recorderCode)
  ledger_start_eq : CoordinatorCollectionLedger.startRound
    (inputAt base value).ledger
    (CoordinatorCollectionUpRoundStep.sourceRound (inputAt base value).time)
    c.enabled c.rawInput = .success c.ledgerStarted
  receptionInput_eq : c.receptionInput = CoordinatorUpMeasurability.receptionInputAtRow
    (inputAt base value).row
    (InputsValid.upInputs (x := inputAt base value) c.ledgerStarted)
    (inputAt base value).time
  reception_eq : CoordinatorUpMeasurability.receiveUpAtRow
    (inputAt base value).row
    (InputsValid.upInputs (x := inputAt base value) c.ledgerStarted)
    (inputAt base value).time = c.reception
  reception_outcome : c.reception = .success (c.ledgerDecoded, c.decoderBankAfter) ∨
    c.reception = .rejected (c.ledgerDecoded, c.decoderBankAfter)
  ledger_finish_eq : CoordinatorCollectionLedger.finishRound c.ledgerDecoded =
    .success c.ledgerFinished
  clock_finish_eq : CoordinatorPhaseClock.finishRound p
    (inputAt base value).etaReal (inputAt base value).time
    c.clockStarted.clock c.ledgerFinished.pending
    (inputAt base value).row = .ok c.clockFinished
  raw_decoder_eq : c.rawDecoderOutput =
    (CoordinatorUpReception.decoderTransition c.receptionInput).2
  parsed_decoder_eq : c.parsedDecoderOutput =
    CoordinatorUpReception.parsedDecoderOutput c.receptionInput

/-- Proof-only relation connecting a countable code back to the exact result
constructor and, on success, all fields of its dependent trace. -/
inductive RunOutputCodeCertificate (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) : RunOutputCode base → Type where
  | failed (reason : Failure)
      (run_eq : runAt base h value = .failed reason) :
      RunOutputCodeCertificate base h value (.inl reason)
  | completed (code : CompletedCode base)
      (sound : CompletedCodeSound base h value code) :
      RunOutputCodeCertificate base h value (.inr code)

/-- Reconstruct the entire dependent accepted result from the original
incoming data, row, observation, exact runtime code, and its proved operation
equations. All omitted certificates are ordinary propositions. -/
def decodeRunOutputCode (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) : (code : RunOutputCode base) →
      RunOutputCodeCertificate base h value code → Result (inputAt base value)
  | .inl reason, .failed _ _ => .failed reason
  | .inr code, .completed _ sound => .completed {
      inputsValid := inputAt_inputsValid base value h
      clockStarted := code.clockStarted
      clockStarted_eq := sound.start_eq
      clockStarted_frame := sound.start_frame
      arm := code.arm
      armChoice_eq := sound.arm_eq
      recorder := CoordinatorRecordingMeasurability.decodeOutput code.recorderCode
      recorder_eq := sound.recorder_eq
      enabled := code.enabled
      enabled_eq := sound.enabled_eq
      rawInput := code.rawInput
      rawInput_eq := sound.rawInput_eq
      ledgerStarted := code.ledgerStarted
      ledgerStart_eq := sound.ledger_start_eq
      receptionInput := code.receptionInput
      receptionInput_eq := sound.receptionInput_eq
      reception := code.reception
      reception_eq := sound.reception_eq
      ledgerDecoded := code.ledgerDecoded
      decoderBankAfter := code.decoderBankAfter
      reception_outcome := sound.reception_outcome
      reception_not_invalid := by
        intro hinvalid
        rcases sound.reception_outcome with hs | hr
        · rw [hs] at hinvalid
          cases hinvalid
        · rw [hr] at hinvalid
          cases hinvalid
      ledgerFinished := code.ledgerFinished
      ledgerFinish_eq := sound.ledger_finish_eq
      clockFinished := code.clockFinished
      clockFinish_eq := sound.clock_finish_eq }

/-- The code of every actual run has the operation equations needed for exact
dependent reconstruction. -/
def runOutputCodeAt_sound (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (value : RunDomain p) :
    RunOutputCodeCertificate base h value (runOutputCodeAt base h value) := by
  cases hr : runAt base h value with
  | failed reason =>
      have hcode : runOutputCodeAt base h value = .inl reason := by
        change encodeResult (runAt base h value) = .inl reason
        rw [hr]
        rfl
      rw [hcode]
      exact .failed reason hr
  | completed trace =>
      have hcode : runOutputCodeAt base h value =
          .inr (encodeTrace (x := inputAt base value) trace) := by
        change encodeResult (runAt base h value) =
          .inr (encodeTrace (x := inputAt base value) trace)
        rw [hr]
        rfl
      rw [hcode]
      refine RunOutputCodeCertificate.completed (base := base) (h := h)
        (value := value) (encodeTrace (x := inputAt base value) trace) ?_
      refine {
        start_eq := trace.clockStarted_eq
        start_frame := trace.clockStarted_frame
        arm_eq := trace.armChoice_eq
        recorder_eq := ?_
        enabled_eq := trace.enabled_eq
        rawInput_eq := trace.rawInput_eq
        ledger_start_eq := trace.ledgerStart_eq
        receptionInput_eq := trace.receptionInput_eq
        reception_eq := trace.reception_eq
        reception_outcome := trace.reception_outcome
        ledger_finish_eq := trace.ledgerFinish_eq
        clock_finish_eq := trace.clockFinish_eq
        raw_decoder_eq := rfl
        parsed_decoder_eq := rfl }
      simpa only [encodeTrace,
        CoordinatorRecordingMeasurability.decodeOutput_encodeOutput] using
        trace.recorder_eq

/-- Only the exact countable output code receives the discrete sigma algebra. -/
instance runOutputCodeMeasurableSpace (base : Inputs p) :
    MeasurableSpace (RunOutputCode base) := ⊤

/-- The literal fixed StartRound result, including its checked grid certificate. -/
def startedClock (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) : StartRoundResult p :=
  ⟨base.clock, clockRegistersValid_gridDomain p base.etaReal base.clock
    h.clock_registers_valid, base.ledger.pending, none, none⟩

/-- Collection FinishRound returns this literal command after ledger finish. -/
def finishedClock (base : Inputs p) (ledger : InputLedger base) : FinishRoundResult p :=
  ⟨base.clock, ledger.pending, some (.accumulateLocalServiceAt base.time)⟩

theorem actualFinishRound_fixed (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (ledger : InputLedger base) (row : CompleteRow p) :
    CoordinatorPhaseClock.finishRound p base.etaReal base.time base.clock
      ledger.pending row = .ok (finishedClock base ledger) := by
  have hcutoff := h.ledger_time_bounds.2.2.2.2.2.2.1
  rw [h.ledger_cutoff_eq, h.ledger_cursor_eq] at hcutoff
  exact CoordinatorPhaseClock.finishRound_collection p base.etaReal base.time
    base.payload.sigma base.cutoffIndex base.clock ledger.pending row
    h.clock_registers_valid h.clock_sigma_eq h.clock_cutoff_eq
    (by simpa only [CoordinatorCollectionUpRoundStep.sourceCutoff,
      CoordinatorCollectionUpRoundStep.sourceRound, Nat.add_le_add_iff_right] using hcutoff)

/-- The receiver boundary on a fixed earlier ledger still varies the SAME
entire original row and its own grid observation. -/
def receptionAtLedger (base : Inputs p) (ledger : InputLedger base)
    (value : RunDomain p) : InputReception base :=
  CoordinatorUpMeasurability.receptionInputAtRow value.1
    (InputsValid.upInputs (x := inputAt base value) ledger) base.time

/-- Countable observation branches feed the accepted joint row receiver API. -/
theorem measurable_receptionAtLedger (base : Inputs p) (ledger : InputLedger base) :
    Measurable (receptionAtLedger base ledger) := by
  refine measurable_of_countable_cases (code := fun value : RunDomain p => value.2)
    (hcode := measurable_snd)
    (fiber := fun observation value =>
      CoordinatorUpMeasurability.receptionInputAtRow value.1
        (ledger, (base.upDecoderBank, (base.time, observation))) base.time) ?_
  intro observation
  exact (CoordinatorUpMeasurability.measurable_receptionInputAtRow base.time).comp
    (measurable_fst.prodMk measurable_const)

/-- Select the actual reception input only after this computation's own
successful ledger start. Earlier failures have no reception input. -/
def selectedReceptionInputAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p) :
    Option (InputReception base) :=
  match ledgerStartAfterRecorder base (recorderAtChoice base h value) with
  | some (.success ledger) => some (receptionAtLedger base ledger value)
  | _ => none

instance selectedReceptionInputMeasurableSpace (base : Inputs p) :
    MeasurableSpace (Option (InputReception base)) := ⊤

/-- The crucial bridge splits on the SAME-computation countable ledger output;
no fixed-ledger premise replaces the produced ledger. -/
theorem measurable_selectedReceptionInputAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable (selectedReceptionInputAt base h) := by
  refine measurable_of_countable_cases
    (code := fun value => ledgerStartAfterRecorder base (recorderAtChoice base h value))
    (hcode := measurable_ledgerStartAt base h)
    (fiber := fun stage value => match stage with
      | some (.success ledger) => some (receptionAtLedger base ledger value)
      | _ => none) ?_
  intro stage
  cases stage with
  | none => exact measurable_const
  | some stage =>
    cases stage with
    | invalid => exact measurable_const
    | rejected ledger => exact measurable_const
    | success ledger =>
      exact (Measurable.of_discrete
        (f := (some : InputReception base → Option (InputReception base)))).comp
          (measurable_receptionAtLedger base ledger)

/-- Encode ledger finish after either non-invalid reception tag. This is a
code assembler using the accepted ledger operation, not another run operation. -/
def finishReceptionCode (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K)
    (recorder : CoordinatorRecordingOperation.Output p)
    (started : InputLedger base) (input : InputReception base)
    (reception : CoordinatorCollectionLedger.Checked
      (InputLedger base × CoordinatorUpReception.UpDecoderBank p))
    (decoded : InputLedger base) (bank : CoordinatorUpReception.UpDecoderBank p) :
    RunOutputCode base :=
  match CoordinatorCollectionLedger.finishRound decoded with
  | .invalid | .rejected _ => .inl .ledgerFinishDomain
  | .success finished => .inr {
      clockStarted := startedClock base h
      arm := arm
      recorderCode := CoordinatorRecordingMeasurability.encodeOutput recorder
      enabled := InputsValid.sourceLearningEnabled base
      rawInput := InputsValid.rawInputOfRecorder recorder
      ledgerStarted := started
      receptionInput := input
      reception := reception
      ledgerDecoded := decoded
      decoderBankAfter := bank
      ledgerFinished := finished
      clockFinished := finishedClock base finished
      rawDecoderOutput := (CoordinatorUpReception.decoderTransition input).2
      parsedDecoderOutput := CoordinatorUpReception.parsedDecoderOutput input }

/-- Keep success and ordinary rejection distinct, and invalid as an error. -/
def receptionCode (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K)
    (recorder : CoordinatorRecordingOperation.Output p)
    (started : InputLedger base) (input : InputReception base) : RunOutputCode base :=
  match CoordinatorUpReception.receiveUp input with
  | .invalid => .inl .upReceptionDomain
  | .success (decoded, bank) => finishReceptionCode base h arm recorder started input
      (.success (decoded, bank)) decoded bank
  | .rejected (decoded, bank) => finishReceptionCode base h arm recorder started input
      (.rejected (decoded, bank)) decoded bank

/-- Continue the exact code after a fixed recorder result. -/
def codeAfterRecorder (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K)
    (recorder : CoordinatorRecordingOperation.Output p) (value : RunDomain p) :
    RunOutputCode base :=
  match InputsValid.ledgerStart base recorder with
  | .invalid | .rejected _ => .inl .ledgerStartDomain
  | .success started => receptionCode base h arm recorder started
      (receptionAtLedger base started value)

theorem measurable_codeAfterRecorder (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K)
    (recorder : CoordinatorRecordingOperation.Output p) :
    Measurable (codeAfterRecorder base h arm recorder) := by
  unfold codeAfterRecorder
  cases InputsValid.ledgerStart base recorder with
  | invalid => exact measurable_const
  | rejected ledger => exact measurable_const
  | success ledger =>
    exact (Measurable.of_discrete (f := receptionCode base h arm recorder ledger)).comp
      (measurable_receptionAtLedger base ledger)

/-- Continue after the pre-feedback arm choice and the single recorder call. -/
def codeAfterArm (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K)
    (value : RunDomain p) : RunOutputCode base :=
  match recorderAtFixedArm base h arm value with
  | none => .inl .recorderDomain
  | some recorder => codeAfterRecorder base h arm recorder value

theorem measurable_codeAfterArm (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K) :
    Measurable (codeAfterArm base h arm) := by
  refine measurable_of_countable_cases (code := recorderAtFixedArm base h arm)
    (hcode := measurable_recorderAtFixedArm base h arm)
    (fiber := fun output value => match output with
      | none => (Sum.inl Failure.recorderDomain : RunOutputCode base)
      | some recorder => codeAfterRecorder base h arm recorder value) ?_
  intro output
  cases output with
  | none => exact measurable_const
  | some recorder => exact measurable_codeAfterRecorder base h arm recorder

/-- Source-ordered code assembly, with each operation the accepted literal one. -/
def assembledCodeAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p) :
    RunOutputCode base :=
  match armChoiceAt base h value with
  | none => .inl .armChoiceDomain
  | some arm => codeAfterArm base h arm value

theorem measurable_assembledCodeAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable (assembledCodeAt base h) := by
  refine measurable_of_countable_cases (code := armChoiceAt base h)
    (hcode := measurable_armChoiceAt base h)
    (fiber := fun arm value => match arm with
      | none => (Sum.inl Failure.armChoiceDomain : RunOutputCode base)
      | some arm => codeAfterArm base h arm value) ?_
  intro arm
  cases arm with
  | none => exact measurable_const
  | some arm => exact measurable_codeAfterArm base h arm

/-- The recorder bridge is exactly the accepted operation at the same row,
actual arm, and original observation. -/
theorem recorderAtFixedArm_eq (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (arm : Fin p.K) (value : RunDomain p) :
    CoordinatorRecorderComplementBridge.run
      (InputsValid.recorderInput (x := inputAt base value)
        (inputAt_inputsValid base value h) arm) = recorderAtFixedArm base h arm value := by
  rw [CoordinatorRecorderComplementBridge.run_eq_accepted]
  rfl

/-- Encode the dependent operation before varying its two original coordinates.
Keeping the input fixed here avoids rewriting inside dependent input indices. -/
theorem encode_run_eq_assembled (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    encodeResult (CoordinatorCollectionUpRoundStep.run base h) =
      assembledCodeAt base h (base.row, base.ownObservation) := by
  classical
  let value : RunDomain p := (base.row, base.ownObservation)
  change encodeResult (CoordinatorCollectionUpRoundStep.run base h) = assembledCodeAt base h value
  unfold CoordinatorCollectionUpRoundStep.run
  split
  · rename_i reason hstart
    have hh := InputsValid.startRound_frame h
    rw [hstart] at hh
    cases hh
  · rename_i clock hstart
    have hc : clock = startedClock base h :=
      Except.ok.inj (hstart.symm.trans (InputsValid.startRound_frame h))
    subst clock
    dsimp +instances only [ActiveRoundActions.Follower, PublicDiscreteDraws.followerCount]
    have hframe : (startedClock base h).clock = base.clock ∧
        (startedClock base h).pending = base.ledger.pending ∧
        (startedClock base h).ledgerCommand = none ∧
        (startedClock base h).assignmentStart = none := ⟨rfl, rfl, rfl, rfl⟩
    simp only [dite_eq_left hframe]
    unfold assembledCodeAt
    split <;> rename_i hchoice
    · change armChoiceAt base h value = none at hchoice
      simp only [hchoice, encodeResult]
    · rename_i arm
      change armChoiceAt base h value = some arm at hchoice
      simp only [hchoice]
      unfold codeAfterArm
      split <;> rename_i hrecorder
      · change recorderAtFixedArm base h arm value = none at hrecorder
        simp only [hrecorder, encodeResult]
      · rename_i recorder
        change recorderAtFixedArm base h arm value = some recorder at hrecorder
        simp only [hrecorder]
        unfold codeAfterRecorder InputsValid.ledgerStart
        split <;> rename_i hstart
        · simp only [hstart, encodeResult]
        · simp only [hstart, encodeResult]
        · rename_i started
          simp only [hstart]
          unfold receptionCode
          split <;> rename_i hreception
          · change CoordinatorUpReception.receiveUp (receptionAtLedger base started value) =
              .invalid at hreception
            simp only [hreception, encodeResult]
          · rename_i decoded bank
            change CoordinatorUpReception.receiveUp (receptionAtLedger base started value) =
              .success (decoded, bank) at hreception
            simp only [hreception]
            unfold finishReceptionCode
            split <;> rename_i hfinish
            · simp only [hfinish, encodeResult]
            · simp only [hfinish, encodeResult]
            · rename_i finished
              simp only [hfinish]
              split
              · rename_i reason hclock
                change CoordinatorPhaseClock.finishRound p base.etaReal base.time base.clock
                  finished.pending base.row = .error reason at hclock
                have hh := actualFinishRound_fixed base h finished base.row
                rw [hclock] at hh
                cases hh
              · rename_i clock hclock
                have hc : clock = finishedClock base finished := Except.ok.inj
                  (hclock.symm.trans (actualFinishRound_fixed base h finished base.row))
                subst clock
                rfl
          · rename_i decoded bank
            change CoordinatorUpReception.receiveUp (receptionAtLedger base started value) =
              .rejected (decoded, bank) at hreception
            simp only [hreception]
            unfold finishReceptionCode
            split <;> rename_i hfinish
            · simp only [hfinish, encodeResult]
            · simp only [hfinish, encodeResult]
            · rename_i finished
              simp only [hfinish]
              split
              · rename_i reason hclock
                change CoordinatorPhaseClock.finishRound p base.etaReal base.time base.clock
                  finished.pending base.row = .error reason at hclock
                have hh := actualFinishRound_fixed base h finished base.row
                rw [hclock] at hh
                cases hh
              · rename_i clock hclock
                have hc : clock = finishedClock base finished := Except.ok.inj
                  (hclock.symm.trans (actualFinishRound_fixed base h finished base.row))
                subst clock
                rfl

/-- The fixed-input tail code ignores the original row fields that `inputAt`
replaces. Split checked outputs so no equality of entire incoming Inputs is used. -/
theorem finishReceptionCode_inputAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p)
    (arm : Fin p.K) (recorder : CoordinatorRecordingOperation.Output p)
    (started : InputLedger base) (input : InputReception base)
    (reception : CoordinatorCollectionLedger.Checked
      (InputLedger base × CoordinatorUpReception.UpDecoderBank p))
    (decoded : InputLedger base) (bank : CoordinatorUpReception.UpDecoderBank p) :
    finishReceptionCode (inputAt base value) (inputAt_inputsValid base value h)
      arm recorder started input reception decoded bank =
      finishReceptionCode base h arm recorder started input reception decoded bank := by
  unfold finishReceptionCode
  dsimp only [inputAt]
  cases CoordinatorCollectionLedger.finishRound decoded <;> rfl

theorem receptionCode_inputAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p)
    (arm : Fin p.K) (recorder : CoordinatorRecordingOperation.Output p)
    (started : InputLedger base) (input : InputReception base) :
    receptionCode (inputAt base value) (inputAt_inputsValid base value h)
      arm recorder started input = receptionCode base h arm recorder started input := by
  unfold receptionCode
  dsimp only [inputAt]
  cases CoordinatorUpReception.receiveUp input with
  | invalid => rfl
  | success result =>
    rcases result with ⟨decoded, bank⟩
    exact finishReceptionCode_inputAt base h value arm recorder started input _ decoded bank
  | rejected result =>
    rcases result with ⟨decoded, bank⟩
    exact finishReceptionCode_inputAt base h value arm recorder started input _ decoded bank

theorem codeAfterRecorder_inputAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p)
    (arm : Fin p.K) (recorder : CoordinatorRecordingOperation.Output p) :
    codeAfterRecorder (inputAt base value) (inputAt_inputsValid base value h) arm recorder value =
      codeAfterRecorder base h arm recorder value := by
  unfold codeAfterRecorder
  have hs : InputsValid.ledgerStart (inputAt base value) recorder =
      InputsValid.ledgerStart base recorder := rfl
  rw [hs]
  cases InputsValid.ledgerStart base recorder with
  | invalid => rfl
  | rejected ledger => rfl
  | success ledger => exact receptionCode_inputAt base h value arm recorder ledger _

theorem codeAfterArm_inputAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p) (arm : Fin p.K) :
    codeAfterArm (inputAt base value) (inputAt_inputsValid base value h) arm value =
      codeAfterArm base h arm value := by
  unfold codeAfterArm
  have hr : recorderAtFixedArm (inputAt base value) (inputAt_inputsValid base value h) arm value =
      recorderAtFixedArm base h arm value := rfl
  rw [hr]
  cases recorderAtFixedArm base h arm value with
  | none => rfl
  | some recorder => exact codeAfterRecorder_inputAt base h value arm recorder

/-- Code assembly equals encoding the ACTUAL accepted dependent run. -/
theorem runOutputCodeAt_eq_assembled (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p) :
    runOutputCodeAt base h value = assembledCodeAt base h value := by
  apply Eq.trans (encode_run_eq_assembled (inputAt base value)
    (inputAt_inputsValid base value h))
  change assembledCodeAt (inputAt base value) (inputAt_inputsValid base value h) value = _
  unfold assembledCodeAt
  have ha : armChoiceAt (inputAt base value) (inputAt_inputsValid base value h) value =
      armChoiceAt base h value := rfl
  rw [ha]
  cases armChoiceAt base h value with
  | none => rfl
  | some arm => exact codeAfterArm_inputAt base h value arm

/-- Complete joint measurability over the entire continuous row and the SAME
finite own observation, for the exact accepted run output code. -/
theorem measurable_runOutputCodeAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable (runOutputCodeAt base h) := by
  have heq : runOutputCodeAt base h = assembledCodeAt base h :=
    funext (runOutputCodeAt_eq_assembled base h)
  rw [heq]
  exact measurable_assembledCodeAt base h

/-- Encoding loses only proof fields of a fixed-input successful trace. -/
theorem encodeTrace_injective {x : Inputs p} :
    Function.Injective (encodeTrace (x := x)) := by
  intro a b hab
  have hrec : a.recorder = b.recorder := by
    have hh := congrArg (fun c : CompletedCode x =>
      CoordinatorRecordingMeasurability.decodeOutput c.recorderCode) hab
    simpa only [encodeTrace, CoordinatorRecordingMeasurability.decodeOutput_encodeOutput] using hh
  cases a
  cases b
  simp only [encodeTrace, CompletedRunCode.mk.injEq] at hab
  rcases hab with ⟨rfl, rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, _, _⟩
  cases hrec
  rfl

theorem encodeResult_injective {x : Inputs p} :
    Function.Injective (encodeResult (x := x)) := by
  intro a b hab
  cases a with
  | failed ra =>
    cases b with
    | failed rb => exact congrArg Result.failed (Sum.inl.inj hab)
    | completed tb => cases hab
  | completed ta =>
    cases b with
    | failed rb => cases hab
    | completed tb => exact congrArg Result.completed (encodeTrace_injective (Sum.inr.inj hab))

/-- Every certified code decodes back to exactly that code, including the raw
and parsed decoder outputs justified by its certificate. -/
theorem encode_decodeRunOutputCode (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p)
    (code : RunOutputCode base) (certificate : RunOutputCodeCertificate base h value code) :
    encodeResult (decodeRunOutputCode base h value code certificate) = code := by
  cases certificate with
  | failed reason hr => rfl
  | completed code sound =>
    apply congrArg Sum.inr
    apply completedCodeFields_injective
    dsimp only [decodeRunOutputCode, encodeResult, encodeTrace, completedCodeFields]
    rw [CoordinatorRecordingMeasurability.encodeOutput_decodeOutput,
      sound.raw_decoder_eq, sound.parsed_decoder_eq]
    rfl

/-- Explicit inverse at the ORIGINAL input, complete row, and own observation:
the reconstructed object equals the ENTIRE accepted dependent Result. -/
theorem decode_runOutputCodeAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p) :
    decodeRunOutputCode base h value (runOutputCodeAt base h value)
      (runOutputCodeAt_sound base h value) = runAt base h value := by
  apply encodeResult_injective
  exact encode_decodeRunOutputCode base h value (runOutputCodeAt base h value)
    (runOutputCodeAt_sound base h value)

/-- Every event on the exact countable result code is measurable. -/
theorem measurableSet_runOutput_event (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (event : Set (RunOutputCode base)) :
    MeasurableSet {value | runOutputCodeAt base h value ∈ event} :=
  (measurable_runOutputCodeAt base h) (MeasurableSet.of_discrete : MeasurableSet event)

/-- Each individual Failure, including each clock reason, has a measurable
actual-run event. -/
theorem measurableSet_runAt_failed (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (reason : Failure) :
    MeasurableSet {value | runAt base h value = .failed reason} := by
  have hevent : {value | runAt base h value = .failed reason} =
      {value | runOutputCodeAt base h value = .inl reason} := by
    ext value
    exact (encodeResult_injective.eq_iff).symm
  rw [hevent]
  exact (measurable_runOutputCodeAt base h) (measurableSet_singleton (.inl reason))

/-- Completion of the actual dependent run is measurable. -/
theorem measurableSet_runAt_completed (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    MeasurableSet {value | ∃ trace, runAt base h value = .completed trace} := by
  have hevent : {value | ∃ trace, runAt base h value = .completed trace} =
      {value | ∃ code, runOutputCodeAt base h value = .inr code} := by
    ext value
    change (∃ trace, runAt base h value = .completed trace) ↔
      ∃ code, runOutputCodeAt base h value = .inr code
    cases hr : runAt base h value with
    | failed reason => simp only [runOutputCodeAt, hr, encodeResult, reduceCtorEq, exists_false]
    | completed trace =>
      constructor
      · intro _
        exact ⟨encodeTrace (x := inputAt base value) trace, by
          simp only [runOutputCodeAt, hr, encodeResult]
          rfl⟩
      · intro _
        exact ⟨trace, rfl⟩
  rw [hevent]
  exact measurableSet_runOutput_event base h {result | ∃ code, result = .inr code}

/-- Recorder equality reads only the current slice, the pre-feedback arm,
and the same original observation. -/
theorem recorderAtFixedArm_eq_of_same_current_control (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (arm : Fin p.K)
    (left right : RunDomain p) (hcontrol : left.1.2 base.time = right.1.2 base.time)
    (hobs : left.2 = right.2) :
    recorderAtFixedArm base h arm left = recorderAtFixedArm base h arm right := by
  apply CoordinatorRecordingMeasurability.run_eq_of_current_slice_eq
  · exact congrArg Prod.fst hcontrol
  · rfl
  · exact hobs

/-- Same CURRENT time control and same own observation give the same full
lossless code, with every other coordinate of the complete row unrestricted. -/
theorem runOutputCodeAt_eq_of_same_current_control (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (left right : RunDomain p)
    (hcontrol : left.1.2 base.time = right.1.2 base.time) (hobs : left.2 = right.2) :
    runOutputCodeAt base h left = runOutputCodeAt base h right := by
  rw [runOutputCodeAt_eq_assembled, runOutputCodeAt_eq_assembled]
  have harm : armChoiceAt base h left = armChoiceAt base h right :=
    CoordinatorLocalArmChoice.coordinatorArmChoice_eq_of_same_current_timeControl
      base.payload base.ledger.pending (some (localCutoff base.cutoffIndex)) base.time
      (Inputs.weights (x := base) h.ledger_valid h.assignment_eq) left.1 right.1 hcontrol
  unfold assembledCodeAt
  rw [harm]
  cases armChoiceAt base h right with
  | none => rfl
  | some arm =>
    change codeAfterArm base h arm left = codeAfterArm base h arm right
    unfold codeAfterArm
    rw [recorderAtFixedArm_eq_of_same_current_control base h arm left right hcontrol hobs]
    cases recorderAtFixedArm base h arm right with
    | none => rfl
    | some recorder =>
      change codeAfterRecorder base h arm recorder left = codeAfterRecorder base h arm recorder right
      unfold codeAfterRecorder
      cases InputsValid.ledgerStart base recorder with
      | invalid => rfl
      | rejected ledger => rfl
      | success ledger =>
        change receptionCode base h arm recorder ledger (receptionAtLedger base ledger left) =
          receptionCode base h arm recorder ledger (receptionAtLedger base ledger right)
        have hi : receptionAtLedger base ledger left = receptionAtLedger base ledger right := by
          change CoordinatorUpMeasurability.receptionInputAtControl (left.1.2 base.time)
            (ledger, (base.upDecoderBank, (base.time, left.2))) =
              CoordinatorUpMeasurability.receptionInputAtControl (right.1.2 base.time)
                (ledger, (base.upDecoderBank, (base.time, right.2)))
          rw [hcontrol, hobs]
        rw [hi]

/-- For two completed actual runs, equality of the code gives every non-row
runtime field via its lossless tuple view, and also the original recorder. -/
theorem completed_fields_eq_of_same_current_control (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (left right : RunDomain p)
    (hcontrol : left.1.2 base.time = right.1.2 base.time) (hobs : left.2 = right.2)
    (a : Trace (inputAt base left)) (b : Trace (inputAt base right))
    (ha : runAt base h left = .completed a) (hb : runAt base h right = .completed b) :
    completedCodeFields (x := base) (encodeTrace (x := inputAt base left) a) =
      completedCodeFields (x := base) (encodeTrace (x := inputAt base right) b) ∧
      a.recorder = b.recorder := by
  have hh := runOutputCodeAt_eq_of_same_current_control base h left right hcontrol hobs
  change encodeResult (runAt base h left) = encodeResult (runAt base h right) at hh
  rw [ha, hb] at hh
  have hc := Sum.inr.inj hh
  refine ⟨congrArg (completedCodeFields (x := base)) hc, ?_⟩
  have hr := congrArg (fun c : CompletedCode base =>
    CoordinatorRecordingMeasurability.decodeOutput c.recorderCode) hc
  simpa only [encodeTrace, CoordinatorRecordingMeasurability.decodeOutput_encodeOutput] using hr

/-- Lift any explicit partial statistic of the actual selected receiver input.
An absent earlier stage stays absent. Only the countable code is discrete. -/
def selectedReceptionStatisticAt {α : Type*} (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (statistic : InputReception base → Option α) (value : RunDomain p) : Option α :=
  (selectedReceptionInputAt base h value).bind statistic

theorem measurable_selectedReceptionStatisticAt {α : Type*} (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (statistic : InputReception base → Option α) :
    Measurable[_, ⊤] (selectedReceptionStatisticAt base h statistic) := by
  let : MeasurableSpace (Option α) := ⊤
  exact (Measurable.of_discrete (f := fun input : Option (InputReception base) =>
    input.bind statistic)).comp (measurable_selectedReceptionInputAt base h)

/-- The actual checked receiver retains invalid, rejected, and successful tags. -/
def selectedCheckedReceptionAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :=
  selectedReceptionStatisticAt base h (fun input => some (CoordinatorUpReception.receiveUp input))

theorem measurable_selectedCheckedReceptionAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable[_, ⊤] (selectedCheckedReceptionAt base h) :=
  measurable_selectedReceptionStatisticAt base h _

/-- Extract the actual updated ledger and WHOLE decoder bank from either
non-invalid reception, preserving ordinary rejection as successful continuation. -/
def receivedLedgerBank (base : Inputs p) (input : InputReception base) :
    Option (InputLedger base × CoordinatorUpReception.UpDecoderBank p) :=
  match CoordinatorUpReception.receiveUp input with
  | .invalid => none
  | .success result | .rejected result => some result

/-- Raw and parsed outputs are read only on the actual non-invalid receiver path. -/
def selectedDecoderOutputsAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :=
  selectedReceptionStatisticAt base h (fun input => (receivedLedgerBank base input).map
    (fun _ => ((CoordinatorUpReception.decoderTransition input).2,
      CoordinatorUpReception.parsedDecoderOutput input)))

theorem measurable_selectedDecoderOutputsAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable[_, ⊤] (selectedDecoderOutputsAt base h) :=
  measurable_selectedReceptionStatisticAt base h _

/-- The whole bank returned by the actual checked receive, including rejection. -/
def selectedDecoderBankAfterAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :=
  selectedReceptionStatisticAt base h (fun input => (receivedLedgerBank base input).map Prod.snd)

theorem measurable_selectedDecoderBankAfterAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable[_, ⊤] (selectedDecoderBankAfterAt base h) :=
  measurable_selectedReceptionStatisticAt base h _

/-- The actual ledger finish is evaluated only after non-invalid reception;
its invalid/rejected/successful tags remain literal. -/
def selectedLedgerFinishAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :=
  selectedReceptionStatisticAt base h (fun input => (receivedLedgerBank base input).map
    (fun result => CoordinatorCollectionLedger.finishRound result.1))

theorem measurable_selectedLedgerFinishAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable[_, ⊤] (selectedLedgerFinishAt base h) :=
  measurable_selectedReceptionStatisticAt base h _

/-- A successful ledger finish supplies the actual collection clock command.
`actualFinishRound_fixed` identifies it with the accepted clock at every row. -/
def selectedClockFinishAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :=
  selectedReceptionStatisticAt base h (fun input => (receivedLedgerBank base input).bind
    (fun result => match CoordinatorCollectionLedger.finishRound result.1 with
      | .success finished => some (finishedClock base finished)
      | .invalid | .rejected _ => none))

theorem measurable_selectedClockFinishAt (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) :
    Measurable[_, ⊤] (selectedClockFinishAt base h) :=
  measurable_selectedReceptionStatisticAt base h _

/-- All completed-code fields, separately or jointly, have measurable exact
option codes. This includes both clock results and all intermediate ledger codes. -/
def completedFieldAt {α : Type*} (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base)
    (field : CompletedCode base → α) (value : RunDomain p) : Option α :=
  match runOutputCodeAt base h value with
  | .inl _ => none
  | .inr code => some (field code)

theorem measurable_completedFieldAt {α : Type*} (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (field : CompletedCode base → α) :
    Measurable[_, ⊤] (completedFieldAt base h field) := by
  let : MeasurableSpace (Option α) := ⊤
  exact (Measurable.of_discrete (f := fun result : RunOutputCode base =>
    match result with
    | .inl _ => (none : Option α)
    | .inr code => some (field code))).comp (measurable_runOutputCodeAt base h)

/-- The selected input stage agrees with the input retained in every actual
completed trace; no externally supplied ledger or reception input is assumed. -/
theorem selectedReceptionInputAt_of_completed (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p)
    (trace : Trace (inputAt base value)) :
    selectedReceptionInputAt base h value = some trace.receptionInput := by
  have harm := trace.armChoice_eq
  rw [trace.clockStarted_frame.2.1] at harm
  change armChoiceAt base h value = some trace.arm at harm
  have hrec := trace.recorder_eq
  change recorderAtFixedArm base h trace.arm value = some trace.recorder at hrec
  have hstart := trace.ledgerStart_eq
  rw [trace.enabled_eq, trace.rawInput_eq] at hstart
  change InputsValid.ledgerStart base trace.recorder = .success trace.ledgerStarted at hstart
  unfold selectedReceptionInputAt recorderAtChoice
  simp only [harm]
  simp only [hrec, ledgerStartAfterRecorder]
  change CoordinatorCollectionLedger.startRound base.ledger
    (CoordinatorCollectionUpRoundStep.sourceRound base.time)
    (InputsValid.sourceLearningEnabled base) (InputsValid.rawInputOfRecorder trace.recorder) =
      .success trace.ledgerStarted at hstart
  rw [hstart]
  exact congrArg some trace.receptionInput_eq.symm

/-- The measurable selected stages are the actual retained stages of every
completed run, including the ordinary rejected-reception branch. -/
theorem selectedStages_of_completed (base : Inputs p)
    (h : CoordinatorCollectionUpRoundStep.InputsValid base) (value : RunDomain p)
    (trace : Trace (inputAt base value)) :
    selectedCheckedReceptionAt base h value = some trace.reception ∧
    selectedDecoderOutputsAt base h value = some
      ((CoordinatorUpReception.decoderTransition trace.receptionInput).2,
        CoordinatorUpReception.parsedDecoderOutput trace.receptionInput) ∧
    selectedDecoderBankAfterAt base h value = some trace.decoderBankAfter ∧
    selectedLedgerFinishAt base h value = some (.success trace.ledgerFinished) ∧
    selectedClockFinishAt base h value = some trace.clockFinished := by
  let input : InputReception base := trace.receptionInput
  let reception : CoordinatorCollectionLedger.Checked
      (InputLedger base × CoordinatorUpReception.UpDecoderBank p) := trace.reception
  let decoded : InputLedger base := trace.ledgerDecoded
  let bank : CoordinatorUpReception.UpDecoderBank p := trace.decoderBankAfter
  let finished : InputLedger base := trace.ledgerFinished
  let clock : FinishRoundResult p := trace.clockFinished
  change selectedCheckedReceptionAt base h value = some reception ∧
    selectedDecoderOutputsAt base h value = some
      ((CoordinatorUpReception.decoderTransition input).2,
        CoordinatorUpReception.parsedDecoderOutput input) ∧
    selectedDecoderBankAfterAt base h value = some bank ∧
    selectedLedgerFinishAt base h value = some (.success finished) ∧
    selectedClockFinishAt base h value = some clock
  have hi : selectedReceptionInputAt base h value = some input :=
    selectedReceptionInputAt_of_completed base h value trace
  have heq : input = receptionAtLedger base trace.ledgerStarted value := trace.receptionInput_eq
  have hr : CoordinatorUpReception.receiveUp input = reception := by
    rw [heq]
    exact trace.reception_eq
  have hout : reception = .success (decoded, bank) ∨
      reception = .rejected (decoded, bank) := trace.reception_outcome
  have hb : receivedLedgerBank base input = some (decoded, bank) := by
    unfold receivedLedgerBank
    rw [hr]
    rcases hout with hs | hs
    · rw [hs]
    · rw [hs]
  have hf : CoordinatorCollectionLedger.finishRound decoded = .success finished := trace.ledgerFinish_eq
  have hc : finishedClock base finished = clock := by
    have ht := trace.clockFinish_eq
    rw [trace.clockStarted_frame.1] at ht
    have ht' : CoordinatorPhaseClock.finishRound p base.etaReal base.time base.clock
        finished.pending value.1 = .ok clock := ht
    exact Except.ok.inj ((actualFinishRound_fixed base h finished value.1).symm.trans ht')
  simp only [selectedCheckedReceptionAt, selectedDecoderOutputsAt, selectedDecoderBankAfterAt,
    selectedLedgerFinishAt, selectedClockFinishAt, selectedReceptionStatisticAt, hi,
    Option.bind_some, Option.map_some, hr, hb, hf, hc, true_and]

end Bandits.Support.CoordinatorCollectionRunMeasurabilityRepair

end
