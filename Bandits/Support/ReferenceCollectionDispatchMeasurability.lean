/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceActivePhysicalStepMeasurability

/-!
# Collection pre-choice coordinates of the canonical physical dispatcher

Sources: `sources/zip4/manuscript/06_interruptions.tex:235-296` and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-60`.

The input products below are transient views of the existing canonical
collection coordinates. The original payload, moving ledger, saved proposal,
sole UP bank, whole continuous row and time all vary. No validity, truthful
message, score bound, reachability or sampling-law hypothesis is imposed.
This module concerns internal deterministic mathematics, not manuscript closure.

Sole direct project dependency: ReferenceActivePhysicalStepMeasurability,
SHA-256 11b431bc05c6971b331016537f4e67f457e80a9c45d76940874cb30d37c6b314,
independent review-0347 PASS and turn-00119 dependency admission.
-/

@[expose] public section

noncomputable section

namespace Bandits.Support.ReferenceCollectionDispatchMeasurability

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceActivePhysicalStepMeasurability

variable {p : Parameters} {rate : RateInput p}

local instance cutoffMeasurableSpace :
    MeasurableSpace (Option (CoordinatorLocalArmChoice.Cutoff p)) := ⊤

/-- Countable original collection fields, with a separate local cutoff index.
The physical boundary checks the ledger cutoff before constructing this index. -/
abbrev DiscreteInput (p : Parameters) (rate : RateInput p) :=
  Ledger rate × (Option (Fin p.T × Bool) ×
    (CoordinatorUpReception.UpDecoderBank p × (Fin p.T × Fin p.T)))

/-- A local product, not a new state: original payload and complete continuous
row, paired with the original countable ledger/clock/bank coordinates. -/
abbrev LocalInput (p : Parameters) (rate : RateInput p) :=
  (Payload rate × CompletePublicTable.CompleteRow p) × DiscreteInput p rate

/-- Literal assembly of the actual collection input. Scores are read from the
moving ledger; the clock uses the old payload start and the saved proposal. -/
def assemble (z : LocalInput p rate) : CoordinatorRoundDispatch.CollectionInput p := {
  etaReal := rate.eta.val
  etaPositive := rate.eta.property
  n := rate.n
  n_cast_identity := rate.n_scale
  payload := z.1.1
  baseScores := z.2.1.baseScore
  ledger := z.2.1
  clock := collectionClock z.1.1 z.2.1 z.2.2.1 z.2.2.2.2.2
  upDecoderBank := z.2.2.2.1
  cutoffIndex := z.2.2.2.2.2
  time := z.2.2.2.2.1
  row := z.1.2 }

theorem assemble_eq_collectionInput (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (proposal : Option (Fin p.T × Bool)) (cutoff : Fin p.T) :
    assemble ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff) =
      collectionInput x payload ledger (collectionClock payload ledger proposal cutoff) cutoff := rfl

theorem measurable_payloadObservation :
    Measurable (LaterAssignmentStartMeasurability.payloadObservation
      (p := p) (eta := rate.eta)) := comap_measurable _

theorem measurable_payloadSigma : Measurable (fun s : Payload rate => s.sigma) :=
  measurable_fst.comp (measurable_snd.comp measurable_payloadObservation)

theorem measurable_payloadSlowSet : Measurable (fun s : Payload rate => s.slowSet) := by
  have h : Measurable (fun s : Payload rate => s.slowSet.val) :=
    measurable_fst.comp (measurable_snd.comp
      (measurable_snd.comp measurable_payloadObservation))
  exact h.subtype_mk

/-- The source-domain/core guard depends on countable fields only. The real
anchor is not discretized: it is absent because this particular guard does
not read it. -/
abbrev CoreKey (p : Parameters) (rate : RateInput p) :=
  (Fin p.T × CanonicalOrientedSetLaw.SlowSet p.K p.m) × DiscreteInput p rate

def coreKey (z : LocalInput p rate) : CoreKey p rate :=
  ((z.1.1.sigma, z.1.1.slowSet), z.2)

theorem measurable_coreKey : Measurable (coreKey (p := p) (rate := rate)) :=
  ((measurable_payloadSigma.prodMk measurable_payloadSlowSet).comp
    (measurable_fst.comp measurable_fst)).prodMk measurable_snd

/-- Expanded, literal core checks on countable coordinates. No successful
execution property is included. -/
def coreChecks (k : CoreKey p rate) : Prop :=
  let ledger := k.2.1
  let clock : CoordinatorPhaseClock.ClockRegisters p :=
    ⟨some k.1.1, some k.2.2.2.2.2, ledger.freezeAt, k.2.2.1⟩
  CoordinatorCollectionLedger.validLedger ledger ∧
  ledger.phase = .ready ∧
  (∀ i, ledger.assignment.arm i =
    CanonicalAssignmentVector.followerArm p.two_le_m k.1.2 i) ∧
  CoordinatorPhaseClock.proposalParameterValid p rate.eta.val ∧
  CoordinatorPhaseClock.clockRegistersValid p rate.eta.val clock ∧
  CoordinatorPhaseClock.startRoundTimeValid p k.2.2.2.2.1 clock ∧
  ledger.sigma = k.1.1.val + 1 ∧
  ledger.cutoff = k.2.2.2.2.2.val + 1 ∧
  ledger.cursor = k.2.2.2.2.1.val + 1 ∧
  CoordinatorUpReception.decoderBankCheck p k.2.2.2.1 = true

theorem coreChecks_iff (z : LocalInput p rate) :
    coreChecks (coreKey z) ↔ CoordinatorRoundDispatch.CollectionCoreValid (assemble z) := by
  constructor
  · rintro ⟨hv, hr, ha, hp, hc, ht, hs, hu, hcursor, hb⟩
    exact {
      payload_n_eq := payload_n_eq z.1.1
      ledger_valid := hv, ledger_ready := hr, assignment_eq := ha
      base_score_eq := rfl, clock_parameter_valid := hp
      clock_registers_valid := hc, clock_start_time_valid := ht
      clock_sigma_eq := rfl, clock_cutoff_eq := rfl
      ledger_sigma_eq := hs, ledger_cutoff_eq := hu
      ledger_freeze_eq := rfl, ledger_cursor_eq := hcursor
      decoder_bank_valid := hb }
  · intro h
    exact ⟨h.ledger_valid, h.ledger_ready, h.assignment_eq,
      h.clock_parameter_valid, h.clock_registers_valid, h.clock_start_time_valid,
      h.ledger_sigma_eq, h.ledger_cutoff_eq, h.ledger_cursor_eq, h.decoder_bank_valid⟩

theorem measurableSet_coreChecks : MeasurableSet
    {z : LocalInput p rate | CoordinatorRoundDispatch.CollectionCoreValid (assemble z)} := by
  have h : MeasurableSet {k : CoreKey p rate | coreChecks k} := Set.to_countable _ |>.measurableSet
  have heq : {z : LocalInput p rate | CoordinatorRoundDispatch.CollectionCoreValid (assemble z)} =
      coreKey ⁻¹' {k | coreChecks k} := by
    ext z
    exact (coreChecks_iff z).symm
  rw [heq]
  exact h.preimage measurable_coreKey

/-- This guard is the actual finite cutoff-score-plus-increment check,
including missing complement registers. It is not supplied by the caller. -/
def currentScoresCheck (k : CoreKey p rate) : Bool :=
  CoordinatorCollectionLedger.allFin p.K fun a =>
    if a ∈ k.1.2.val then true else
      match k.2.1.cutoffRegisters a with
      | none => false
      | some cutoff => decide (cutoff.score + k.2.1.increment a ≤ p.T * D p)

theorem currentScoresCheck_eq (z : LocalInput p rate) :
    currentScoresCheck (coreKey z) =
      CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z) := rfl

theorem measurable_currentScoresCheck : Measurable
    (fun z : LocalInput p rate =>
      CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z)) :=
  (measurable_of_countable currentScoresCheck).comp measurable_coreKey

theorem measurableSet_currentScoresCheck : MeasurableSet
    {z : LocalInput p rate |
      CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z) = true} :=
  measurable_currentScoresCheck (measurableSet_singleton true)

/-- The clock result retains its actual failure or complete start result,
including the instruction. Both carriers have countable literal coordinates. -/
local instance startResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance startResultDiscrete :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⟨fun _ => trivial⟩
local instance clockFailureMeasurableSpace :
    MeasurableSpace CoordinatorPhaseClock.ClockFailure := ⊤
local instance clockFailureDiscrete :
    DiscreteMeasurableSpace CoordinatorPhaseClock.ClockFailure := ⟨fun _ => trivial⟩

abbrev ClockObservation (p : Parameters) :=
  CoordinatorPhaseClock.ClockFailure ⊕ CoordinatorPhaseClock.StartRoundResult p

local instance clockObservationMeasurableSpace : MeasurableSpace (ClockObservation p) := ⊤

def clockObservation (z : LocalInput p rate) : ClockObservation p :=
  match CoordinatorPhaseClock.startRound p rate.eta.val (assemble z).time
      (assemble z).clock (assemble z).ledger.pending with
  | .error reason => .inl reason
  | .ok started => .inr started

theorem measurable_clockObservation : Measurable
    (clockObservation (p := p) (rate := rate)) := by
  let f : CoreKey p rate → ClockObservation p := fun k =>
    match CoordinatorPhaseClock.startRound p rate.eta.val k.2.2.2.2.1
        ⟨some k.1.1, some k.2.2.2.2.2, k.2.1.freezeAt, k.2.2.1⟩ k.2.1.pending with
    | .error reason => .inl reason
    | .ok started => .inr started
  exact (measurable_of_countable f).comp measurable_coreKey

/-- The checked core is a measurable branch of the unrestricted local product,
not a standing hypothesis on physical input. -/
abbrev CoreInput (p : Parameters) (rate : RateInput p) :=
  {z : LocalInput p rate // CoordinatorRoundDispatch.CollectionCoreValid (assemble z)}

/-- Derive all later-start consistency fields from the actual core checks.
In particular the old freeze boundary is the ledger's boundary. -/
def localConsistency (z : CoreInput p rate) :
    LaterAssignmentStartOperation.LocalConsistency (assemble z.val).payload
      (CoordinatorRoundDispatch.collectionOperationLedger (assemble z.val) z.property.payload_n_eq) := {
  oldStart_eq := z.property.ledger_sigma_eq.symm
  oldAssignment_eq := fun i => (z.property.assignment_eq i).symm
  oldFreezeAt := z.val.2.1.freezeAt
  oldFreezeAt_eq := rfl }

local instance instructionMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⊤
local instance instructionDiscrete :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.AssignmentStartInstruction p) := ⟨fun _ => trivial⟩

/-- The existing varying-input later-start carrier, assembled from a checked
branch and its instruction. No local consistency field is supplied externally. -/
def laterInput (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :
    LaterAssignmentFullOutputMeasurability.JointLocalStartInput p rate.eta :=
  ⟨z.val.1.1,
    CoordinatorRoundDispatch.collectionOperationLedger (assemble z.val) z.property.payload_n_eq,
    instruction, localConsistency z⟩

/-- Only entirely discrete fields are copied into the accepted local-input
code. The payload itself keeps its original continuous measurable space. -/
def laterLocalCode (ledger : Ledger rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :
    LaterAssignmentAnchorMeasurability.LocalStartObservableCode p :=
  ((ledger.assignment, ledger.sigma, ledger.cutoff, ledger.freezeAt,
    ledger.baseScore, ledger.pending, ledger.cutoffRegisters,
    ledger.currentRegisters, ledger.increment, ledger.gammaLoc,
    ledger.rawBuffer, ledger.enabledHistory, ledger.cursor, ledger.phase),
    LaterAssignmentStartMeasurability.instructionCode instruction, ledger.freezeAt)

theorem laterInput_observation (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :
    LaterAssignmentAnchorMeasurability.jointLocalStartObservation (laterInput z instruction) =
      (LaterAssignmentStartMeasurability.payloadObservation z.val.1.1,
        laterLocalCode z.val.2.1 instruction) := rfl

theorem measurable_laterInput : Measurable
    (fun z : CoreInput p rate × CoordinatorPhaseClock.AssignmentStartInstruction p =>
      laterInput z.1 z.2) := by
  apply measurable_comap_iff.mpr
  have hpayload : Measurable (fun z : CoreInput p rate ×
      CoordinatorPhaseClock.AssignmentStartInstruction p =>
      LaterAssignmentStartMeasurability.payloadObservation z.1.val.1.1) :=
    measurable_payloadObservation.comp
      (measurable_fst.comp (measurable_fst.comp
        (measurable_subtype_coe.comp measurable_fst)))
  have hledger : Measurable (fun z : CoreInput p rate ×
      CoordinatorPhaseClock.AssignmentStartInstruction p => z.1.val.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst))
  exact hpayload.prodMk ((measurable_of_countable
    (fun z : Ledger rate × CoordinatorPhaseClock.AssignmentStartInstruction p =>
      laterLocalCode z.1 z.2)).comp (hledger.prodMk measurable_snd))

/-- Full accepted later output on varying original payload, moving ledger,
whole row and instruction. This retains its law parameters, payload, base
scores, full K+1 assignment vector and derived continuous fields. -/
def laterObservation (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :
    LaterAssignmentFullOutputMeasurability.FullOutputObservation p :=
  LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
    (laterInput z instruction, z.val.1.2)

theorem measurable_laterObservation : Measurable
    (fun z : CoreInput p rate × CoordinatorPhaseClock.AssignmentStartInstruction p =>
      laterObservation z.1 z.2) :=
  LaterAssignmentFullOutputMeasurability.measurable_laterAssignmentFullOutputObservation_comp
    (fun z : CoreInput p rate × CoordinatorPhaseClock.AssignmentStartInstruction p =>
      laterInput z.1 z.2) (fun z => z.1.val.1.2)
    measurable_laterInput
    (measurable_snd.comp (measurable_fst.comp
      (measurable_subtype_coe.comp measurable_fst)))

/-- Exact accepted decoder: this reconstructs the original result, including
all reconstruction/prefix/orientation failures and the actual successful
payload, reconstruction, assignment vector and base scores. -/
theorem laterObservation_decode (z : CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :
    LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
      z.val.1.1 (laterInput z instruction).2.1 instruction z.val.1.2
      (localConsistency z) (laterObservation z instruction).1 =
      some (LaterAssignmentStartOperation.laterAssignmentStart
        z.val.1.1 (laterInput z instruction).2.1 instruction z.val.1.2
        (localConsistency z)) :=
  LaterAssignmentFullOutputMeasurability.fullOutput_code_decodes_exactly
    (laterInput z instruction, z.val.1.2)

theorem measurable_laterObservation_comp {X : Type*} [MeasurableSpace X]
    (input : X → CoreInput p rate)
    (instruction : X → CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hinput : Measurable input) (hinstruction : Measurable instruction) :
    Measurable (fun x => laterObservation (input x) (instruction x)) :=
  measurable_laterObservation.comp (hinput.prodMk hinstruction)

/-- The original actual score observation is optional on every arm, so an
unknown register remains visibly unknown on the unrestricted input. -/
def ledgerCurrentScores (ledger : Ledger rate) (a : Fin p.K) : Option ℕ :=
  (ledger.cutoffRegisters a).map (fun cutoff => cutoff.score + ledger.increment a)

theorem measurable_ledgerCurrentScores : Measurable
    (fun z : LocalInput p rate => ledgerCurrentScores z.2.1) :=
  (measurable_of_countable ledgerCurrentScores).comp (measurable_fst.comp measurable_snd)

theorem ledgerCurrentScores_eq_actual (z : CoreInput p rate)
    (a : Fin p.K) (ha : a ∉ z.val.1.1.slowSet.val) :
    ledgerCurrentScores z.val.2.1 a = some
      (CoordinatorCollectionUpRoundStep.complementCurrentScore (assemble z.val).ledger
        (assemble z.val).payload z.property.ledger_valid z.property.assignment_eq a ha) := by
  obtain ⟨cutoff, hcutoff, _⟩ :=
    CoordinatorCollectionUpRoundStep.complementRegisters_known (assemble z.val).ledger
      (assemble z.val).payload z.property.ledger_valid z.property.assignment_eq a ha
  rw [CoordinatorRoundDispatch.collection_complementCurrentScore_eq
    (assemble z.val) z.property a ha cutoff hcutoff]
  change z.val.2.1.cutoffRegisters a = some cutoff at hcutoff
  change (z.val.2.1.cutoffRegisters a).map _ = _
  rw [hcutoff]
  rfl

/-- A zero extension used only for the Borel proof. On a checked complement
its option is proved present below; it is never a replacement runtime score. -/
def extendedLedgerWeight (k : CoreKey p rate) (a : Fin p.K) : ℝ :=
  if a ∈ k.1.2.val then 0 else
    match ledgerCurrentScores k.2.1 a with
    | none => 0
    | some score => ScoreWeights.scoreWeight
        (AssignmentScoreReconstruction.sourceWeightBase p) score

/-- The actual continuing view retains the OLD payload and the genuine
ledger-derived weights. No renewed anchor or installed live state appears. -/
def continuingView (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    ReferenceDownReception.ChoiceTimeView p rate.eta := {
  payload := z.val.1.1
  pendingAtChoice := started.pending
  cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
  complementWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights
    (assemble z.val) z.property.ledger_valid z.property.assignment_eq }

theorem continuingView_weights (z : CoreInput p rate)
    (started : CoordinatorPhaseClock.StartRoundResult p) :
    ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
      (continuingView z started) = extendedLedgerWeight (coreKey z.val) := by
  classical
  funext a
  by_cases ha : a ∈ CanonicalFastSampling.fastArmFinset z.val.1.1.slowSet
  · have hnot := (Finset.mem_sdiff.mp ha).2
    have hscore := ledgerCurrentScores_eq_actual z a hnot
    unfold ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
    change (if h : a ∈ CanonicalFastSampling.fastArmFinset z.val.1.1.slowSet then
      (continuingView z started).complementWeights ⟨a, h⟩ else 0) = _
    rw [dite_eq_left ha]
    change _ = (if a ∈ z.val.1.1.slowSet.val then 0 else
      match ledgerCurrentScores z.val.2.1 a with
      | none => 0
      | some score => ScoreWeights.scoreWeight
        (AssignmentScoreReconstruction.sourceWeightBase p) score)
    rw [ite_eq_right hnot, hscore]
    rfl
  · have hslow : a ∈ z.val.1.1.slowSet.val := by
      simpa [CanonicalFastSampling.fastArmFinset] using ha
    unfold ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector
    change (if h : a ∈ CanonicalFastSampling.fastArmFinset z.val.1.1.slowSet then
      (continuingView z started).complementWeights ⟨a, h⟩ else 0) = _
    rw [dite_eq_right ha]
    change 0 = (if a ∈ z.val.1.1.slowSet.val then 0 else _)
    rw [ite_eq_left hslow]

theorem measurable_continuingView : Measurable
    (fun z : CoreInput p rate × CoordinatorPhaseClock.StartRoundResult p =>
      continuingView z.1 z.2) := by
  apply measurable_comap_iff.mpr
  have hp : Measurable (fun z : CoreInput p rate × CoordinatorPhaseClock.StartRoundResult p =>
      z.1.val.1.1) := measurable_fst.comp (measurable_fst.comp
        (measurable_subtype_coe.comp measurable_fst))
  have hpend : Measurable (fun z : CoreInput p rate × CoordinatorPhaseClock.StartRoundResult p =>
      z.2.pending) := (measurable_of_countable _).comp measurable_snd
  have hcut : Measurable (fun z : CoreInput p rate × CoordinatorPhaseClock.StartRoundResult p =>
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p z.2.clock.u) :=
    (measurable_of_countable (fun started : CoordinatorPhaseClock.StartRoundResult p =>
      CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u)).comp measurable_snd
  have hw : Measurable (fun z : CoreInput p rate × CoordinatorPhaseClock.StartRoundResult p =>
      ReferenceDownReceptionMeasurability.choiceTimeViewWeightVector (continuingView z.1 z.2)) := by
    simp_rw [continuingView_weights]
    exact (measurable_of_countable extendedLedgerWeight).comp
      (measurable_coreKey.comp (measurable_subtype_coe.comp measurable_fst))
  exact hp.prodMk (hpend.prodMk (hcut.prodMk hw))

/-- The actual choice-domain guard is Borel on the checked core branch,
including its continuous anchor inequalities. -/
theorem measurable_continuingChoiceCheck : Measurable
    (fun z : CoreInput p rate × CoordinatorPhaseClock.StartRoundResult p =>
      ReferenceDownReceptionMeasurability.choiceInputsValidBit
        (continuingView z.1 z.2) z.1.val.2.2.2.2.1) :=
  ReferenceDownReceptionMeasurability.measurable_choiceInputsValid.comp
    (measurable_continuingView.prodMk
      ((measurable_of_countable (fun d : DiscreteInput p rate => d.2.2.2.1)).comp
        (measurable_snd.comp (measurable_subtype_coe.comp measurable_fst))))

/-- Joint finite-index evaluation, with the array retaining its original
product measurable space. -/
theorem measurable_eval_fin {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} (f : X → Fin n → Y) (i : X → Fin n)
    (hf : Measurable f) (hi : Measurable i) : Measurable (fun x => f x (i x)) := by
  have h : Measurable (fun z : (Fin n → Y) × Fin n => z.1 z.2) :=
    measurable_from_prod_countable_left fun j => measurable_pi_apply j
  exact h.comp (hf.prodMk hi)

/-- All successful collection choices have nonempty pending sets, including
a new later assignment. This local branch carrier therefore excludes the
live-and-empty fast draw without assuming anything about the continuous row. -/
local instance wordMeasurableSpace :
    MeasurableSpace (AffineChannelLaw.Word (AffineBatchDecoder.width p)) := MeasurableSpace.pi

local instance wordOptionMeasurableSpace :
    MeasurableSpace (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) :=
  @LaterAssignmentStartMeasurability.optionMeasurableSpace
    (AffineChannelLaw.Word (AffineBatchDecoder.width p)) (wordMeasurableSpace (p := p))

local instance wordOptionDiscrete :
    DiscreteMeasurableSpace (Option (AffineChannelLaw.Word (AffineBatchDecoder.width p))) := by
  constructor
  intro s
  let e := Equiv.optionEquivSumPUnit (AffineChannelLaw.Word (AffineBatchDecoder.width p))
  exact ⟨e '' s, measurableSet_sum_iff.mpr
    ⟨MeasurableSet.of_discrete, MeasurableSet.of_discrete⟩, e.injective.preimage_image s⟩

abbrev PendingChoiceInput (p : Parameters) (rate : RateInput p) :=
  {z : ReferenceDownReception.ChoiceTimeView p rate.eta ×
      (CompletePublicTable.CompleteRow p × Fin p.T) // z.1.pendingAtChoice.Nonempty}

/-- The actual coordinator choice is jointly Borel on a nonempty-pending
branch. The proof consumes the accepted full DOWN word observation on that
same view, row and time. No truthful-sender or arm equation is an input. -/
theorem measurable_pendingArmChoice : Measurable
    (fun z : PendingChoiceInput p rate =>
      CoordinatorLocalArmChoice.coordinatorArmChoice z.val.1.payload
        z.val.1.pendingAtChoice z.val.1.cutoff z.val.2.2
        z.val.1.complementWeights z.val.2.1) := by
  classical
  let row : PendingChoiceInput p rate → CompletePublicTable.CompleteRow p := fun z => z.val.2.1
  let time : PendingChoiceInput p rate → Fin p.T := fun z => z.val.2.2
  let view : PendingChoiceInput p rate → ReferenceDownReception.ChoiceTimeView p rate.eta :=
    fun z => z.val.1
  have hr : Measurable row := measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
  have ht : Measurable time := measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)
  have hv : Measurable view := measurable_fst.comp measurable_subtype_coe
  have hs : Measurable (fun z => (row z).2 (time z)) :=
    measurable_eval_fin _ time (measurable_snd.comp hr) ht
  have hvalid : Measurable (fun z =>
      ReferenceDownReceptionMeasurability.choiceInputsValidBit (view z) (time z)) :=
    ReferenceDownReceptionMeasurability.measurable_choiceInputsValid.comp (hv.prodMk ht)
  have hwords : Measurable (fun z => fun i : Fin (p.m - 1) =>
      ReferenceDownReception.expectedDownFlatWord (some (view z)) i (row z) (time z)) := by
    apply Measurable.of_eval
    intro i
    exact (ReferenceDownReceptionMeasurability.measurable_expectedDownFlatWord i).comp
      ((LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable view hv).prodMk
        (hr.prodMk ht))
  let key := fun z : PendingChoiceInput p rate =>
    (ReferenceDownReceptionMeasurability.choiceInputsValidBit (view z) (time z),
      PublicDiscreteDraws.slotDraw ((row z).2 (time z)).1,
      PublicDiscreteDraws.pilotDraw (K_pos p) (ActiveRoundActions.coordinator p.two_le_m)
        ((row z).2 (time z)).1,
      (OrderedTupleSampler.sample p.two_le_m p.m_lt_K ((row z).2 (time z)).1).val,
      PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K ((row z).2 (time z)).1,
      ((row z).2 (time z)).2,
      fun i => ReferenceDownReception.expectedDownFlatWord (some (view z)) i (row z) (time z))
  have hk : Measurable key :=
    hvalid.prodMk ((PublicDiscreteDraws.measurable_slotDraw.comp (measurable_fst.comp hs)).prodMk
      ((PublicDiscreteDraws.measurable_pilotDraw (K_pos p)
        (ActiveRoundActions.coordinator p.two_le_m) |>.comp (measurable_fst.comp hs)).prodMk
      ((measurable_subtype_coe.comp ((OrderedTupleSampler.measurable_sample
        p.two_le_m p.m_lt_K).comp (measurable_fst.comp hs))).prodMk
      ((PublicDiscreteDraws.measurable_selectedFollowerDraw p.two_le_m p.m_lt_K |>.comp
        (measurable_fst.comp hs)).prodMk ((measurable_snd.comp hs).prodMk hwords)))))
  let evaluate := fun k : Bool × (PublicDiscreteDraws.Slot × (Fin p.K ×
      ((Fin p.m → Fin p.K) × (Fin (p.m - 1) ×
      (ContinuousLearningRows.AffineSamples p ×
        (Fin (p.m - 1) → Option (AffineChannelLaw.Word (AffineBatchDecoder.width p)))))))) =>
    if k.1 then
      if k.2.1 = PublicDiscreteDraws.dataSlot then some k.2.2.1
      else if k.2.1 = PublicDiscreteDraws.downSlot then
        match k.2.2.2.2.2.2 k.2.2.2.2.1 with
        | some word => some (ActiveRoundActions.sendArm
            (AffineChannelLaw.affineHash
              (k.2.2.2.2.2.1 (CoordinatorLocalArmChoice.downChannel k.2.2.2.2.1)) word)
            (k.2.2.2.1 (ActiveRoundActions.coordinator p.two_le_m))
            (k.2.2.2.1 (PublicDiscreteDraws.followerPlayer p.two_le_m k.2.2.2.2.1)))
        | none => some (k.2.2.2.1 (ActiveRoundActions.coordinator p.two_le_m))
      else some (k.2.2.2.1 (ActiveRoundActions.coordinator p.two_le_m))
    else none
  have heq (z : PendingChoiceInput p rate) :
      CoordinatorLocalArmChoice.coordinatorArmChoice (view z).payload
        (view z).pendingAtChoice (view z).cutoff (time z)
        (view z).complementWeights (row z) = evaluate (key z) := by
    have hnotfast : ¬ (CoordinatorLocalArmChoice.assignmentIsLive (view z).payload
        (view z).cutoff (time z) ∧ (view z).pendingAtChoice = ∅) :=
      fun h => z.property.ne_empty h.2
    by_cases hvalid : CoordinatorLocalArmChoice.ChoiceInputsValid (view z).payload
        (view z).cutoff (time z) (view z).complementWeights
    · have hnonempty := CoordinatorLiveChoiceRecorderStep.coordinatorArmChoice_ne_none
        (view z).payload (view z).pendingAtChoice (view z).cutoff (time z)
        (view z).complementWeights (row z) hvalid
      by_cases hdata : PublicDiscreteDraws.slotDraw ((row z).2 (time z)).1 =
          PublicDiscreteDraws.dataSlot
      · simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
          CoordinatorLocalArmChoice.coordinatorArmChoiceCore, dite_eq_left hvalid,
          ite_eq_right hnotfast, ite_eq_left hdata, evaluate, key,
          ReferenceDownReceptionMeasurability.choiceInputsValidBit,
          decide_eq_true hvalid, ite_true]
      · by_cases hdown : PublicDiscreteDraws.slotDraw ((row z).2 (time z)).1 =
            PublicDiscreteDraws.downSlot
        · by_cases hpending : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
              ((row z).2 (time z)).1 ∈ (view z).pendingAtChoice
          · have hword := (ReferenceDownReception.expectedDownFlatWord_eq_some_iff
              (view z) (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                ((row z).2 (time z)).1) (row z) (time z)).mpr
                ⟨hnonempty, hdown, rfl, hpending⟩
            simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
              CoordinatorLocalArmChoice.coordinatorArmChoiceCore, dite_eq_left hvalid,
              ite_eq_right hnotfast, hdown, hpending,
              and_self, ite_true, PublicDiscreteDraws.downSlot, PublicDiscreteDraws.dataSlot,
              evaluate, key,
              ReferenceDownReceptionMeasurability.choiceInputsValidBit,
              decide_eq_true hvalid, hword]
            rfl
          · have hword : ReferenceDownReception.expectedDownFlatWord (some (view z))
                (PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                  ((row z).2 (time z)).1) (row z) (time z) = none := by
              change (if _ then some _ else none) = none
              apply ite_eq_right
              intro h
              exact hpending h.2.2.2
            simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
              CoordinatorLocalArmChoice.coordinatorArmChoiceCore, dite_eq_left hvalid,
              ite_eq_right hnotfast, hdown, hpending,
              and_false, ite_false, PublicDiscreteDraws.downSlot, PublicDiscreteDraws.dataSlot,
              evaluate, key,
              ReferenceDownReceptionMeasurability.choiceInputsValidBit,
              decide_eq_true hvalid, ite_true, hword]
        · simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
            CoordinatorLocalArmChoice.coordinatorArmChoiceCore, dite_eq_left hvalid,
            ite_eq_right hnotfast, ite_eq_right hdata, hdown, false_and, ite_false,
            evaluate, key, ReferenceDownReceptionMeasurability.choiceInputsValidBit,
            decide_eq_true hvalid, ite_true]
    · simp only [CoordinatorLocalArmChoice.coordinatorArmChoice,
        CoordinatorLocalArmChoice.coordinatorArmChoiceCore, dite_eq_right hvalid,
        evaluate, key, ReferenceDownReceptionMeasurability.choiceInputsValidBit,
        decide_eq_false hvalid, Bool.false_eq_true, ite_false]
  change Measurable (fun z : PendingChoiceInput p rate =>
    CoordinatorLocalArmChoice.coordinatorArmChoice (view z).payload
      (view z).pendingAtChoice (view z).cutoff (time z)
      (view z).complementWeights (row z))
  simp_rw [heq]
  exact (measurable_of_countable evaluate).comp hk

local instance instructionOptionMeasurableSpace :
    MeasurableSpace (Option (CoordinatorPhaseClock.AssignmentStartInstruction p)) := ⊤

/-- The actual instruction can be consumed only on the empty-pending branch.
Clock errors and a missing instruction stay explicitly absent. -/
def requestedInstructionAt (z : LocalInput p rate) (clock : ClockObservation p) :
    Option (CoordinatorPhaseClock.AssignmentStartInstruction p) := by
  classical
  exact if z.2.1.pending.Nonempty then none else
    match clock with
    | .inl _ => none
    | .inr started => started.assignmentStart

def requestedInstruction (z : LocalInput p rate) :
    Option (CoordinatorPhaseClock.AssignmentStartInstruction p) :=
  requestedInstructionAt z (clockObservation z)

theorem measurable_requestedInstruction :
    Measurable (requestedInstruction (p := p) (rate := rate)) := by
  classical
  let f : Ledger rate × ClockObservation p →
      Option (CoordinatorPhaseClock.AssignmentStartInstruction p) := fun z =>
    if z.1.pending.Nonempty then none else
      match z.2 with
      | .inl _ => none
      | .inr started => started.assignmentStart
  exact (measurable_of_countable f).comp
    ((measurable_fst.comp measurable_snd).prodMk measurable_clockObservation)

/-- Optional full later output, without evaluating the later operation on a
missing instruction. -/
def laterObservationForInstruction (z : CoreInput p rate) :
    Option (CoordinatorPhaseClock.AssignmentStartInstruction p) →
      Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
  | none => none
  | some instruction => some (laterObservation z instruction)

theorem measurable_laterObservationForInstruction : Measurable
    (fun z : CoreInput p rate ×
      Option (CoordinatorPhaseClock.AssignmentStartInstruction p) =>
      laterObservationForInstruction z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro instruction
  cases instruction with
  | none => exact measurable_const
  | some instruction =>
      exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
        (measurable_laterObservation_comp id (fun _ => instruction)
          measurable_id measurable_const)

/-- Actual checked entry to the accepted full later-start observation, on the
WHOLE local input product. The core is a tested measurable branch, not a
hypothesis on the input. -/
def laterObservationAtClock (z : LocalInput p rate) (clock : ClockObservation p) :
    Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) := by
  classical
  exact if hcore : CoordinatorRoundDispatch.CollectionCoreValid (assemble z) then
    laterObservationForInstruction ⟨z, hcore⟩ (requestedInstructionAt z clock)
  else none

def laterObservation? (z : LocalInput p rate) :
    Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) :=
  laterObservationAtClock z (clockObservation z)

theorem measurable_laterObservation? :
    Measurable (laterObservation? (p := p) (rate := rate)) := by
  classical
  exact Measurable.dite
    (measurable_laterObservationForInstruction.comp
      (measurable_id.prodMk
        (measurable_requestedInstruction.comp measurable_subtype_coe)))
    measurable_const measurableSet_coreChecks

/-- A branch equation exposes the original instruction and full observation;
it supplies no global validity or local-consistency premise. -/
theorem laterObservation?_of_instruction (z : LocalInput p rate)
    (core : CoordinatorRoundDispatch.CollectionCoreValid (assemble z))
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hrequest : requestedInstruction z = some instruction) :
    laterObservation? z = some (laterObservation ⟨z, core⟩ instruction) := by
  classical
  change requestedInstructionAt z (clockObservation z) = some instruction at hrequest
  simp only [laterObservation?, laterObservationAtClock, dite_eq_left core, hrequest,
    laterObservationForInstruction]

/-- The guard diagnostics are observations of the actual tests. These fields
are useful before assembling the remaining output/installation observation. -/
def coreCheck (z : LocalInput p rate) : Bool := by
  classical
  exact if CoordinatorRoundDispatch.CollectionCoreValid (assemble z) then true else false

theorem measurable_coreCheck : Measurable (coreCheck (p := p) (rate := rate)) := by
  classical
  exact Measurable.ite measurableSet_coreChecks measurable_const measurable_const

abbrev PrechoiceDiagnostics (p : Parameters) :=
  ClockObservation p × (Bool × (Bool ×
    ((Fin p.K → Option ℕ) ×
      Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p))))

/-- Complete initial checks and the actual optional later-start observation.
This is a prefix observation; it does not yet encode the final dispatcher tag,
installation, Selection, or all output fields of `CollectionOutcome`. -/
def prechoiceDiagnostics (z : LocalInput p rate) : PrechoiceDiagnostics p :=
  let clock := clockObservation z
  (clock, coreCheck z, CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z),
    ledgerCurrentScores z.2.1, laterObservationAtClock z clock)

theorem measurable_prechoiceDiagnostics :
    Measurable (prechoiceDiagnostics (p := p) (rate := rate)) :=
  measurable_clockObservation.prodMk (measurable_coreCheck.prodMk
    (measurable_currentScoresCheck.prodMk
      (measurable_ledgerCurrentScores.prodMk measurable_laterObservation?)))

/-- Separate-input composition retains the whole continuous row and old
payload, the MOVING ledger, proposal, sole bank, time and local cutoff. Every
measurability premise is a caller's ordinary coordinate map. -/
theorem measurable_prechoiceDiagnostics_comp {X : Type*} [MeasurableSpace X]
    (payload : X → Payload rate) (ledger : X → Ledger rate)
    (proposal : X → Option (Fin p.T × Bool))
    (bank : X → CoordinatorUpReception.UpDecoderBank p)
    (row : X → CompletePublicTable.CompleteRow p) (time cutoff : X → Fin p.T)
    (hpayload : Measurable payload) (hledger : Measurable ledger)
    (hproposal : Measurable proposal) (hbank : Measurable bank)
    (hrow : Measurable row) (htime : Measurable time) (hcutoff : Measurable cutoff) :
    Measurable (fun x => prechoiceDiagnostics
      ((payload x, row x), ledger x, proposal x, bank x, time x, cutoff x)) :=
  measurable_prechoiceDiagnostics.comp
    ((hpayload.prodMk hrow).prodMk
      (hledger.prodMk (hproposal.prodMk (hbank.prodMk (htime.prodMk hcutoff)))))

/-- Physical-boundary inputs use the SAME collection coordinates of the
accepted CoordinatorCode. The cutoff index has not yet been manufactured. -/
abbrev BoundaryInput (p : Parameters) (rate : RateInput p) :=
  (Payload rate × CompletePublicTable.CompleteRow p) ×
    (Ledger rate × (Option (Fin p.T × Bool) ×
      (CoordinatorUpReception.UpDecoderBank p × Fin p.T)))

/-- The exact outer physical dispatch cutoff-domain test. -/
def cutoffValid (z : BoundaryInput p rate) : Prop :=
  1 ≤ z.2.1.cutoff ∧ z.2.1.cutoff ≤ p.T

theorem measurableSet_cutoffValid :
    MeasurableSet {z : BoundaryInput p rate | cutoffValid z} := by
  have h : MeasurableSet {ledger : Ledger rate |
      1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T} := Set.to_countable _ |>.measurableSet
  exact h.preimage (measurable_fst.comp measurable_snd)

/-- The local index uses exactly the existing physical cutoff conversion. -/
def boundaryLocal (z : {z : BoundaryInput p rate // cutoffValid z}) : LocalInput p rate :=
  (z.val.1, z.val.2.1, z.val.2.2.1, z.val.2.2.2.1, z.val.2.2.2.2,
    ⟨z.val.2.1.cutoff - 1, by have h := z.property; dsimp [cutoffValid] at h; omega⟩)

theorem measurable_boundaryLocal : Measurable (boundaryLocal (p := p) (rate := rate)) := by
  have hd : Measurable (fun z : {z : BoundaryInput p rate // cutoffValid z} => z.val.2) :=
    measurable_snd.comp measurable_subtype_coe
  have hledger : Measurable
      (fun z : {z : BoundaryInput p rate // cutoffValid z} =>
        (⟨z.val.2.1, z.property⟩ : {ledger : Ledger rate |
          1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T})) :=
    (measurable_fst.comp hd).subtype_mk
  let index : {ledger : Ledger rate | 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T} → Fin p.T :=
    fun ledger => ⟨ledger.val.cutoff - 1, by
      rcases ledger.property with ⟨hlo, hhi⟩
      omega⟩
  have hi : Measurable
      (fun z : {z : BoundaryInput p rate // cutoffValid z} =>
        (boundaryLocal z).2.2.2.2.2) :=
    (measurable_of_countable index).comp hledger
  exact (measurable_fst.comp measurable_subtype_coe).prodMk
    ((measurable_fst.comp hd).prodMk
      ((measurable_fst.comp (measurable_snd.comp hd)).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp hd))).prodMk
          ((measurable_snd.comp (measurable_snd.comp (measurable_snd.comp hd))).prodMk hi))))

/-- The malformed physical cutoff remains an explicit separate tag. A valid
cutoff enters the actual jointly varying local prefix, with no validity input. -/
def boundaryDiagnostics (z : BoundaryInput p rate) : Unit ⊕ PrechoiceDiagnostics p := by
  classical
  exact if hcutoff : cutoffValid z then
    .inr (prechoiceDiagnostics (boundaryLocal ⟨z, hcutoff⟩)) else .inl ()

theorem measurable_boundaryDiagnostics :
    Measurable (boundaryDiagnostics (p := p) (rate := rate)) := by
  classical
  exact Measurable.dite
    (measurable_inr.comp (measurable_prechoiceDiagnostics.comp measurable_boundaryLocal))
    measurable_const measurableSet_cutoffValid

theorem measurable_boundaryDiagnostics_comp {X : Type*} [MeasurableSpace X]
    (payload : X → Payload rate) (ledger : X → Ledger rate)
    (proposal : X → Option (Fin p.T × Bool))
    (bank : X → CoordinatorUpReception.UpDecoderBank p)
    (row : X → CompletePublicTable.CompleteRow p) (time : X → Fin p.T)
    (hpayload : Measurable payload) (hledger : Measurable ledger)
    (hproposal : Measurable proposal) (hbank : Measurable bank)
    (hrow : Measurable row) (htime : Measurable time) :
    Measurable (fun x => boundaryDiagnostics
      ((payload x, row x), ledger x, proposal x, bank x, time x)) :=
  measurable_boundaryDiagnostics.comp
    ((hpayload.prodMk hrow).prodMk
      (hledger.prodMk (hproposal.prodMk (hbank.prodMk htime))))

/-- Pointwise identity with the existing physical dispatch, on the canonical
collection constructor. It does not replace a Borel output theorem. -/
theorem dispatch_collection (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T) :
    let z : BoundaryInput p rate :=
      ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)
    let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
    dispatch x = .collection payload ledger (collectionClock payload ledger proposal cutoff) cutoff
      (CoordinatorRoundDispatch.dispatchCollection (assemble (boundaryLocal ⟨z, hcutoff⟩))) := by
  classical
  simp only [dispatch, hstate, dite_eq_left hcutoff, CoordinatorRoundDispatch.dispatch]
  rfl

/-- The outer failure retains the actual invalid-cutoff result, no Selection,
no DOWN view, and the prescribed fallback arm. -/
theorem dispatch_collection_invalid (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)) :
    dispatch x = .invalidCollectionCutoff ∧
      (dispatch x).selection = none ∧ (dispatch x).downView = none ∧
        (dispatch x).arm = coordinatorFallback p := by
  obtain ⟨hdispatch, harm⟩ := dispatch_collection_invalid_cutoff x payload ledger proposal hstate hcutoff
  exact ⟨hdispatch, by rw [hdispatch]; rfl, by rw [hdispatch]; rfl, harm⟩

/-- Literal collection coordinates already present in CoordinatorCode.
No new collection store or measurable representation is introduced. -/
abbrev CollectionCoordinates (p : Parameters) (rate : RateInput p) :=
  Payload rate × (Ledger rate × Option (Fin p.T × Bool))

def collectionCoordinates? : CoordinatorCode p rate → Option (CollectionCoordinates p rate)
  | .inl _ => none
  | .inr (.inl _) => none
  | .inr (.inr (.inl coordinates)) => some coordinates
  | .inr (.inr (.inr _)) => none

theorem measurable_collectionCoordinates? :
    Measurable (collectionCoordinates? (p := p) (rate := rate)) := by
  apply measurable_fun_sum measurable_const
  apply measurable_fun_sum measurable_const
  exact measurable_fun_sum
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable id measurable_id)
    measurable_const

/-- Attach the original row, bank and time to a collection coordinate triple. -/
def attachBoundary (c : CollectionCoordinates p rate)
    (rest : CompletePublicTable.CompleteRow p × (CoordinatorUpReception.UpDecoderBank p × Fin p.T)) :
    BoundaryInput p rate :=
  ((c.1, rest.1), c.2.1, c.2.2, rest.2.1, rest.2.2)

theorem measurable_attachBoundary : Measurable
    (fun z : CollectionCoordinates p rate ×
      (CompletePublicTable.CompleteRow p × (CoordinatorUpReception.UpDecoderBank p × Fin p.T)) =>
      attachBoundary z.1 z.2) := by
  exact ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp measurable_snd)).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
          (measurable_snd.comp (measurable_snd.comp measurable_snd)))))

/-- Sum decomposition for the original Option measurable space. It retains
all continuous coordinates of the supplied value and the independent rest. -/
def optionPairEquiv (A B : Type*) [MeasurableSpace A] [MeasurableSpace B] :
    (Option A × B) ≃ᵐ (A × B) ⊕ (PUnit × B) := by
  let e : Option A ≃ᵐ A ⊕ PUnit := {
    toEquiv := Equiv.optionEquivSumPUnit A
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      exact measurable_id }
  exact (MeasurableEquiv.prodCongr e (MeasurableEquiv.refl B)).trans
    (MeasurableEquiv.sumProdDistrib A PUnit B)

/-- Optional boundary diagnostics on original collection coordinates. Other
coordinator phases are absent; the invalid collection cutoff remains present
with its explicit boundary tag. -/
def optionalBoundaryDiagnostics (z : Option (CollectionCoordinates p rate) ×
    (CompletePublicTable.CompleteRow p × (CoordinatorUpReception.UpDecoderBank p × Fin p.T))) :
    Option (Unit ⊕ PrechoiceDiagnostics p) :=
  match z.1 with
  | none => none
  | some c => some (boundaryDiagnostics (attachBoundary c z.2))

theorem measurable_optionalBoundaryDiagnostics :
    Measurable (optionalBoundaryDiagnostics (p := p) (rate := rate)) := by
  let e := optionPairEquiv (CollectionCoordinates p rate)
    (CompletePublicTable.CompleteRow p × (CoordinatorUpReception.UpDecoderBank p × Fin p.T))
  let f : (CollectionCoordinates p rate ×
      (CompletePublicTable.CompleteRow p × (CoordinatorUpReception.UpDecoderBank p × Fin p.T))) ⊕
      (PUnit × (CompletePublicTable.CompleteRow p ×
        (CoordinatorUpReception.UpDecoderBank p × Fin p.T))) →
      Option (Unit ⊕ PrechoiceDiagnostics p) :=
    Sum.elim (fun z => some (boundaryDiagnostics (attachBoundary z.1 z.2))) (fun _ => none)
  have hf : Measurable f := measurable_fun_sum
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_boundaryDiagnostics.comp measurable_attachBoundary)) measurable_const
  have heq : optionalBoundaryDiagnostics (p := p) (rate := rate) = fun z => f (e z) := by
    funext z
    rcases z with ⟨c, rest⟩
    cases c <;> rfl
  rw [heq]
  exact hf.comp e.measurable

/-- Prefix diagnostics formed from the SAME canonical input and its
CoordinatorCode collection branch. This does not assert full-step Borel. -/
def canonicalDiagnostics (x : RoundInput p rate) : Option (Unit ⊕ PrechoiceDiagnostics p) :=
  optionalBoundaryDiagnostics
    (collectionCoordinates? (encodeCoordinator x.state.coordinator),
      x.row, x.state.upDecoderBank, x.time)

theorem measurable_canonicalDiagnostics :
    Measurable (canonicalDiagnostics (p := p) (rate := rate)) :=
  measurable_optionalBoundaryDiagnostics.comp
    ((measurable_collectionCoordinates?.comp
        (measurable_coordinatorCode.comp measurable_state)).prodMk
      (measurable_row.prodMk
        ((measurable_upDecoderBank.comp measurable_state).prodMk measurable_time)))

theorem canonicalDiagnostics_collection (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal) :
    canonicalDiagnostics x = some (boundaryDiagnostics
      ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)) := by
  simp only [canonicalDiagnostics, hstate, encodeCoordinator,
    collectionCoordinates?, optionalBoundaryDiagnostics, attachBoundary]

theorem canonicalDiagnostics_invalid (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate) (proposal : Option (Fin p.T × Bool))
    (hstate : x.state.coordinator = .collection payload ledger proposal)
    (hcutoff : ¬ (1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T)) :
    canonicalDiagnostics x = some (.inl ()) := by
  classical
  rw [canonicalDiagnostics_collection x payload ledger proposal hstate]
  exact congrArg some (dite_eq_right hcutoff)

/-- Lossless transient coordinates of the EXISTING Selection. The view keeps
its original continuous payload and weights. Only three certificate fields
are omitted, and their exact reconstruction is checked below. -/
abbrev SelectionCoordinates (p : Parameters) (rate : RateInput p) :=
  ReferenceDownReception.ChoiceTimeView p rate.eta ×
    (CoordinatorPhaseClock.StartRoundResult p × Fin p.K)

def encodeSelection {x : RoundInput p rate} (selection : Selection x) : SelectionCoordinates p rate :=
  (selection.view, selection.started, selection.arm)

def decodeSelection (x : RoundInput p rate) (code : SelectionCoordinates p rate) :
    Option (Selection x) := by
  classical
  exact if hpending : code.1.pendingAtChoice = code.2.1.pending then
    if hcutoff : code.1.cutoff =
        CoordinatorLiveChoiceRecorderStep.cutoffFromClock p code.2.1.clock.u then
      if hchoice : CoordinatorLocalArmChoice.coordinatorArmChoice code.1.payload
          code.1.pendingAtChoice code.1.cutoff x.time code.1.complementWeights x.row =
            some code.2.2 then
        some { view := code.1, started := code.2.1
               pending_eq := hpending, cutoff_eq := hcutoff
               arm := code.2.2, choice_eq := hchoice }
      else none
    else none
  else none

theorem decodeSelection_encodeSelection {x : RoundInput p rate} (selection : Selection x) :
    decodeSelection x (encodeSelection selection) = some selection := by
  classical
  cases selection with
  | mk view started hpending hcutoff arm hchoice =>
      dsimp only [encodeSelection, decodeSelection]
      rw [dite_eq_left hpending, dite_eq_left hcutoff, dite_eq_left hchoice]

theorem encodeSelection_injective {x : RoundInput p rate} :
    Function.Injective (encodeSelection (x := x)) := by
  intro a b h
  have heq := congrArg (decodeSelection x) h
  rw [decodeSelection_encodeSelection, decodeSelection_encodeSelection] at heq
  exact Option.some.inj heq

/-- Decode an optional retained selection without rerunning dispatch,
StartRound, or the later-assignment sampler. -/
def decodeSelection? (x : RoundInput p rate) : Option (SelectionCoordinates p rate) → Option (Selection x)
  | none => none
  | some code => decodeSelection x code

theorem decodeSelection?_map {x : RoundInput p rate} (selected : Option (Selection x)) :
    decodeSelection? x (selected.map encodeSelection) = selected := by
  cases selected with
  | none => rfl
  | some selection => exact decodeSelection_encodeSelection selection

/-- Exact Selection, DOWN-view and arm reconstruction of the very same
physical dispatch. These are pointwise identities; the joint measurability of
this final selection-code producer is still a separate obligation. -/
theorem dispatch_selection_reconstruct (x : RoundInput p rate) :
    let selected := decodeSelection? x ((dispatch x).selection.map encodeSelection)
    selected = (dispatch x).selection ∧
      selected.map Selection.view = (dispatch x).downView ∧
      (selected.map Selection.arm).getD (coordinatorFallback p) = (dispatch x).arm := by
  dsimp only
  rw [decodeSelection?_map]
  refine ⟨rfl, rfl, ?_⟩
  unfold DispatchCut.arm
  cases (dispatch x).selection <;> rfl

/-- The existing private countable-key arguments in the initialization
modules are not exported. This local gluing lemma uses only countable fibers
of a literal key and never changes a continuous measurable space. -/
private theorem measurable_of_countable_key {X K Y : Type*}
    [MeasurableSpace X] [MeasurableSpace K] [MeasurableSpace Y]
    [Countable K] [MeasurableSingletonClass K]
    [Countable Y] [MeasurableSingletonClass Y]
    (key : X → K) (hkey : Measurable key) (f : X → Y)
    (hfactor : ∀ x y, key x = key y → f x = f y) : Measurable f := by
  classical
  apply measurable_to_countable'
  intro b
  have heq : f ⁻¹' {b} =
      ⋃ k : {k : K // ∃ y, key y = k ∧ f y = b}, key ⁻¹' {k.val} := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨key x, x, rfl, hx⟩, rfl⟩
    · intro hx
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨y, hy, hfy⟩ := k.property
      exact (hfactor x y (hk.trans hy.symm)).trans hfy
  rw [heq]
  exact MeasurableSet.iUnion fun k => hkey (measurableSet_singleton k.val)

/-- An INTERNAL branch subtype obtained after testing the core and nonempty
pending set. Its carrier is not a global input assumption. -/
abbrev PendingCoreInput (p : Parameters) (rate : RateInput p) :=
  {z : CoreInput p rate // z.val.2.1.pending.Nonempty}

/-- The exact retained clock result on continuing collection. This constructs
its literal fields and proves equality with the one original StartRound call;
it does not make another call to StartRound. -/
def carriedStart (z : PendingCoreInput p rate) : CoordinatorPhaseClock.StartRoundResult p := {
  clock := (assemble z.val.val).clock
  gridDomain := CoordinatorPhaseClock.clockRegistersValid_gridDomain p rate.eta.val
    (assemble z.val.val).clock z.val.property.clock_registers_valid
  pending := z.val.val.2.1.pending
  ledgerCommand := none
  assignmentStart := none }

theorem carriedStart_eq_actual (z : PendingCoreInput p rate) :
    CoordinatorPhaseClock.startRound p rate.eta.val (assemble z.val.val).time
      (assemble z.val.val).clock (assemble z.val.val).ledger.pending =
        .ok (carriedStart z) := by
  have htime : (assemble z.val.val).payload.sigma.val < (assemble z.val.val).time.val ∧
      (assemble z.val.val).cutoffIndex.val ≤ (assemble z.val.val).time.val := by
    simpa only [CoordinatorPhaseClock.startRoundTimeValid,
      z.val.property.clock_sigma_eq, z.val.property.clock_cutoff_eq] using
      z.val.property.clock_start_time_valid
  exact CoordinatorPhaseClock.startRound_collection_pending p rate.eta.val
    (assemble z.val.val).time (assemble z.val.val).payload.sigma
    (assemble z.val.val).cutoffIndex (assemble z.val.val).clock
    (assemble z.val.val).ledger.pending z.val.property.clock_parameter_valid
    z.val.property.clock_registers_valid z.val.property.clock_sigma_eq
    z.val.property.clock_cutoff_eq htime.2 z.property.ne_empty

theorem measurable_carriedStart : Measurable (carriedStart (p := p) (rate := rate)) := by
  apply measurable_of_countable_key (fun z : PendingCoreInput p rate => coreKey z.val.val)
    (measurable_coreKey.comp (measurable_subtype_coe.comp measurable_subtype_coe))
  intro a b hab
  apply CoordinatorCollectionRunMeasurabilityRepair.startRoundResultCode_injective
  exact congrArg (fun k : CoreKey p rate =>
    ((⟨some k.1.1, some k.2.2.2.2.2, k.2.1.freezeAt, k.2.2.1⟩ :
      CoordinatorPhaseClock.ClockRegisters p),
      k.2.1.pending,
      (none : Option (CoordinatorPhaseClock.CollectionLedgerCommand p)),
      (none : Option (CoordinatorPhaseClock.AssignmentStartInstruction p)))) hab

/-- The actual continuing view, original StartRound result, and checked arm
candidate. An absent candidate is the real choice-domain failure. -/
abbrev ContinuingObservation (p : Parameters) (rate : RateInput p) :=
  ReferenceDownReception.ChoiceTimeView p rate.eta ×
    (CoordinatorPhaseClock.StartRoundResult p × Option (Fin p.K))

def continuingObservation (z : PendingCoreInput p rate) : ContinuingObservation p rate :=
  let view := continuingView z.val (carriedStart z)
  (view, carriedStart z, CoordinatorLocalArmChoice.coordinatorArmChoice
    view.payload view.pendingAtChoice view.cutoff (assemble z.val.val).time
    view.complementWeights (assemble z.val.val).row)

theorem measurable_continuingObservation :
    Measurable (continuingObservation (p := p) (rate := rate)) := by
  have hv : Measurable (fun z : PendingCoreInput p rate =>
      continuingView z.val (carriedStart z)) :=
    measurable_continuingView.comp (measurable_subtype_coe.prodMk measurable_carriedStart)
  have ht : Measurable (fun z : PendingCoreInput p rate => (assemble z.val.val).time) :=
    (measurable_of_countable (fun d : DiscreteInput p rate => d.2.2.2.1)).comp
      (measurable_snd.comp (measurable_subtype_coe.comp measurable_subtype_coe))
  have hr : Measurable (fun z : PendingCoreInput p rate => (assemble z.val.val).row) :=
    measurable_snd.comp (measurable_fst.comp
      (measurable_subtype_coe.comp measurable_subtype_coe))
  have hin : Measurable (fun z : PendingCoreInput p rate =>
      (⟨(continuingView z.val (carriedStart z),
        (assemble z.val.val).row, (assemble z.val.val).time), z.property⟩ :
        PendingChoiceInput p rate)) :=
    (hv.prodMk (hr.prodMk ht)).subtype_mk
  exact hv.prodMk (measurable_carriedStart.prodMk
    (measurable_pendingArmChoice.comp hin))

/-- Literal connection of the continuing view with an original prepared
snapshot: the OLD payload and actual ledger weights are retained exactly. -/
theorem continuingView_eq_snapshot (z : CoreInput p rate)
    (prepared : CoordinatorCollectionInteractive.PreparedSnapshot (assemble z.val)) :
    (continuingView z prepared.clockStarted).payload = (assemble z.val).payload ∧
      (continuingView z prepared.clockStarted).pendingAtChoice = prepared.clockStarted.pending ∧
      (continuingView z prepared.clockStarted).complementWeights =
        CoordinatorCollectionInteractive.PreObservationInputs.weights (assemble z.val)
          prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq :=
  ⟨rfl, rfl, rfl⟩

/-- Separate component composition for the pending-choice theorem. Nonempty
pending is an explicit branch condition, with no validity or current-score
truth premise. The caller supplies the view/row/time maps separately. -/
theorem measurable_pendingArmChoice_comp {X : Type*} [MeasurableSpace X]
    (view : X → ReferenceDownReception.ChoiceTimeView p rate.eta)
    (row : X → CompletePublicTable.CompleteRow p) (time : X → Fin p.T)
    (hview : Measurable view) (hrow : Measurable row) (htime : Measurable time)
    (hpending : ∀ x, (view x).pendingAtChoice.Nonempty) :
    Measurable (fun x => CoordinatorLocalArmChoice.coordinatorArmChoice
      (view x).payload (view x).pendingAtChoice (view x).cutoff (time x)
      (view x).complementWeights (row x)) :=
  measurable_pendingArmChoice.comp
    ((hview.prodMk (hrow.prodMk htime)).subtype_mk (h := hpending))

/-- Test the nonempty-pending branch internally before constructing its
certified continuing observation. -/
def pendingObservation? (z : CoreInput p rate) : Option (ContinuingObservation p rate) := by
  classical
  exact if hpending : z.val.2.1.pending.Nonempty then
    some (continuingObservation ⟨z, hpending⟩) else none

theorem measurable_pendingObservation? :
    Measurable (pendingObservation? (p := p) (rate := rate)) := by
  classical
  have hset : MeasurableSet {z : CoreInput p rate | z.val.2.1.pending.Nonempty} :=
    (Set.to_countable {ledger : Ledger rate | ledger.pending.Nonempty}).measurableSet.preimage
      (measurable_fst.comp (measurable_snd.comp measurable_subtype_coe))
  unfold pendingObservation?
  have hsome : Measurable (fun z : PendingCoreInput p rate =>
      (some (continuingObservation z) : Option (ContinuingObservation p rate))) :=
    LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      measurable_continuingObservation
  have hm := Measurable.dite hsome
    (measurable_const (a := (none : Option (ContinuingObservation p rate)))) hset
  convert hm using 1
  funext z
  by_cases hpending : z.val.2.1.pending.Nonempty
  · simp [hpending]
    exact ⟨hpending, rfl⟩
  · simp [hpending]
    exact hpending

/-- Unrestricted continuing observation. Failed cores, empty pending sets and
failed current-score bounds never produce a continuing candidate. Choice
failure remains the literal absent arm inside a retained candidate. -/
def continuingObservation? (z : LocalInput p rate) : Option (ContinuingObservation p rate) := by
  classical
  exact if hcore : CoordinatorRoundDispatch.CollectionCoreValid (assemble z) then
    if CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z) = true then
      pendingObservation? ⟨z, hcore⟩ else none
  else none

theorem measurable_continuingObservation? :
    Measurable (continuingObservation? (p := p) (rate := rate)) := by
  classical
  exact Measurable.dite
    (Measurable.ite (measurableSet_currentScoresCheck.preimage measurable_subtype_coe)
      measurable_pendingObservation? measurable_const)
    measurable_const measurableSet_coreChecks

/-- The explicit continuing guard equation is local to this constructor; it
is not used as a premise of the unrestricted Borel theorem. -/
theorem continuingObservation?_eq (z : LocalInput p rate)
    (core : CoordinatorRoundDispatch.CollectionCoreValid (assemble z))
    (hpending : z.2.1.pending.Nonempty)
    (hscores : CoordinatorRoundDispatch.collectionCurrentScoresCheck (assemble z) = true) :
    continuingObservation? z = some (continuingObservation ⟨⟨z, core⟩, hpending⟩) := by
  classical
  simp only [continuingObservation?, dite_eq_left core, ite_eq_left hscores,
    pendingObservation?, dite_eq_left hpending]

/-- All proved pre-choice ingredients: checked clock/core/score diagnostics,
actual full later operation observation, and the old-payload continuing view
with its original checked arm candidate. This is not a full dispatch-output
encoding: the successful later installation and final outcome tag still
require gluing. -/
abbrev CollectionPrefixObservation (p : Parameters) (rate : RateInput p) :=
  PrechoiceDiagnostics p × Option (ContinuingObservation p rate)

def collectionPrefixObservation (z : LocalInput p rate) : CollectionPrefixObservation p rate :=
  (prechoiceDiagnostics z, continuingObservation? z)

theorem measurable_collectionPrefixObservation :
    Measurable (collectionPrefixObservation (p := p) (rate := rate)) :=
  measurable_prechoiceDiagnostics.prodMk measurable_continuingObservation?

theorem measurable_collectionPrefixObservation_comp {X : Type*} [MeasurableSpace X]
    (payload : X → Payload rate) (ledger : X → Ledger rate)
    (proposal : X → Option (Fin p.T × Bool))
    (bank : X → CoordinatorUpReception.UpDecoderBank p)
    (row : X → CompletePublicTable.CompleteRow p) (time cutoff : X → Fin p.T)
    (hpayload : Measurable payload) (hledger : Measurable ledger)
    (hproposal : Measurable proposal) (hbank : Measurable bank)
    (hrow : Measurable row) (htime : Measurable time) (hcutoff : Measurable cutoff) :
    Measurable (fun x => collectionPrefixObservation
      ((payload x, row x), ledger x, proposal x, bank x, time x, cutoff x)) :=
  measurable_collectionPrefixObservation.comp
    ((hpayload.prodMk hrow).prodMk
      (hledger.prodMk (hproposal.prodMk (hbank.prodMk (htime.prodMk hcutoff)))))

/-- The full proved prefix, including the outer invalid-cutoff boundary. -/
def boundaryPrefixObservation (z : BoundaryInput p rate) :
    Unit ⊕ CollectionPrefixObservation p rate := by
  classical
  exact if hcutoff : cutoffValid z then
    .inr (collectionPrefixObservation (boundaryLocal ⟨z, hcutoff⟩)) else .inl ()

theorem measurable_boundaryPrefixObservation :
    Measurable (boundaryPrefixObservation (p := p) (rate := rate)) := by
  classical
  exact Measurable.dite
    (measurable_inr.comp (measurable_collectionPrefixObservation.comp measurable_boundaryLocal))
    measurable_const measurableSet_cutoffValid

/-!
Remaining obligation (not an assumption or exported theorem): prove a single
joint lossless observation/decoder of `dispatchCollection` itself, retaining
every final failure tag, actual later installation, reconstruction and
Selection. In particular the proved prefix and pointwise reconstruction
lemmas above do not establish joint Borel measurability of the final
`CollectionOutcome` observation, its installed canonical live code, or the
actual physical dispatch selection-code producer. No whole-step, horizon,
sampling-law or manuscript-closure theorem is asserted.
-/

/-- Exact lossless numerical selection coordinates of every original
collection outcome. Continuing collection retains the OLD payload and actual
ledger weights. A chosen later start retains the installed payload and actual
installed score weights. Failures have no Selection; their full tags remain
in the original retained outcome. This is a pointwise theorem. -/
theorem collection_selection_coordinates (x : RoundInput p rate)
    (payload : Payload rate) (ledger : Ledger rate)
    (clock : CoordinatorPhaseClock.ClockRegisters p) (cutoff : Fin p.T)
    (outcome : CoordinatorRoundDispatch.CollectionOutcome
      (collectionInput x payload ledger clock cutoff)) :
    (DispatchCut.collection payload ledger clock cutoff outcome).selection.map encodeSelection =
      match outcome with
      | .continuing _ prepared _ _ =>
          some (({
            payload := payload
            pendingAtChoice := prepared.clockStarted.pending
            cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p prepared.clockStarted.clock.u
            complementWeights := CoordinatorCollectionInteractive.PreObservationInputs.weights
              (collectionInput x payload ledger clock cutoff)
              prepared.inputsValid.ledger_valid prepared.inputsValid.assignment_eq } :
                ReferenceDownReception.ChoiceTimeView p rate.eta),
            prepared.clockStarted, prepared.arm)
      | .laterChosen _ _ started _ _ _ _ _ _ installed selected =>
          some (({
            payload := installed.registers.payload
            pendingAtChoice := started.pending
            cutoff := CoordinatorLiveChoiceRecorderStep.cutoffFromClock p started.clock.u
            complementWeights := installed.registers.complementWeights } :
              ReferenceDownReception.ChoiceTimeView p rate.eta), started, selected.arm)
      | _ => none := by
  classical
  cases outcome
  case laterChosen core consistent started hstart instruction hinstruction output
      hlocal clockData installed selected =>
    have ht := later_instruction_time x payload ledger clock cutoff core started instruction
      hstart hinstruction
    simp only [DispatchCut.selection, selectionAt, dite_eq_left ht, Option.map_some,
      encodeSelection]
  all_goals rfl

end Bandits.Support.ReferenceCollectionDispatchMeasurability

end
