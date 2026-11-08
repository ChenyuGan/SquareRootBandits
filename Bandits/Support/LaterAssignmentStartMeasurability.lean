/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.LaterAssignmentStartOperation
public import Bandits.Support.CheckedAssignmentJointMeasurability
public import Mathlib.Basic.Countable.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of the actual later assignment start

For one fixed retained old payload, the local ledger, instruction, and
consistency witness form a countable carrier. The complete public row remains
continuous. The code records the exact reconstruction failure, checked-prefix
failure, orientation failure, or sampled oriented assignment; the original
row, including every assignment coordinate, stays in the input.

Sources: `sources/zip4/manuscript/06_interruptions.tex:16-61,80-100`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CoordinatorCollectionLedger
open Bandits.Support.CoordinatorPhaseClock
open Bandits.Support.AssignmentScoreReconstruction
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.CheckedAssignmentSample
open Bandits.Support.CheckedAssignmentJointMeasurability
open Bandits.Support.PrefixSetSampler
open Bandits.Support.OrientedAssignmentLaw
open Bandits.Support.CompletePublicTable
open Bandits.Support.ContinuousControlSlice

namespace Bandits.Support.LaterAssignmentStartMeasurability

variable {p : ConstructorDimensions.Parameters}
abbrev LearningRate := Bandits.Support.ReferencePrelaunchFollower.LearningRate

variable {eta : LearningRate}
variable {old : AssignmentStartPayload.Input p eta}

/-! ## A faithful countable encoding of the actual local input -/

private def assignmentCode (a : CoordinatorCollectionLedger.Assignment p) := a.arm

private theorem assignmentCode_injective :
    Function.Injective (assignmentCode (p := p)) := by
  intro a b h
  cases a with
  | mk aa ha =>
    cases b with
    | mk ba hb =>
      simp only [assignmentCode] at h
      cases h
      rfl

private instance assignmentCountable :
    Countable (CoordinatorCollectionLedger.Assignment p) :=
  assignmentCode_injective.countable

private def cutoffRegisterCode (r : CoordinatorCollectionLedger.CutoffRegister) :=
  (r.score, (r.queue, r.lastService))

private theorem cutoffRegisterCode_injective :
    Function.Injective cutoffRegisterCode := by
  intro a b h
  cases a with
  | mk as aq ad =>
    cases b with
    | mk bs bq bd =>
      simp only [cutoffRegisterCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl

private instance cutoffRegisterCountable :
    Countable CoordinatorCollectionLedger.CutoffRegister :=
  cutoffRegisterCode_injective.countable

private def currentRegisterCode (r : CoordinatorCollectionLedger.CurrentRegister) :=
  (r.queue, r.lastService)

private theorem currentRegisterCode_injective :
    Function.Injective currentRegisterCode := by
  intro a b h
  cases a with
  | mk aq ad =>
    cases b with
    | mk bq bd =>
      simp only [currentRegisterCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

private instance currentRegisterCountable :
    Countable CoordinatorCollectionLedger.CurrentRegister :=
  currentRegisterCode_injective.countable

private def phaseCode : CoordinatorCollectionLedger.Phase → Fin 3
  | .ready => 0
  | .started => 1
  | .decoded => 2

private theorem phaseCode_injective : Function.Injective phaseCode := by
  intro a b h
  cases a <;> cases b <;> simp [phaseCode] at h ⊢

private instance phaseCountable : Countable CoordinatorCollectionLedger.Phase :=
  phaseCode_injective.countable

/-- The ledger code retains every data field. Its proof fields are omitted
because equality of those fields is proof-irrelevant. In particular the raw
buffer is the actual finite arm-by-time `Option ℕ` array. -/
def ledgerCode
    (ledger : LaterAssignmentStartOperation.LocalLedger old) :=
  (ledger.assignment, ledger.sigma, ledger.cutoff, ledger.freezeAt,
    ledger.baseScore, ledger.pending, ledger.cutoffRegisters,
    ledger.currentRegisters, ledger.increment, ledger.gammaLoc,
    ledger.rawBuffer, ledger.enabledHistory, ledger.cursor, ledger.phase)

theorem ledgerCode_injective :
    Function.Injective (ledgerCode (p := p) (eta := eta) (old := old)) := by
  intro a b h
  cases a with
  | mk aa as ac af abs ap acr cur inc gam raw enabled cursor phase =>
    cases b with
    | mk ba bs bc bf bbs bp bcr bcur binc bgam braw benabled bcursor bphase =>
      simp only [ledgerCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

theorem countable_localLedger :
    Countable (LaterAssignmentStartOperation.LocalLedger (p := p) (eta := eta) old) :=
  ledgerCode_injective.countable

def assignmentStartKindCode :
    CoordinatorPhaseClock.AssignmentStartKind → Fin 3
  | .first => 0
  | .corrected => 1
  | .renewal => 2

private theorem assignmentStartKindCode_injective :
    Function.Injective assignmentStartKindCode := by
  intro a b h
  cases a <;> cases b <;> simp [assignmentStartKindCode] at h ⊢

def instructionCode (instruction : AssignmentStartInstruction p) :=
  (instruction.time, assignmentStartKindCode instruction.kind)

private theorem instructionCode_injective :
    Function.Injective (instructionCode (p := p)) := by
  intro a b h
  cases a with
  | mk atime akind =>
    cases b with
    | mk btime bkind =>
      simp only [instructionCode, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hk⟩
      have : akind = bkind := assignmentStartKindCode_injective hk
      cases this
      rfl

private instance instructionCountable :
    Countable (AssignmentStartInstruction p) := instructionCode_injective.countable

def consistencyCode
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger) : ℕ :=
  consistent.oldFreezeAt

private theorem consistencyCode_injective
    (ledger : LaterAssignmentStartOperation.LocalLedger (p := p) (eta := eta) old) :
    Function.Injective (consistencyCode (old := old) ledger) := by
  intro a b h
  cases a with
  | mk hstart hassignment freeze hfreeze =>
    cases b with
    | mk hstart' hassignment' freeze' hfreeze' =>
      simp only [consistencyCode] at h
      cases h
      rfl

/-- The actual dependent local inputs, bundled only to state joint
measurability. Every runtime field of the ledger, instruction and consistency
data is retained; only equality proofs are omitted by `ledgerCode`. -/
abbrev LocalStartInput (old : AssignmentStartPayload.Input p eta) :=
  Σ ledger : LaterAssignmentStartOperation.LocalLedger old,
    AssignmentStartInstruction p × LaterAssignmentStartOperation.LocalConsistency old ledger

def localStartInputCode (input : LocalStartInput (p := p) (eta := eta) old) :=
  (ledgerCode input.1, (instructionCode input.2.1,
    consistencyCode input.1 input.2.2))

/-- Observable coordinates of a retained payload. The real anchor function
keeps the ordinary product Borel sigma algebra. -/
abbrev PayloadObservation (p : ConstructorDimensions.Parameters) :=
  ℕ × (Fin p.T × (Finset (Fin p.K) × ((Fin p.K → ℝ) × (Fin p.K → ℕ))))

def payloadObservation (input : AssignmentStartPayload.Input p eta) : PayloadObservation p :=
  (input.n, (input.sigma, (input.slowSet.1, (input.anchor, input.queues))))

private theorem payloadObservation_injective :
    Function.Injective (payloadObservation (p := p) (eta := eta)) := by
  intro a b h
  cases a with
  | mk ac an ane asigma aslowset aanchor aapos aqueues aqle =>
    cases b with
    | mk bc bn bne bsigma bslowset banchor bapos bqueues bqle =>
      simp only [payloadObservation, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, hslow, rfl, rfl⟩
      have : aslowset = bslowset := Subtype.ext hslow
      cases this
      rfl

instance payloadInputMeasurableSpace :
    MeasurableSpace (AssignmentStartPayload.Input p eta) :=
  (inferInstance : MeasurableSpace (PayloadObservation p)).comap payloadObservation

theorem measurableSet_singleton_payload
    (value : AssignmentStartPayload.Input p eta) :
    MeasurableSet ({value} : Set (AssignmentStartPayload.Input p eta)) := by
  have hset : ({value} : Set (AssignmentStartPayload.Input p eta)) =
      payloadObservation ⁻¹' {payloadObservation value} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact payloadObservation_injective.eq_iff.symm
  rw [hset]
  exact (measurableSet_singleton (payloadObservation value)).preimage
    (comap_measurable payloadObservation)

theorem localStartInputCode_injective :
    Function.Injective (localStartInputCode (p := p) (eta := eta) (old := old)) := by
  intro a b h
  rcases a with ⟨ledgerA, ⟨instructionA, consistentA⟩⟩
  rcases b with ⟨ledgerB, ⟨instructionB, consistentB⟩⟩
  simp only [localStartInputCode, Prod.mk.injEq] at h
  rcases h with ⟨hledger, hinstruction, hfreeze⟩
  have hledger' : ledgerA = ledgerB := ledgerCode_injective hledger
  subst ledgerB
  have hinstruction' : instructionA = instructionB := instructionCode_injective hinstruction
  subst instructionB
  have hconsistent : consistentA = consistentB :=
    consistencyCode_injective (old := old) (ledger := ledgerA) hfreeze
  subst consistentB
  rfl

instance localStartInputCountable :
    Countable (LocalStartInput (p := p) (eta := eta) old) :=
  localStartInputCode_injective.countable

theorem countable_localStartInput :
    Countable (LocalStartInput (p := p) (eta := eta) old) :=
  localStartInputCountable

instance localStartInputMeasurableSpace (old : AssignmentStartPayload.Input p eta) :
    MeasurableSpace (LocalStartInput old) := ⊤

instance localStartInputDiscrete (old : AssignmentStartPayload.Input p eta) :
    DiscreteMeasurableSpace (LocalStartInput old) := by
  exact ⟨fun _ => trivial⟩

/-! ## Exact countable output code -/

/-- The lossless finite code for the actual dependent operation result. A
successful code retains the complete oriented assignment outcome; the original
assignment vector remains in the complete-row input. -/
inductive LaterAssignmentStartCode (p : ConstructorDimensions.Parameters) where
  | reconstructionFailure (reason : AssignmentScoreReconstruction.Failure)
  | prefixFailure (arm : Option (Fin p.K))
      (reason : CheckedPrefixSampler.FailureReason)
  | orientationFailure (set : PrefixSetSampler.SetCarrier p.K p.m)
  | sampled (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m)
  deriving DecidableEq

private def failureCode (failure : AssignmentScoreReconstruction.Failure) : Fin 7 :=
  match failure with
  | .invalidLedger => 0
  | .phaseNotReady => 1
  | .cursorMismatch => 2
  | .collectionPending => 3
  | .instructionKindMismatch => 4
  | .currentOutputDomain => 5
  | .previousOutputDomain => 6

private theorem failureCode_injective : Function.Injective failureCode := by
  intro a b h
  cases a <;> cases b <;> simp [failureCode] at h ⊢

private instance reconstructionFailureCountable :
    Countable AssignmentScoreReconstruction.Failure :=
  failureCode_injective.countable

private def laterCodeEncoding (code : LaterAssignmentStartCode p) :=
  match code with
  | .reconstructionFailure reason => Sum.inl reason
  | .prefixFailure arm reason =>
      Sum.inr (Sum.inl (arm, reason))
  | .orientationFailure set =>
      Sum.inr (Sum.inr (Sum.inl set))
  | .sampled outcome =>
      Sum.inr (Sum.inr (Sum.inr outcome))

private theorem laterCodeEncoding_injective :
    Function.Injective (laterCodeEncoding (p := p)) := by
  intro a b h
  cases a <;> cases b <;> simp_all [laterCodeEncoding]

instance codeCountable (p : ConstructorDimensions.Parameters) :
    Countable (LaterAssignmentStartCode p) :=
  (laterCodeEncoding_injective (p := p)).countable

instance codeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (LaterAssignmentStartCode p) := ⊤

instance codeDiscrete (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (LaterAssignmentStartCode p) := by
  exact ⟨fun _ => trivial⟩

local instance checkedSampleResultMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (CheckedAssignmentSample.Result p) := ⊤

local instance checkedSampleResultDiscrete (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (CheckedAssignmentSample.Result p) := by
  exact ⟨fun _ => trivial⟩

universe u
instance optionMeasurableSpace {α : Type u} [MeasurableSpace α] :
    MeasurableSpace (Option α) :=
  (inferInstance : MeasurableSpace (α ⊕ PUnit.{u + 1})).comap
    (Equiv.optionEquivSumPUnit.{u, u} α)
def codeOfCheckedSample (p : ConstructorDimensions.Parameters)
    (sample : CheckedAssignmentSample.Result p) : LaterAssignmentStartCode p :=
  match sample with
  | .prefixFailure arm reason => .prefixFailure arm reason
  | .orientationFailure set => .orientationFailure set
  | .sampled outcome => .sampled outcome
def codeOfResult (p : ConstructorDimensions.Parameters)
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    {consistent : LaterAssignmentStartOperation.LocalConsistency old ledger}
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent) :
    LaterAssignmentStartCode p :=
  match result with
  | .reconstructionFailure reason => .reconstructionFailure reason
  | .prefixFailure arm reason => .prefixFailure arm reason
  | .orientationFailure set => .orientationFailure set
  | .success output _ => .sampled output.outcome

/-- Code projection of the operation's complete dependent result. -/
noncomputable def laterAssignmentStartCode
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger) :
    LaterAssignmentStartCode p :=
  codeOfResult p (LaterAssignmentStartOperation.laterAssignmentStart
    old ledger instruction row consistent)

/-- The law parameters chosen by the literal reconstruction-first operation.
This definition takes no measurability inputs: both real-valued maps are
computed from the actual successful reconstruction and the fixed old payload. -/
structure SuccessfulLawSelection
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction) where
  cutoffReached : ledger.cutoff ≤ instruction.time.val + 1
  currentWeightPos : ∀ i, 0 < AssignmentScoreReconstruction.currentWeight out i
  cutoffWeightPos : ∀ i, 0 < AssignmentScoreReconstruction.cutoffWeight out i
  law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out
  lawSelected : LaterAssignmentStartOperation.selectLaw? old ledger instruction out
    cutoffReached currentWeightPos = some law

/-- Derive every successful-law input from the literal reconstruction result.
The selected law is the existing law-selection result, not a supplied
measurability or feasibility assumption. -/
noncomputable def successfulLawSelection
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
    SuccessfulLawSelection old ledger instruction out := by
  classical
  have hequations := AssignmentScoreReconstruction.reconstructLaterStart_success_equations
    ledger instruction out hcall
  rcases hequations with
    ⟨hchecks, _, _, _, _, _, _, hcurrentPos, hcutoffPos, _, _⟩
  rcases hchecks with ⟨hvalid, _, hcursor, _, _, _, _⟩
  have hcutoffCursor : ledger.cutoff ≤ ledger.cursor := by
    have h := hvalid
    simp only [CoordinatorCollectionLedger.validLedgerCheck,
      Bool.and_eq_true, decide_eq_true_eq] at h
    tauto
  have hcutoff : ledger.cutoff ≤ instruction.time.val + 1 := by
    rw [← hcursor]
    exact hcutoffCursor
  have hselected := LaterAssignmentStartOperation.selectLaw?_isSome
    old ledger instruction out hcall hcutoff hcurrentPos
  let law := Classical.choose hselected
  exact ⟨hcutoff, hcurrentPos, hcutoffPos, law, Classical.choose_spec hselected⟩

/-- The actual selected law's raw mass and anchor, computed after successful
reconstruction. -/
noncomputable def selectedSamplerParameters
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
    CheckedAssignmentJointMeasurability.RawMass p ×
      CheckedAssignmentJointMeasurability.Anchor p :=
  let selection := successfulLawSelection old ledger instruction out hcall
  (selection.law.mass, selection.law.anchor)

/-- The literal selected law and anchor, absent only when the accepted
reconstruction itself fails. -/
noncomputable def selectedSamplerParameters?
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old) :
    Option (CheckedAssignmentJointMeasurability.RawMass p ×
      CheckedAssignmentJointMeasurability.Anchor p) := by
  rcases input with ⟨ledger, ⟨instruction, _consistent⟩⟩
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction
      old ledger instruction with
  | failure _ => exact none
  | success out hcall =>
      exact some (selectedSamplerParameters old ledger instruction out hcall)

/-- The selected-law raw-mass map is measurable on the actual countable local
input. On reconstruction failure it is absent, rather than assigned an
arbitrary mass. -/
theorem measurable_selectedSamplerParameters?
    (old : AssignmentStartPayload.Input p eta) :
    Measurable (selectedSamplerParameters? (p := p) (eta := eta) old) :=
  Measurable.of_discrete

/-- Measurability of the requested complete `K+1` vector read from the
coordinator's own continuous row. -/
theorem measurable_ownAssignmentVector (time : Fin p.T) :
    Measurable (fun row : CompletePublicTable.CompleteRow p =>
      LaterAssignmentStartOperation.ownAssignmentVector row time) := by
  change Measurable (ContinuousControlSlice.assignmentVector ∘
    (fun row : CompletePublicTable.CompleteRow p => ((row.2) time).1))
  have hslice : Measurable (fun row : CompletePublicTable.CompleteRow p =>
      (row.2 time).1) := by
    exact measurable_fst.comp
      ((measurable_pi_apply time).comp measurable_snd)
  exact (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp hslice

/-- The code computed by the actual operation's reconstruction, selected-law,
and one checked full-vector sampler call. -/
noncomputable def reconstructedFirstCode
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row : CompletePublicTable.CompleteRow p) : LaterAssignmentStartCode p :=
  match LaterAssignmentStartOperation.decideReconstruction old input.1 input.2.1 with
  | .failure reason => .reconstructionFailure reason
  | .success out hcall =>
      let parameters := selectedSamplerParameters old input.1 input.2.1 out hcall
      codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
        parameters.1 parameters.2
        (LaterAssignmentStartOperation.ownAssignmentVector row input.2.1.time))

/-- On the renewal branch, law selection only constructs `Q(currentWeight)`
and takes its anchor from the current weights. This projection equality makes
the absence of the corrected previous-weight read explicit. -/
theorem selectedSamplerParameters_renewal
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hrenewal : instruction.kind = .renewal) :
    (selectedSamplerParameters old ledger instruction out hcall).2 =
      AssignmentScoreReconstruction.currentWeight out ∧
      ∀ S, (selectedSamplerParameters old ledger instruction out hcall).1 S =
        LaterAssignmentStartOperation.renewalRawMass out S := by
  classical
  let selection := successfulLawSelection old ledger instruction out hcall
  have hspec := LaterAssignmentStartOperation.selectLaw?_renewal_spec
    old ledger instruction out selection.cutoffReached selection.currentWeightPos
      selection.law selection.lawSelected hrenewal
  simpa [selectedSamplerParameters, selection] using hspec

/-- For a fixed countable local input, every exact failure or sampled-outcome
fiber of the reconstruction-first code is measurable in the untouched full
continuous complete row. -/
theorem measurableSet_reconstructedFirstCode_fiber
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (code : LaterAssignmentStartCode p) :
    MeasurableSet {row : CompletePublicTable.CompleteRow p |
      reconstructedFirstCode old input row = code} := by
  classical
  rcases input with ⟨ledger, ⟨instruction, _consistent⟩⟩
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction
      old ledger instruction with
  | failure reason =>
      by_cases hcode : LaterAssignmentStartCode.reconstructionFailure reason = code
      · simp [reconstructedFirstCode, hdecision, hcode]
      · simp [reconstructedFirstCode, hdecision, hcode]
  | success out hcall =>
      let parameters := selectedSamplerParameters old ledger instruction out hcall
      let sample : CompletePublicTable.CompleteRow p → CheckedAssignmentSample.Result p :=
        fun row => CheckedAssignmentSample.checkedAssignmentSample p
          parameters.1 parameters.2
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
      have hmass : Measurable (fun _ : CompletePublicTable.CompleteRow p => parameters.1) :=
        measurable_const
      have hanchor : Measurable (fun _ : CompletePublicTable.CompleteRow p => parameters.2) :=
        measurable_const
      have hassignment : Measurable (fun row : CompletePublicTable.CompleteRow p =>
          LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) :=
        measurable_ownAssignmentVector instruction.time
      have hsample : Measurable sample := by
        change Measurable (fun row =>
          CheckedAssignmentSample.checkedAssignmentSample p parameters.1 parameters.2
            (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time))
        exact CheckedAssignmentJointMeasurability.measurable_checkedAssignmentSample_comp
          p (fun _ => parameters.1) (fun _ => parameters.2)
          (fun row => LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
          hmass hanchor hassignment
      have hcode : Measurable (fun row => codeOfCheckedSample p (sample row)) :=
        (Measurable.of_discrete (f := codeOfCheckedSample p)).comp hsample
      have hevent := hcode (measurableSet_singleton code)
      have hset :
          {row : CompletePublicTable.CompleteRow p |
            reconstructedFirstCode old ⟨ledger, (instruction, _consistent)⟩ row = code} =
          (fun row => codeOfCheckedSample p (sample row)) ⁻¹' {code} := by
        ext row
        simp [reconstructedFirstCode, hdecision, sample, parameters]
      rw [hset]
      exact hevent

/-- Joint measurability of the sampled-outcome/failure code when the actual
ledger, instruction and consistency data vary over their faithful countable
carrier jointly with the complete continuous row. -/
theorem measurable_reconstructedFirstCode
    (old : AssignmentStartPayload.Input p eta) :
    Measurable (fun z : LocalStartInput old × CompletePublicTable.CompleteRow p =>
      reconstructedFirstCode old z.1 z.2) := by
  classical
  apply measurable_to_countable'
  intro code
  change MeasurableSet {z : LocalStartInput old × CompletePublicTable.CompleteRow p |
    reconstructedFirstCode old z.1 z.2 = code}
  have hset :
      {z : LocalStartInput old × CompletePublicTable.CompleteRow p |
        reconstructedFirstCode old z.1 z.2 = code} =
      ⋃ input : LocalStartInput old,
        ({input} : Set (LocalStartInput old)) ×ˢ
          {row : CompletePublicTable.CompleteRow p |
            reconstructedFirstCode old input row = code} := by
    ext ⟨input, row⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨input, rfl, h⟩
    · rintro ⟨input', rfl, h⟩
      exact h
  rw [hset]
  exact MeasurableSet.iUnion fun input =>
    (measurableSet_singleton input).prod
      (measurableSet_reconstructedFirstCode_fiber old input code)
private theorem codeOfResult_finishCheckedSample
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out) :
    codeOfResult p (LaterAssignmentStartOperation.finishCheckedSample
      old ledger instruction row consistent out hcall selection.cutoffReached
      selection.currentWeightPos selection.cutoffWeightPos selection.law
      selection.lawSelected) =
      codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
        selection.law.mass selection.law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) := by
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> simp_all [codeOfResult, codeOfCheckedSample]

/-- The finite code computed directly from the accepted reconstruction-first
pipeline is exactly the code of the complete dependent operation result. -/
theorem laterAssignmentStartCode_eq_reconstructedFirstCode
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row : CompletePublicTable.CompleteRow p) :
    laterAssignmentStartCode old input.1 input.2.1 row input.2.2 =
      reconstructedFirstCode old input row := by
  classical
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction
      old ledger instruction with
  | failure reason =>
      simp [laterAssignmentStartCode, codeOfResult, reconstructedFirstCode,
        LaterAssignmentStartOperation.laterAssignmentStart,
        LaterAssignmentStartOperation.runReconstructionDecision, hdecision]
  | success out hcall =>
      let selection := successfulLawSelection old ledger instruction out hcall
      have hrun : LaterAssignmentStartOperation.laterAssignmentStart
          old ledger instruction row consistent =
        LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
          consistent out hcall selection.cutoffReached selection.currentWeightPos
          selection.cutoffWeightPos selection.law selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hdecision]
        rfl
      calc
        laterAssignmentStartCode old ledger instruction row consistent =
            codeOfResult p (LaterAssignmentStartOperation.finishCheckedSample
              old ledger instruction row consistent out hcall selection.cutoffReached
              selection.currentWeightPos selection.cutoffWeightPos selection.law
              selection.lawSelected) := by
                unfold laterAssignmentStartCode
                rw [hrun]
        _ = codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
              selection.law.mass selection.law.anchor
              (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) :=
          codeOfResult_finishCheckedSample old ledger instruction row consistent out hcall selection
        _ = reconstructedFirstCode old ⟨ledger, (instruction, consistent)⟩ row := by
          simp [reconstructedFirstCode, hdecision, selectedSamplerParameters, selection]

/-- The reconstruction-first code reads the complete requested `K+1` vector
at the instruction time. Equal vectors therefore give equal exact failure or
sampled-outcome codes. -/
theorem reconstructedFirstCode_eq_of_ownAssignmentVector_eq
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector row₁ input.2.1.time =
      LaterAssignmentStartOperation.ownAssignmentVector row₂ input.2.1.time) :
    reconstructedFirstCode old input row₁ = reconstructedFirstCode old input row₂ := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason => simp [reconstructedFirstCode, hdecision]
  | success out hcall => simp [reconstructedFirstCode, hdecision, hvector]

/-- The code projected from the actual dependent operation has the same
`K+1`-vector locality. -/
theorem laterAssignmentStartCode_eq_of_ownAssignmentVector_eq
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector row₁ input.2.1.time =
      LaterAssignmentStartOperation.ownAssignmentVector row₂ input.2.1.time) :
    laterAssignmentStartCode old input.1 input.2.1 row₁ input.2.2 =
      laterAssignmentStartCode old input.1 input.2.1 row₂ input.2.2 := by
  rw [laterAssignmentStartCode_eq_reconstructedFirstCode,
    laterAssignmentStartCode_eq_reconstructedFirstCode]
  exact reconstructedFirstCode_eq_of_ownAssignmentVector_eq old input row₁ row₂ hvector

/-- Exact reconstruction failures are returned without consulting the row;
the code keeps the accepted failure reason. -/
theorem laterAssignmentStartCode_reconstructionFailure
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row : CompletePublicTable.CompleteRow p)
    (reason : AssignmentScoreReconstruction.Failure)
    (hdecision : LaterAssignmentStartOperation.decideReconstruction old input.1 input.2.1 =
      .failure reason) :
    laterAssignmentStartCode old input.1 input.2.1 row input.2.2 =
      .reconstructionFailure reason := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  rw [laterAssignmentStartCode_eq_reconstructedFirstCode old
    ⟨ledger, (instruction, consistent)⟩ row]
  simp [reconstructedFirstCode, hdecision]

/-- Retain the payload projection of the actual operation, when it succeeds.
Its measurable carrier is supplied below with the real anchor coordinates
given their ordinary Borel sigma algebra. -/
def resultPayload?
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    {consistent : LaterAssignmentStartOperation.LocalConsistency old ledger}
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent) :
    Option (AssignmentStartPayload.Input p eta) :=
  match result with
  | .success output _ => some output.payload
  | _ => none

/-- Both non-row values carried for chronological dispatch: the retained
payload and its original reconstructed base-score function. -/
def resultPayloadScore?
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    {consistent : LaterAssignmentStartOperation.LocalConsistency old ledger}
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent) :
    Option (AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ)) :=
  match result with
  | .success output _ => some (output.payload, output.baseScore)
  | _ => none
private noncomputable def payloadScoreOfCheckedSample
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out)
    (sample : CheckedAssignmentSample.Result p) :
    Option (AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ)) :=
  match sample with
  | .sampled outcome =>
      let payload := LaterAssignmentStartOperation.payloadInput old instruction out law
        (CheckedAssignmentOrientation.slowSetAfter p outcome.1.1 outcome.1.2 outcome.2)
      some (payload, LaterAssignmentStartOperation.retainedBaseScore out payload)
  | _ => none
private theorem resultPayloadScore_finish_eq_payloadScoreOfCheckedSample
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out) :
    resultPayloadScore? (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
      row consistent out hcall selection.cutoffReached selection.currentWeightPos
      selection.cutoffWeightPos selection.law selection.lawSelected) =
    payloadScoreOfCheckedSample old ledger instruction out selection.law
      (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) := by
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> simp_all [resultPayloadScore?, payloadScoreOfCheckedSample]
private theorem resultPayloadScore_finish_eq_of_vector_eq
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time) :
    resultPayloadScore? (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
      row₁ consistent out hcall selection.cutoffReached selection.currentWeightPos
      selection.cutoffWeightPos selection.law selection.lawSelected) =
    resultPayloadScore? (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
      row₂ consistent out hcall selection.cutoffReached selection.currentWeightPos
      selection.cutoffWeightPos selection.law selection.lawSelected) := by
  have hsampleEq :
      CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time) =
        CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time) := by
    rw [hvector]
  calc
    _ = payloadScoreOfCheckedSample old ledger instruction out selection.law
        (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time)) :=
      resultPayloadScore_finish_eq_payloadScoreOfCheckedSample old ledger instruction row₁
        consistent out hcall selection
    _ = payloadScoreOfCheckedSample old ledger instruction out selection.law
        (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time)) := by
      rw [hsampleEq]
    _ = _ := (resultPayloadScore_finish_eq_payloadScoreOfCheckedSample old ledger instruction
      row₂ consistent out hcall selection).symm
private noncomputable def payloadOfCheckedSample
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (law : LaterAssignmentStartOperation.SelectedLaw old ledger instruction out)
    (sample : CheckedAssignmentSample.Result p) :
    Option (AssignmentStartPayload.Input p eta) :=
  match sample with
  | .sampled outcome =>
      some (LaterAssignmentStartOperation.payloadInput old instruction out law
        (CheckedAssignmentOrientation.slowSetAfter p outcome.1.1 outcome.1.2 outcome.2))
  | _ => none
private theorem resultPayload_finishCheckedSample_eq_payloadOfCheckedSample
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out) :
    resultPayload? (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
      row consistent out hcall selection.cutoffReached selection.currentWeightPos
      selection.cutoffWeightPos selection.law selection.lawSelected) =
    payloadOfCheckedSample old ledger instruction out selection.law
      (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
        (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) := by
  unfold LaterAssignmentStartOperation.finishCheckedSample
  split <;> simp_all [resultPayload?, payloadOfCheckedSample]
private theorem resultPayload_finishCheckedSample_eq
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time =
      LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time) :
    resultPayload? (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
      row₁ consistent out hcall selection.cutoffReached selection.currentWeightPos
      selection.cutoffWeightPos selection.law selection.lawSelected) =
    resultPayload? (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
      row₂ consistent out hcall selection.cutoffReached selection.currentWeightPos
      selection.cutoffWeightPos selection.law selection.lawSelected) := by
  have hsampleEq :
      CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time) =
        CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time) := by
    rw [hvector]
  calc
    _ = payloadOfCheckedSample old ledger instruction out selection.law
        (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time)) :=
      resultPayload_finishCheckedSample_eq_payloadOfCheckedSample old ledger instruction row₁
        consistent out hcall selection
    _ = payloadOfCheckedSample old ledger instruction out selection.law
        (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time)) := by
      rw [hsampleEq]
    _ = _ := (resultPayload_finishCheckedSample_eq_payloadOfCheckedSample old ledger instruction
      row₂ consistent out hcall selection).symm

/-- The actual operation's non-row payload projection is invariant under
equality of its entire requested assignment vector. -/
theorem laterAssignmentStart_payload?_eq_of_ownAssignmentVector_eq
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector row₁ input.2.1.time =
      LaterAssignmentStartOperation.ownAssignmentVector row₂ input.2.1.time) :
    resultPayload? (LaterAssignmentStartOperation.laterAssignmentStart
      old input.1 input.2.1 row₁ input.2.2) =
    resultPayload? (LaterAssignmentStartOperation.laterAssignmentStart
      old input.1 input.2.1 row₂ input.2.2) := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason => simp [resultPayload?, LaterAssignmentStartOperation.laterAssignmentStart,
      LaterAssignmentStartOperation.runReconstructionDecision, hdecision]
  | success out hcall =>
      have hvector' : LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time =
          LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time := by
        simpa using hvector
      let selection := successfulLawSelection old ledger instruction out hcall
      have hrun₁ : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction
          row₁ consistent = LaterAssignmentStartOperation.finishCheckedSample old ledger
            instruction row₁ consistent out hcall selection.cutoffReached
            selection.currentWeightPos selection.cutoffWeightPos selection.law
            selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hdecision]
        rfl
      have hrun₂ : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction
          row₂ consistent = LaterAssignmentStartOperation.finishCheckedSample old ledger
            instruction row₂ consistent out hcall selection.cutoffReached
            selection.currentWeightPos selection.cutoffWeightPos selection.law
            selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hdecision]
        rfl
      rw [hrun₁, hrun₂]
      exact resultPayload_finishCheckedSample_eq old ledger instruction row₁ row₂
        consistent out hcall selection hvector'

/-- The base score accompanying the original payload has the same full-vector
locality as the payload itself. -/
theorem laterAssignmentStart_payloadAndBaseScore?_eq_of_ownAssignmentVector_eq
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old)
    (row₁ row₂ : CompletePublicTable.CompleteRow p)
    (hvector : LaterAssignmentStartOperation.ownAssignmentVector row₁ input.2.1.time =
      LaterAssignmentStartOperation.ownAssignmentVector row₂ input.2.1.time) :
    resultPayloadScore? (LaterAssignmentStartOperation.laterAssignmentStart
      old input.1 input.2.1 row₁ input.2.2) =
    resultPayloadScore? (LaterAssignmentStartOperation.laterAssignmentStart
      old input.1 input.2.1 row₂ input.2.2) := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason =>
      simp [resultPayloadScore?, LaterAssignmentStartOperation.laterAssignmentStart,
        LaterAssignmentStartOperation.runReconstructionDecision, hdecision]
  | success out hcall =>
      have hvector' : LaterAssignmentStartOperation.ownAssignmentVector row₁ instruction.time =
          LaterAssignmentStartOperation.ownAssignmentVector row₂ instruction.time := by
        simpa using hvector
      let selection := successfulLawSelection old ledger instruction out hcall
      have hrun₁ : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction
          row₁ consistent = LaterAssignmentStartOperation.finishCheckedSample old ledger
            instruction row₁ consistent out hcall selection.cutoffReached
            selection.currentWeightPos selection.cutoffWeightPos selection.law
            selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hdecision]
        rfl
      have hrun₂ : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction
          row₂ consistent = LaterAssignmentStartOperation.finishCheckedSample old ledger
            instruction row₂ consistent out hcall selection.cutoffReached
            selection.currentWeightPos selection.cutoffWeightPos selection.law
            selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hdecision]
        rfl
      rw [hrun₁, hrun₂]
      exact resultPayloadScore_finish_eq_of_vector_eq old ledger instruction row₁ row₂
        consistent out hcall selection hvector'
noncomputable def decodeAfterSuccessful
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out)
    (code : LaterAssignmentStartCode p) :
    Option (LaterAssignmentStartOperation.Result old ledger instruction row consistent) := by
  classical
  cases code with
  | reconstructionFailure _ => exact none
  | prefixFailure arm reason =>
      exact if h : CheckedAssignmentSample.checkedAssignmentSample p
          selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
            .prefixFailure arm reason then
        some (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
          row consistent out hcall selection.cutoffReached selection.currentWeightPos
          selection.cutoffWeightPos selection.law selection.lawSelected) else none
  | orientationFailure set =>
      exact if h : CheckedAssignmentSample.checkedAssignmentSample p
          selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
            .orientationFailure set then
        some (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
          row consistent out hcall selection.cutoffReached selection.currentWeightPos
          selection.cutoffWeightPos selection.law selection.lawSelected) else none
  | sampled outcome =>
      exact if h : CheckedAssignmentSample.checkedAssignmentSample p
          selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
            .sampled outcome then
        some (LaterAssignmentStartOperation.finishCheckedSample old ledger
          instruction row consistent out hcall selection.cutoffReached
          selection.currentWeightPos selection.cutoffWeightPos selection.law
          selection.lawSelected) else none
private theorem decodeAfterSuccessful_prefixFailure
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
    (hsample : CheckedAssignmentSample.checkedAssignmentSample p
      selection.law.mass selection.law.anchor
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
        .prefixFailure arm reason) :
    decodeAfterSuccessful old ledger instruction row consistent out hcall selection
      (.prefixFailure arm reason) = some (LaterAssignmentStartOperation.finishCheckedSample old
        ledger instruction row consistent out hcall selection.cutoffReached
        selection.currentWeightPos selection.cutoffWeightPos selection.law
        selection.lawSelected) := by
  classical
  simp [decodeAfterSuccessful, hsample]
private theorem decodeAfterSuccessful_orientationFailure
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out)
    (set : PrefixSetSampler.SetCarrier p.K p.m)
    (hsample : CheckedAssignmentSample.checkedAssignmentSample p
      selection.law.mass selection.law.anchor
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
        .orientationFailure set) :
    decodeAfterSuccessful old ledger instruction row consistent out hcall selection
      (.orientationFailure set) = some (LaterAssignmentStartOperation.finishCheckedSample old
        ledger instruction row consistent out hcall selection.cutoffReached
        selection.currentWeightPos selection.cutoffWeightPos selection.law
        selection.lawSelected) := by
  classical
  simp [decodeAfterSuccessful, hsample]
private theorem decodeAfterSuccessful_sampled
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (selection : SuccessfulLawSelection old ledger instruction out)
    (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m)
    (hsample : CheckedAssignmentSample.checkedAssignmentSample p
      selection.law.mass selection.law.anchor
      (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) =
        .sampled outcome) :
    decodeAfterSuccessful old ledger instruction row consistent out hcall selection
      (.sampled outcome) = some (LaterAssignmentStartOperation.finishCheckedSample old
        ledger instruction row consistent out hcall selection.cutoffReached
        selection.currentWeightPos selection.cutoffWeightPos selection.law
        selection.lawSelected) := by
  classical
  simp [decodeAfterSuccessful, hsample]

/-- Decode after the reconstruction decision has been selected. Only a code
matching the literal branch decodes. The sampled case rebuilds the full
dependent success payload from the recorded outcome and verbatim row. -/
noncomputable def decodeAfterReconstruction
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (decision : LaterAssignmentStartOperation.ReconstructionDecision old ledger instruction)
    (code : LaterAssignmentStartCode p) :
    Option (LaterAssignmentStartOperation.Result old ledger instruction row consistent) := by
  classical
  cases decision with
  | failure reason =>
      cases code with
      | reconstructionFailure encodedReason =>
          exact if h : encodedReason = reason then
            some (.reconstructionFailure encodedReason) else none
      | prefixFailure _ _ => exact none
      | orientationFailure _ => exact none
      | sampled _ => exact none
  | success out hcall =>
      let selection := successfulLawSelection old ledger instruction out hcall
      exact decodeAfterSuccessful old ledger instruction row consistent out hcall
        selection code

/-- Decode a countable code using the original local inputs and complete row. -/
noncomputable def decodeLaterAssignmentStart
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (code : LaterAssignmentStartCode p) :
    Option (LaterAssignmentStartOperation.Result old ledger instruction row consistent) :=
  decodeAfterReconstruction old ledger instruction row consistent
    (LaterAssignmentStartOperation.decideReconstruction old ledger instruction) code
private theorem decodeAfterReconstruction_codeOfResult
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger)
    (decision : LaterAssignmentStartOperation.ReconstructionDecision old ledger instruction) :
    decodeAfterReconstruction old ledger instruction row consistent decision
      (codeOfResult p (LaterAssignmentStartOperation.runReconstructionDecision
        old ledger instruction row consistent decision)) =
      some (LaterAssignmentStartOperation.runReconstructionDecision
        old ledger instruction row consistent decision) := by
  classical
  cases decision with
  | failure reason =>
      have hcode : codeOfResult p (LaterAssignmentStartOperation.runReconstructionDecision
          old ledger instruction row consistent (.failure reason)) =
          .reconstructionFailure reason := rfl
      rw [hcode]
      simp [decodeAfterReconstruction,
        LaterAssignmentStartOperation.runReconstructionDecision]
  | success out hcall =>
      let selection := successfulLawSelection old ledger instruction out hcall
      have hrun : LaterAssignmentStartOperation.runReconstructionDecision old ledger
          instruction row consistent (.success out hcall) =
        LaterAssignmentStartOperation.finishCheckedSample old ledger instruction row
          consistent out hcall selection.cutoffReached selection.currentWeightPos
          selection.cutoffWeightPos selection.law selection.lawSelected := by
        rfl
      cases hsample : CheckedAssignmentSample.checkedAssignmentSample p
          selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) with
      | prefixFailure arm reason =>
          have hcode : codeOfResult p (LaterAssignmentStartOperation.finishCheckedSample
              old ledger instruction row consistent out hcall selection.cutoffReached
              selection.currentWeightPos selection.cutoffWeightPos selection.law
              selection.lawSelected) = .prefixFailure arm reason := by
            calc
              _ = codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
                    selection.law.mass selection.law.anchor
                    (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) :=
                codeOfResult_finishCheckedSample old ledger instruction row consistent out hcall selection
              _ = .prefixFailure arm reason := by rw [hsample]; rfl
          rw [hrun, hcode]
          change decodeAfterSuccessful old ledger instruction row consistent out hcall
            selection (.prefixFailure arm reason) =
              some (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
                row consistent out hcall selection.cutoffReached selection.currentWeightPos
                selection.cutoffWeightPos selection.law selection.lawSelected)
          have hdecode := decodeAfterSuccessful_prefixFailure old ledger instruction row
            consistent out hcall selection arm reason hsample
          exact hdecode
      | orientationFailure set =>
          have hcode : codeOfResult p (LaterAssignmentStartOperation.finishCheckedSample
              old ledger instruction row consistent out hcall selection.cutoffReached
              selection.currentWeightPos selection.cutoffWeightPos selection.law
              selection.lawSelected) = .orientationFailure set := by
            calc
              _ = codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
                    selection.law.mass selection.law.anchor
                    (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) :=
                codeOfResult_finishCheckedSample old ledger instruction row consistent out hcall selection
              _ = .orientationFailure set := by rw [hsample]; rfl
          rw [hrun, hcode]
          change decodeAfterSuccessful old ledger instruction row consistent out hcall
            selection (.orientationFailure set) =
              some (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
                row consistent out hcall selection.cutoffReached selection.currentWeightPos
                selection.cutoffWeightPos selection.law selection.lawSelected)
          have hdecode := decodeAfterSuccessful_orientationFailure old ledger instruction row
            consistent out hcall selection set hsample
          exact hdecode
      | sampled outcome =>
          have hcode : codeOfResult p (LaterAssignmentStartOperation.finishCheckedSample
              old ledger instruction row consistent out hcall selection.cutoffReached
              selection.currentWeightPos selection.cutoffWeightPos selection.law
              selection.lawSelected) = .sampled outcome := by
            calc
              _ = codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
                    selection.law.mass selection.law.anchor
                    (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) :=
                codeOfResult_finishCheckedSample old ledger instruction row consistent out hcall selection
              _ = .sampled outcome := by rw [hsample]; rfl
          rw [hrun, hcode]
          change decodeAfterSuccessful old ledger instruction row consistent out hcall
            selection (.sampled outcome) =
              some (LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
                row consistent out hcall selection.cutoffReached selection.currentWeightPos
                selection.cutoffWeightPos selection.law selection.lawSelected)
          exact decodeAfterSuccessful_sampled old ledger instruction row consistent out
            hcall selection outcome hsample

/-- The actual operation code decodes losslessly to `some` of the entire
dependent result. This preserves the exact failure payload and, on success,
the original `K+1` assignment vector, real payload anchor, base scores, and all
equality fields (up to proof irrelevance). -/
theorem decodeLaterAssignmentStart_exact
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : AssignmentStartInstruction p)
    (row : CompletePublicTable.CompleteRow p)
    (consistent : LaterAssignmentStartOperation.LocalConsistency old ledger) :
    decodeLaterAssignmentStart old ledger instruction row consistent
      (laterAssignmentStartCode old ledger instruction row consistent) =
        some (LaterAssignmentStartOperation.laterAssignmentStart
          old ledger instruction row consistent) := by
  simpa [decodeLaterAssignmentStart, laterAssignmentStartCode, codeOfResult,
    LaterAssignmentStartOperation.laterAssignmentStart] using
    (decodeAfterReconstruction_codeOfResult old ledger instruction row consistent
      (LaterAssignmentStartOperation.decideReconstruction old ledger instruction))

/-- Joint measurability of the code of the actual accepted operation. -/
noncomputable def laterAssignmentStartCodeMap
    (old : AssignmentStartPayload.Input p eta) :
    LocalStartInput old × CompletePublicTable.CompleteRow p → LaterAssignmentStartCode p :=
  fun z => laterAssignmentStartCode old z.1.1 z.1.2.1 z.2 z.1.2.2
theorem measurable_laterAssignmentStartCode
    (old : AssignmentStartPayload.Input p eta) :
    Measurable (laterAssignmentStartCodeMap old) := by
  have hcode := measurable_reconstructedFirstCode (p := p) (eta := eta) old
  have heq : laterAssignmentStartCodeMap old =
      (fun z => reconstructedFirstCode old z.1 z.2) := by
    funext z
    exact laterAssignmentStartCode_eq_reconstructedFirstCode old z.1 z.2
  rw [heq]
  exact hcode

/-- Payload chosen from an exact operation code and its original local input.
Only the sampled outcome comes from the row-dependent code; the anchor and
queue coordinates come from literal reconstruction and law selection. -/
noncomputable def payloadOfCode
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old) (code : LaterAssignmentStartCode p) :
    Option (AssignmentStartPayload.Input p eta) :=
  match code with
  | .sampled outcome =>
      match input with
      | ⟨ledger, (instruction, _consistent)⟩ =>
          match LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
          | .failure _ => none
          | .success out hcall =>
              let selection := successfulLawSelection old ledger instruction out hcall
              some (LaterAssignmentStartOperation.payloadInput old instruction out
                selection.law (CheckedAssignmentOrientation.slowSetAfter p
                  outcome.1.1 outcome.1.2 outcome.2))
  | _ => none

/-- The actual result's payload projection, when present. -/
noncomputable def laterAssignmentStartPayload?Map
    (old : AssignmentStartPayload.Input p eta)
    (z : LocalStartInput old × CompletePublicTable.CompleteRow p) :
    Option (AssignmentStartPayload.Input p eta) :=
  resultPayload? (LaterAssignmentStartOperation.laterAssignmentStart
    old z.1.1 z.1.2.1 z.2 z.1.2.2)

/-- The payload is exactly recovered from the actual operation code, retaining
the real anchor in the Borel payload carrier. -/
theorem laterAssignmentStartPayload?_eq_payloadOfCode
    (old : AssignmentStartPayload.Input p eta)
    (z : LocalStartInput old × CompletePublicTable.CompleteRow p) :
    laterAssignmentStartPayload?Map old z =
      payloadOfCode old z.1 (laterAssignmentStartCodeMap old z) := by
  cases z with
  | mk input row =>
    cases input with
    | mk ledger pair =>
      cases pair with
      | mk instruction consistent =>
        change resultPayload? (LaterAssignmentStartOperation.laterAssignmentStart
            old ledger instruction row consistent) =
          payloadOfCode old ⟨ledger, (instruction, consistent)⟩
            (laterAssignmentStartCode old ledger instruction row consistent)
        cases hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
        | failure reason =>
            have hcode : laterAssignmentStartCode old ledger instruction row consistent =
                .reconstructionFailure reason := by
              unfold laterAssignmentStartCode
              simp [LaterAssignmentStartOperation.laterAssignmentStart,
                LaterAssignmentStartOperation.runReconstructionDecision, codeOfResult, hdecision]
            have hresult : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction
                row consistent = .reconstructionFailure reason := by
              unfold LaterAssignmentStartOperation.laterAssignmentStart
              simp [LaterAssignmentStartOperation.runReconstructionDecision, hdecision]
            rw [hresult, hcode]
            simp [resultPayload?, payloadOfCode]
        | success out hcall =>
            let selection := successfulLawSelection old ledger instruction out hcall
            have hrun : LaterAssignmentStartOperation.laterAssignmentStart old ledger instruction
                row consistent = LaterAssignmentStartOperation.finishCheckedSample old ledger instruction
                  row consistent out hcall selection.cutoffReached selection.currentWeightPos
                  selection.cutoffWeightPos selection.law selection.lawSelected := by
              unfold LaterAssignmentStartOperation.laterAssignmentStart
              rw [hdecision]
              rfl
            have hcode : laterAssignmentStartCode old ledger instruction row consistent =
                codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
                  selection.law.mass selection.law.anchor
                  (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) := by
              unfold laterAssignmentStartCode
              rw [hrun]
              exact codeOfResult_finishCheckedSample old ledger instruction row consistent out hcall selection
            rw [hrun, resultPayload_finishCheckedSample_eq_payloadOfCheckedSample]
            change payloadOfCheckedSample old ledger instruction out selection.law
                (CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass selection.law.anchor
                  (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)) =
              payloadOfCode old ⟨ledger, (instruction, consistent)⟩
                (laterAssignmentStartCode old ledger instruction row consistent)
            cases hsample : CheckedAssignmentSample.checkedAssignmentSample p selection.law.mass
                selection.law.anchor (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time)
            · simp [payloadOfCheckedSample, codeOfCheckedSample, hsample, hcode, payloadOfCode]
            · simp [payloadOfCheckedSample, codeOfCheckedSample, hsample, hcode, payloadOfCode]
            · simp [payloadOfCheckedSample, codeOfCheckedSample, hsample, hcode, payloadOfCode,
                hdecision, selection]
def laterAssignmentStartPayloadSourceSet
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old) (code : LaterAssignmentStartCode p) :
    Set (LocalStartInput old × CompletePublicTable.CompleteRow p) :=
  {z | z.1 = input ∧ laterAssignmentStartCodeMap old z = code}
def laterAssignmentStartPayloadFiberSet
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old) (code : LaterAssignmentStartCode p) :
    Set (AssignmentStartPayload.Input p eta) :=
  {value | payloadOfCode old input code = some value}
def laterAssignmentStartPayloadGraphSet
    (old : AssignmentStartPayload.Input p eta) :
    Set ((LocalStartInput old × CompletePublicTable.CompleteRow p) ×
      AssignmentStartPayload.Input p eta) :=
  {q | laterAssignmentStartPayload?Map old q.1 = some q.2}
theorem measurableSet_laterAssignmentStartPayloadSource
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old) (code : LaterAssignmentStartCode p) :
    MeasurableSet (laterAssignmentStartPayloadSourceSet old input code) := by
  change MeasurableSet {z : LocalStartInput old × CompletePublicTable.CompleteRow p |
    z.1 = input ∧ laterAssignmentStartCodeMap old z = code}
  exact ((measurableSet_singleton input).preimage measurable_fst).inter
    (measurable_laterAssignmentStartCode old (measurableSet_singleton code))
theorem measurableSet_laterAssignmentStartPayloadFiber
    (old : AssignmentStartPayload.Input p eta)
    (input : LocalStartInput old) (code : LaterAssignmentStartCode p) :
    MeasurableSet (laterAssignmentStartPayloadFiberSet old input code) := by
  cases h : payloadOfCode old input code with
  | none => simp [laterAssignmentStartPayloadFiberSet, h]
  | some value =>
      rw [show laterAssignmentStartPayloadFiberSet old input code = {value} by
        simp [laterAssignmentStartPayloadFiberSet, h]]
      exact measurableSet_singleton_payload value
theorem measurableSet_laterAssignmentStartPayloadGraph
    (old : AssignmentStartPayload.Input p eta) :
    MeasurableSet (laterAssignmentStartPayloadGraphSet old) := by
  have hset : laterAssignmentStartPayloadGraphSet old =
      ⋃ input : LocalStartInput old, ⋃ code : LaterAssignmentStartCode p,
        laterAssignmentStartPayloadSourceSet old input code ×ˢ
          laterAssignmentStartPayloadFiberSet old input code := by
    ext ⟨z, value⟩
    simp only [laterAssignmentStartPayloadGraphSet, Set.mem_ofPred_eq,
      Set.mem_iUnion, Set.mem_prod]
    constructor
    · intro h
      refine ⟨z.1, laterAssignmentStartCodeMap old z, ?_, ?_⟩
      · exact ⟨rfl, rfl⟩
      · have hactual := laterAssignmentStartPayload?_eq_payloadOfCode old z
        rw [hactual] at h
        exact h
    · rintro ⟨input, code, ⟨hinput, hcode⟩, hpayload⟩
      subst input
      have hactual := laterAssignmentStartPayload?_eq_payloadOfCode old z
      rw [hcode] at hactual
      exact hactual.trans hpayload
  rw [hset]
  exact MeasurableSet.iUnion fun input => MeasurableSet.iUnion fun code =>
    (measurableSet_laterAssignmentStartPayloadSource old input code).prod
      (measurableSet_laterAssignmentStartPayloadFiber old input code)
def laterAssignmentStartSuccessCodeSet (p : ConstructorDimensions.Parameters) :
    Set (LaterAssignmentStartCode p) :=
  Set.range (LaterAssignmentStartCode.sampled (p := p))
def laterAssignmentStartSuccessSet
    (old : AssignmentStartPayload.Input p eta) :
    Set (LocalStartInput old × CompletePublicTable.CompleteRow p) :=
  (laterAssignmentStartCodeMap old) ⁻¹' laterAssignmentStartSuccessCodeSet p
theorem measurableSet_laterAssignmentStartSuccess
    (old : AssignmentStartPayload.Input p eta) :
    MeasurableSet (laterAssignmentStartSuccessSet old) := by
  exact measurable_laterAssignmentStartCode old MeasurableSet.of_discrete
def laterAssignmentStartReconstructionFailureSet
    (old : AssignmentStartPayload.Input p eta)
    (reason : AssignmentScoreReconstruction.Failure) :
    Set (LocalStartInput old × CompletePublicTable.CompleteRow p) :=
  {z | laterAssignmentStartCodeMap old z = .reconstructionFailure reason}
theorem measurableSet_laterAssignmentStartReconstructionFailure
    (old : AssignmentStartPayload.Input p eta)
    (reason : AssignmentScoreReconstruction.Failure) :
    MeasurableSet (laterAssignmentStartReconstructionFailureSet old reason) := by
  exact (measurable_laterAssignmentStartCode old)
    (measurableSet_singleton (.reconstructionFailure reason))
def laterAssignmentStartPrefixFailureSet
    (old : AssignmentStartPayload.Input p eta)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason) :
    Set (LocalStartInput old × CompletePublicTable.CompleteRow p) :=
  {z | laterAssignmentStartCodeMap old z = .prefixFailure arm reason}
theorem measurableSet_laterAssignmentStartPrefixFailure
    (old : AssignmentStartPayload.Input p eta)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason) :
    MeasurableSet (laterAssignmentStartPrefixFailureSet old arm reason) := by
  exact (measurable_laterAssignmentStartCode old)
    (measurableSet_singleton (.prefixFailure arm reason))
def laterAssignmentStartOrientationFailureSet
    (old : AssignmentStartPayload.Input p eta)
    (set : PrefixSetSampler.SetCarrier p.K p.m) :
    Set (LocalStartInput old × CompletePublicTable.CompleteRow p) :=
  {z | laterAssignmentStartCodeMap old z = .orientationFailure set}
theorem measurableSet_laterAssignmentStartOrientationFailure
    (old : AssignmentStartPayload.Input p eta)
    (set : PrefixSetSampler.SetCarrier p.K p.m) :
    MeasurableSet (laterAssignmentStartOrientationFailureSet old set) := by
  exact (measurable_laterAssignmentStartCode old)
    (measurableSet_singleton (.orientationFailure set))
def slowSetErasureOfCode (code : LaterAssignmentStartCode p) : Finset (Fin p.K) :=
  match code with
  | .sampled outcome =>
      (CheckedAssignmentOrientation.slowSetAfter p outcome.1.1 outcome.1.2 outcome.2).1
  | _ => ∅
theorem measurable_slowSetErasureOfCode :
    Measurable (slowSetErasureOfCode (p := p)) :=
  Measurable.of_discrete
def laterAssignmentStartSlowSetGraphSet
    (old : AssignmentStartPayload.Input p eta) :
    Set ((LocalStartInput old × CompletePublicTable.CompleteRow p) × Finset (Fin p.K)) :=
  {q | q.1 ∈ laterAssignmentStartSuccessSet old ∧
    q.2 = slowSetErasureOfCode (laterAssignmentStartCodeMap old q.1)}
theorem measurableSet_laterAssignmentStartSlowSetGraph
    (old : AssignmentStartPayload.Input p eta) :
    MeasurableSet (laterAssignmentStartSlowSetGraphSet old) := by
  let slowMap (z : LocalStartInput old × CompletePublicTable.CompleteRow p) :=
    slowSetErasureOfCode (laterAssignmentStartCodeMap old z)
  have hcode := measurable_laterAssignmentStartCode old
  have hslow : Measurable slowMap := measurable_slowSetErasureOfCode.comp hcode
  have hgraph : MeasurableSet {q :
      (LocalStartInput old × CompletePublicTable.CompleteRow p) × Finset (Fin p.K) |
        q.2 = slowMap q.1} :=
    measurableSet_eq_fun measurable_snd (hslow.comp measurable_fst)
  have hsuccess : MeasurableSet {q :
      (LocalStartInput old × CompletePublicTable.CompleteRow p) × Finset (Fin p.K) |
        q.1 ∈ laterAssignmentStartSuccessSet old} :=
    (measurableSet_laterAssignmentStartSuccess old).preimage measurable_fst
  have hset : laterAssignmentStartSlowSetGraphSet old =
      {q | q.1 ∈ laterAssignmentStartSuccessSet old} ∩
        {q | q.2 = slowMap q.1} := by
    rfl
  rw [hset]
  exact hsuccess.inter hgraph
theorem successful_slowSet_matches_code
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row) :
    output.slowSet.1 = slowSetErasureOfCode (.sampled output.outcome) := by
  simp [slowSetErasureOfCode, CheckedAssignmentOrientation.slowSetAfter_val]
  exact LaterAssignmentStartOperation.successfulSlowSet_eq_erase output
def laterAssignmentStartAssignmentVectorGraphSet
    (old : AssignmentStartPayload.Input p eta) :
    Set (LocalStartInput old ×
      (CompletePublicTable.CompleteRow p × CheckedAssignmentSample.AssignmentVector p)) :=
  {q | q.2.2 = LaterAssignmentStartOperation.ownAssignmentVector
      q.2.1 q.1.2.1.time ∧
    laterAssignmentStartCodeMap old (q.1, q.2.1) ∈
      laterAssignmentStartSuccessCodeSet p}
theorem measurableSet_laterAssignmentStartAssignmentVectorGraph
    (old : AssignmentStartPayload.Input p eta) :
    MeasurableSet (laterAssignmentStartAssignmentVectorGraphSet old) := by
  let domain := LocalStartInput old × CompletePublicTable.CompleteRow p
  let hmap := measurable_laterAssignmentStartCode old
  have hbase : Measurable (fun q : LocalStartInput old ×
      (CompletePublicTable.CompleteRow p × CheckedAssignmentSample.AssignmentVector p) =>
        (q.1, q.2.1)) := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hcode := hmap.comp hbase
  have hcodeSet : MeasurableSet (laterAssignmentStartSuccessCodeSet p) :=
    MeasurableSet.of_discrete
  have hsuccess : MeasurableSet {q : LocalStartInput old ×
      (CompletePublicTable.CompleteRow p × CheckedAssignmentSample.AssignmentVector p) |
        laterAssignmentStartCodeMap old (q.1, q.2.1) ∈
          laterAssignmentStartSuccessCodeSet p} := hcode hcodeSet
  have hgraphSet : {q : LocalStartInput old ×
      (CompletePublicTable.CompleteRow p × CheckedAssignmentSample.AssignmentVector p) |
        q.2.2 = LaterAssignmentStartOperation.ownAssignmentVector
          q.2.1 q.1.2.1.time} =
      ⋃ input : LocalStartInput old,
        ({input} : Set (LocalStartInput old)) ×ˢ
          {rv : CompletePublicTable.CompleteRow p × CheckedAssignmentSample.AssignmentVector p |
            rv.2 = LaterAssignmentStartOperation.ownAssignmentVector rv.1 input.2.1.time} := by
    ext ⟨input, ⟨row, vector⟩⟩
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · intro h
      exact ⟨input, rfl, h⟩
    · rintro ⟨input', rfl, h⟩
      exact h
  have hvector : MeasurableSet {q : LocalStartInput old ×
      (CompletePublicTable.CompleteRow p × CheckedAssignmentSample.AssignmentVector p) |
        q.2.2 = LaterAssignmentStartOperation.ownAssignmentVector
          q.2.1 q.1.2.1.time} := by
    rw [hgraphSet]
    apply MeasurableSet.iUnion
    intro input
    apply (measurableSet_singleton input).prod
    exact measurableSet_eq_fun measurable_snd
      ((measurable_ownAssignmentVector input.2.1.time).comp measurable_fst)
  have hset : laterAssignmentStartAssignmentVectorGraphSet old =
      {q | q.2.2 = LaterAssignmentStartOperation.ownAssignmentVector
        q.2.1 q.1.2.1.time} ∩
      {q | laterAssignmentStartCodeMap old (q.1, q.2.1) ∈
        laterAssignmentStartSuccessCodeSet p} := by
    rfl
  rw [hset]
  exact hvector.inter hsuccess
theorem successful_assignmentVector_is_original_row_projection
    {old : AssignmentStartPayload.Input p eta}
    {ledger : LaterAssignmentStartOperation.LocalLedger old}
    {instruction : AssignmentStartInstruction p}
    {row : CompletePublicTable.CompleteRow p}
    (output : LaterAssignmentStartOperation.SuccessfulStart old ledger instruction row) :
    output.assignmentVector = LaterAssignmentStartOperation.ownAssignmentVector row instruction.time :=
  output.assignmentVector_eq_row_projection
