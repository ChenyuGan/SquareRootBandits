/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.LaterAssignmentAnchorMeasurability

/-!
# Varying-anchor measurability of the actual later-start parameters and code

Sources: `sources/zip4/manuscript/06_interruptions.tex:16-61,80-100`,
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:8-14`.

The attained discrete slices and the positive anchor use the accepted joint
carrier and comap sigma algebra. Reconstruction is unchanged by reanchoring.
On each slice corrected masses are constant and the retained anchor varies
continuously; renewal uses only the reconstructed current weights. These are
identities of the actual selected parameters, including their absent branch.

This is internal local mathematics. Physical provenance, physical score truth,
corrected feasibility, adaptive laws and full execution are separate obligations.
NEXT consumer: joint measurability of successful payloads, rates, auxiliary arms
and output observations; a countable result code alone does not establish it.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.LaterAssignmentAnchorMeasurability
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.LaterAssignmentJointCodeMeasurability

variable {p : ConstructorDimensions.Parameters}
variable {eta : ReferencePrelaunchFollower.LearningRate}

local instance checkedResultMeasurableSpace :
    MeasurableSpace (CheckedAssignmentSample.Result p) := ⊤

local instance checkedResultDiscrete :
    DiscreteMeasurableSpace (CheckedAssignmentSample.Result p) := ⟨fun _ => trivial⟩

/-- Reanchoring preserves the complete discrete code, including consistency
data. No reconstruction or successful-law assumption is required. -/
theorem localStartInputCode_transport
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) :
    localStartInputCode (transportLocalStartInput old anchor input) =
      localStartInputCode input := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  rfl

/-- The ledger type changes only in proof indices when the real anchor changes.
The runtime ledger, and hence its complete reconstruction call, are identical. -/
theorem reconstructLaterStart_transport
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) :
    AssignmentScoreReconstruction.reconstructLaterStart
        (transportLocalStartInput old anchor input).1
        (transportLocalStartInput old anchor input).2.1 =
      AssignmentScoreReconstruction.reconstructLaterStart input.1 input.2.1 := by
  rfl

private theorem decideFromCall_payloadWithAnchor
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (call : ReconstructionCall old ledger instruction) :
    decideFromCall (payloadWithAnchor old anchor) ledger instruction
        ⟨call.result, call.call⟩ =
      match decideFromCall old ledger instruction call with
      | .failure reason => .failure reason
      | .success out hcall => .success out hcall := by
  rcases call with ⟨result, hcall⟩
  cases result <;> rfl

/-- Transport the existing decision's proof-indexed successful output. The
anchor does not occur in any ledger data or reconstruction computation. -/
theorem decideReconstruction_payloadWithAnchor
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p) :
    decideReconstruction (payloadWithAnchor old anchor) ledger instruction =
      match decideReconstruction old ledger instruction with
      | .failure reason => .failure reason
      | .success out hcall => .success out hcall := by
  exact decideFromCall_payloadWithAnchor old anchor ledger instruction
    ⟨AssignmentScoreReconstruction.reconstructLaterStart ledger instruction, rfl⟩

/-- Literal corrected parameters of a successful reconstruction. The previous
vector is an explicit conditional input here; the slice proof below obtains
its presence from the actual selected law. -/
theorem selectedSamplerParameters_corrected
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out)
    (hkind : instruction.kind = .corrected)
    (previous : Fin p.K → ℝ)
    (hpresent : AssignmentScoreReconstruction.previousWeight out = some previous) :
    selectedSamplerParameters old ledger instruction out hcall =
      (correctedRawMass old ledger instruction out previous
        (successfulLawSelection old ledger instruction out hcall).cutoffReached,
        old.anchor) := by
  let selection := successfulLawSelection old ledger instruction out hcall
  have hs := selection.lawSelected
  simp only [selectLaw?, hkind, hpresent] at hs
  exact congrArg (fun law => (law.mass, law.anchor)) (Option.some.inj hs).symm

/-- On one actual successful reconstruction, changing the retained positive
anchor changes the selected parameters continuously. Corrected mass uses the
literal current/cutoff/previous Q and kappa; renewal never reads previousWeight.
The success equation is an explicit conditional helper input, not a premise of
the unconditional joint producer below. -/
theorem continuous_selectedSamplerParameters_withAnchor
    (old : AssignmentStartPayload.Input p eta)
    (ledger : LaterAssignmentStartOperation.LocalLedger old)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (out : AssignmentScoreReconstruction.ReconstructedStart ledger instruction)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart ledger instruction =
      .success ledger instruction out) :
    Continuous (fun anchor : PositiveAnchor p =>
      selectedSamplerParameters (payloadWithAnchor old anchor)
        ledger instruction out hcall) := by
  classical
  let selection := successfulLawSelection old ledger instruction out hcall
  cases hkind : instruction.kind with
  | first =>
      have hs := selection.lawSelected
      simp only [selectLaw?, hkind] at hs
      cases hs
  | corrected =>
      obtain ⟨previous, hpresent, _, _⟩ := selectLaw?_corrected_spec old ledger
        instruction out selection.cutoffReached selection.currentWeightPos
        selection.law selection.lawSelected hkind
      have heq : (fun anchor : PositiveAnchor p =>
          selectedSamplerParameters (payloadWithAnchor old anchor)
            ledger instruction out hcall) =
          (fun anchor : PositiveAnchor p =>
            (correctedRawMass old ledger instruction out previous
              selection.cutoffReached, anchor.1)) := by
        funext anchor
        exact selectedSamplerParameters_corrected (payloadWithAnchor old anchor)
          ledger instruction out hcall hkind previous hpresent
      rw [heq]
      exact continuous_const.prodMk continuous_subtype_val
  | renewal =>
      have heq : (fun anchor : PositiveAnchor p =>
          selectedSamplerParameters (payloadWithAnchor old anchor)
            ledger instruction out hcall) =
          (fun _ : PositiveAnchor p =>
            (renewalRawMass out, AssignmentScoreReconstruction.currentWeight out)) := by
        funext anchor
        obtain ⟨ha, hm⟩ := selectedSamplerParameters_renewal
          (payloadWithAnchor old anchor) ledger instruction out hcall hkind
        exact Prod.ext (funext hm) ha
      rw [heq]
      exact continuous_const

private theorem measurable_some_parameters :
    Measurable (some :
      (CheckedAssignmentJointMeasurability.RawMass p ×
        CheckedAssignmentJointMeasurability.Anchor p) → Option
      (CheckedAssignmentJointMeasurability.RawMass p ×
        CheckedAssignmentJointMeasurability.Anchor p)) := by
  apply measurable_comap_iff.mpr
  exact measurable_inl

/-- Remove only the proof transports introduced by the accepted optional
definition's dependent case split. Both branches retain the actual decision
and its successful call equation. -/
theorem selectedSamplerParameters?_eq_match
    (old : AssignmentStartPayload.Input p eta) (input : LocalStartInput old) :
    selectedSamplerParameters? old input =
      match decideReconstruction old input.1 input.2.1 with
      | .failure _ => none
      | .success out hcall =>
          some (selectedSamplerParameters old input.1 input.2.1 out hcall) := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  unfold selectedSamplerParameters?
  dsimp only
  conv_lhs =>
    arg 1
    intro reason h
    rw [apply_eqRec (fun (x : ReconstructionDecision old ledger instruction)
      (_ : ReconstructionDecision.failure reason = x) =>
        decideReconstruction old ledger instruction = x)]
  conv_lhs =>
    arg 2
    intro out hcall h
    rw [apply_eqRec (fun (x : ReconstructionDecision old ledger instruction)
      (_ : ReconstructionDecision.success out hcall = x) =>
        decideReconstruction old ledger instruction = x)]
  change (ReconstructionDecision.rec
      (motive := fun decision => decideReconstruction old ledger instruction = decision →
        Option (CheckedAssignmentJointMeasurability.RawMass p ×
          CheckedAssignmentJointMeasurability.Anchor p))
      (fun _ _ => none)
      (fun out hcall _ => some (selectedSamplerParameters old ledger instruction out hcall))
      (decideReconstruction old ledger instruction) rfl) = _
  generalize hdecision : decideReconstruction old ledger instruction = decision
  cases decision <;> rfl

/-- The accepted optional selected parameters on a fixed discrete input and a
varying positive anchor. Reconstruction failure remains literally `none`. -/
theorem measurable_selectedSamplerParameters?_withAnchor
    (old : AssignmentStartPayload.Input p eta) (input : LocalStartInput old) :
    Measurable (fun anchor : PositiveAnchor p =>
      selectedSamplerParameters? (payloadWithAnchor old anchor)
        (transportLocalStartInput old anchor input)) := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  cases hdecision : decideReconstruction old ledger instruction with
  | failure reason =>
      have hd (anchor : PositiveAnchor p) :
          decideReconstruction (payloadWithAnchor old anchor)
            (transportLocalStartInput old anchor ⟨ledger, (instruction, consistent)⟩).1
            (transportLocalStartInput old anchor ⟨ledger, (instruction, consistent)⟩).2.1 =
              .failure reason := by
        change decideReconstruction (payloadWithAnchor old anchor) ledger instruction = _
        rw [decideReconstruction_payloadWithAnchor, hdecision]
        rfl
      have heq : (fun anchor : PositiveAnchor p =>
          selectedSamplerParameters? (payloadWithAnchor old anchor)
            (transportLocalStartInput old anchor ⟨ledger, (instruction, consistent)⟩)) =
          (fun _ => none) := by
        funext anchor
        rw [selectedSamplerParameters?_eq_match, hd]
      rw [heq]
      exact measurable_const
  | success out hcall =>
      have hd (anchor : PositiveAnchor p) :
          decideReconstruction (payloadWithAnchor old anchor)
            (transportLocalStartInput old anchor ⟨ledger, (instruction, consistent)⟩).1
            (transportLocalStartInput old anchor ⟨ledger, (instruction, consistent)⟩).2.1 =
              .success out hcall := by
        change decideReconstruction (payloadWithAnchor old anchor) ledger instruction = _
        rw [decideReconstruction_payloadWithAnchor, hdecision]
        rfl
      have heq : (fun anchor : PositiveAnchor p =>
          selectedSamplerParameters? (payloadWithAnchor old anchor)
            (transportLocalStartInput old anchor ⟨ledger, (instruction, consistent)⟩)) =
          (fun anchor => some (selectedSamplerParameters
            (payloadWithAnchor old anchor) ledger instruction out hcall)) := by
        funext anchor
        rw [selectedSamplerParameters?_eq_match, hd]
        rfl
      rw [heq]
      exact measurable_some_parameters.comp
        (continuous_selectedSamplerParameters_withAnchor old ledger instruction out hcall).measurable

/-- Equal discrete observations identify the original dependent input after
changing only the representative's anchor. This uses the accepted faithful
observation, including all runtime consistency data. -/
theorem jointInput_reanchor_eq_of_discrete_eq
    (a b : JointLocalStartInput p eta)
    (hdiscrete : jointDiscreteObservation a = jointDiscreteObservation b) :
    (⟨payloadWithAnchor a.1 (jointPositiveAnchor b),
      transportLocalStartInput a.1 (jointPositiveAnchor b) a.2⟩ :
        JointLocalStartInput p eta) = b := by
  apply jointLocalStartObservation_injective
  apply Prod.ext
  · have hfields := congrArg Prod.fst hdiscrete
    change (a.1.n, (a.1.sigma, (a.1.slowSet.1, a.1.queues))) =
      (b.1.n, (b.1.sigma, (b.1.slowSet.1, b.1.queues))) at hfields
    rcases Prod.mk.inj hfields with ⟨hn, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hsigma, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hslow, hqueues⟩
    change payloadObservation (payloadWithAnchor a.1 (jointPositiveAnchor b)) =
      payloadObservation b.1
    simp only [payloadObservation, payloadWithAnchor, jointPositiveAnchor,
      hn, hsigma, hslow, hqueues]
  · change localStartInputCode
        (transportLocalStartInput a.1 (jointPositiveAnchor b) a.2) =
      localStartInputCode b.2
    exact (localStartInputCode_transport a.1 (jointPositiveAnchor b) a.2).trans
      (congrArg Prod.snd hdiscrete)

private instance discreteRangeCountable :
    Countable (JointDiscreteObservationRange p eta) := by
  dsimp only [JointDiscreteObservationRange]
  infer_instance

/-- The attained discrete coordinate of the actual joint input. -/
def jointDiscreteRange (z : JointLocalStartInput p eta) :
    JointDiscreteObservationRange p eta :=
  ⟨jointDiscreteObservation z, ⟨z, rfl⟩⟩

theorem measurable_jointDiscreteRange :
    Measurable (jointDiscreteRange (p := p) (eta := eta)) := by
  apply measurable_to_countable'
  intro c
  have heq : {z : JointLocalStartInput p eta | jointDiscreteRange z = c} =
      {z | jointDiscreteObservation z = c.1} := by
    ext z
    exact Subtype.ext_iff
  change MeasurableSet {z : JointLocalStartInput p eta | jointDiscreteRange z = c}
  rw [heq]
  exact (measurableSet_singleton c.1).preimage measurable_jointDiscreteObservation

/-- Literal optional parameters of the accepted representative, with only
its positive anchor replaced. -/
noncomputable def selectedSamplerParametersOnDiscreteSlice
    (c : JointDiscreteObservationRange p eta) (anchor : PositiveAnchor p) :
    Option (CheckedAssignmentJointMeasurability.RawMass p ×
      CheckedAssignmentJointMeasurability.Anchor p) :=
  selectedSamplerParameters? (payloadWithAnchor (jointInputRepresentative c).1 anchor)
    (transportLocalStartInput (jointInputRepresentative c).1 anchor
      (jointInputRepresentative c).2)

theorem measurable_selectedSamplerParametersOnDiscreteSlice
    (c : JointDiscreteObservationRange p eta) :
    Measurable (selectedSamplerParametersOnDiscreteSlice c) :=
  measurable_selectedSamplerParameters?_withAnchor
    (jointInputRepresentative c).1 (jointInputRepresentative c).2

/-- Slice parameters are exactly the existing parameters on every original
varying input, rather than parameters of a replacement sampled operation. -/
theorem selectedSamplerParameters?_eq_discreteSlice
    (z : JointLocalStartInput p eta) :
    selectedSamplerParameters? z.1 z.2 =
      selectedSamplerParametersOnDiscreteSlice (jointDiscreteRange z)
        (jointPositiveAnchor z) := by
  have hdiscrete : jointDiscreteObservation
      (jointInputRepresentative (jointDiscreteRange z)) = jointDiscreteObservation z :=
    jointDiscreteObservation_representative (jointDiscreteRange z)
  have hin := jointInput_reanchor_eq_of_discrete_eq
    (jointInputRepresentative (jointDiscreteRange z)) z hdiscrete
  exact (congrArg (fun input : JointLocalStartInput p eta =>
    selectedSamplerParameters? input.1 input.2) hin).symm

/-- Unconditional varying-anchor joint measurability of the ACTUAL optional
selected raw mass and real anchor. The input sigma algebra is the accepted
comap; no discrete structure is placed on the real anchor or joint input. -/
theorem measurable_selectedSamplerParameters?_joint :
    Measurable (fun z : JointLocalStartInput p eta =>
      selectedSamplerParameters? z.1 z.2) := by
  have hs : Measurable (fun q : JointDiscreteObservationRange p eta × PositiveAnchor p =>
      selectedSamplerParametersOnDiscreteSlice q.1 q.2) :=
    measurable_from_prod_countable_right
      measurable_selectedSamplerParametersOnDiscreteSlice
  have heq : (fun z : JointLocalStartInput p eta => selectedSamplerParameters? z.1 z.2) =
      (fun z => selectedSamplerParametersOnDiscreteSlice
        (jointDiscreteRange z) (jointPositiveAnchor z)) :=
    funext selectedSamplerParameters?_eq_discreteSlice
  rw [heq]
  exact hs.comp (measurable_jointDiscreteRange.prodMk measurable_jointPositiveAnchor)

/-- Arbitrary-base composition of the actual optional joint parameters.
Only measurability of the supplied actual joint input is an input. -/
theorem measurable_selectedSamplerParameters?_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta) (hinput : Measurable input) :
    Measurable (fun x => selectedSamplerParameters? (input x).1 (input x).2) :=
  measurable_selectedSamplerParameters?_joint.comp hinput

/-- Every present selected anchor is strictly positive. This is obtained from
the actual selected law, without assuming reconstruction succeeds. -/
theorem selectedSamplerParameters?_anchor_pos
    (z : JointLocalStartInput p eta)
    (parameters : CheckedAssignmentJointMeasurability.RawMass p ×
      CheckedAssignmentJointMeasurability.Anchor p)
    (hpresent : selectedSamplerParameters? z.1 z.2 = some parameters) :
    ∀ i, 0 < parameters.2 i := by
  rw [selectedSamplerParameters?_eq_match] at hpresent
  cases hdecision : decideReconstruction z.1 z.2.1 z.2.2.1 with
  | failure reason => simp only [hdecision] at hpresent; cases hpresent
  | success out hcall =>
      simp only [hdecision] at hpresent
      have heq := Option.some.inj hpresent
      rw [← heq]
      exact (successfulLawSelection z.1 z.2.1 z.2.2.1 out hcall).law.anchor_pos

/-- Joint code measurability on a single attained discrete input with its
positive anchor and complete row varying. The sampler consumes the actual
selected parameters and every original assignment coordinate. -/
theorem measurable_laterAssignmentStartCode_withAnchor
    (old : AssignmentStartPayload.Input p eta) (input : LocalStartInput old) :
    Measurable (fun z : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
      laterAssignmentStartCode (payloadWithAnchor old z.1)
        (transportLocalStartInput old z.1 input).1
        (transportLocalStartInput old z.1 input).2.1 z.2
        (transportLocalStartInput old z.1 input).2.2) := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  have heq : (fun z : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
      laterAssignmentStartCode (payloadWithAnchor old z.1)
        (transportLocalStartInput old z.1 ⟨ledger, (instruction, consistent)⟩).1
        (transportLocalStartInput old z.1 ⟨ledger, (instruction, consistent)⟩).2.1 z.2
        (transportLocalStartInput old z.1 ⟨ledger, (instruction, consistent)⟩).2.2) =
      (fun z : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
        match decideReconstruction old ledger instruction with
        | .failure reason => LaterAssignmentStartCode.reconstructionFailure reason
        | .success out hcall =>
            let parameters := selectedSamplerParameters
              (payloadWithAnchor old z.1) ledger instruction out hcall
            codeOfCheckedSample p (CheckedAssignmentSample.checkedAssignmentSample p
              parameters.1 parameters.2 (ownAssignmentVector z.2 instruction.time))) := by
    funext z
    rw [laterAssignmentStartCode_eq_reconstructedFirstCode
      (payloadWithAnchor old z.1)
      (transportLocalStartInput old z.1 ⟨ledger, (instruction, consistent)⟩) z.2]
    dsimp only [reconstructedFirstCode, transportLocalStartInput]
    rw [decideReconstruction_payloadWithAnchor]
    cases decideReconstruction old ledger instruction <;> rfl
  rw [heq]
  cases decideReconstruction old ledger instruction with
  | failure reason => exact measurable_const
  | success out hcall =>
      have hparameters : Measurable
          (fun z : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
            selectedSamplerParameters (payloadWithAnchor old z.1)
              ledger instruction out hcall) :=
        (continuous_selectedSamplerParameters_withAnchor old ledger instruction out hcall).measurable.comp
          measurable_fst
      have hsample := CheckedAssignmentJointMeasurability.measurable_checkedAssignmentSample_comp p
        (fun z : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
          (selectedSamplerParameters (payloadWithAnchor old z.1)
            ledger instruction out hcall).1)
        (fun z : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
          (selectedSamplerParameters (payloadWithAnchor old z.1)
            ledger instruction out hcall).2)
        (fun z => ownAssignmentVector z.2 instruction.time)
        hparameters.fst hparameters.snd
        ((measurable_ownAssignmentVector instruction.time).comp measurable_snd)
      exact (Measurable.of_discrete (f := codeOfCheckedSample p)).comp hsample

/-- The accepted slice operation code is measurable in its positive anchor
and untouched continuous row. -/
theorem measurable_operationCodeOnDiscreteSlice
    (c : JointDiscreteObservationRange p eta) :
    Measurable (operationCodeOnDiscreteSlice c) :=
  measurable_laterAssignmentStartCode_withAnchor
    (jointInputRepresentative c).1 (jointInputRepresentative c).2

/-- Joint Borel measurability of the EXISTING exact operation code on its
ENTIRE varying dependent input and complete-row domain. -/
theorem measurable_laterAssignmentStartCodeMap :
    Measurable
      (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap
        (p := p) (eta := eta)) := by
  have hs : Measurable (fun q : JointDiscreteObservationRange p eta ×
      (PositiveAnchor p × CompletePublicTable.CompleteRow p) =>
      operationCodeOnDiscreteSlice q.1 q.2) :=
    measurable_from_prod_countable_right measurable_operationCodeOnDiscreteSlice
  have heq : LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap
      (p := p) (eta := eta) =
      (fun z => operationCodeOnDiscreteSlice (jointDiscreteRange z.1)
        (jointPositiveAnchor z.1, z.2)) :=
    funext laterAssignmentStartCode_eq_discreteSlice
  rw [heq]
  exact hs.comp
    ((measurable_jointDiscreteRange.comp measurable_fst).prodMk
      ((measurable_jointPositiveAnchor.comp measurable_fst).prodMk measurable_snd))

/-- Compose separately measurable actual local inputs and complete rows over
any measurable base. This retains the original complete row and K+1 vector. -/
theorem measurable_laterAssignmentStartCodeMap_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (row : X → CompletePublicTable.CompleteRow p)
    (hinput : Measurable input) (hrow : Measurable row) :
    Measurable (fun x =>
      LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap (input x, row x)) :=
  measurable_laterAssignmentStartCodeMap.comp (hinput.prodMk hrow)

/-- The measurable code is the projection of the original dependent operation
result, including every exceptional path and the full sampled outcome. -/
theorem laterAssignmentStartCodeMap_eq_codeOfResult
    (z : JointOperationInput p eta) :
    LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z =
      codeOfResult p (LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2) := rfl

/-- The accepted decoder identity ties these measurable codes to the existing
operation, with its original input, complete row, payload and proof indices.
This identity makes no claim that a real-valued payload is measurable. -/
theorem decode_laterAssignmentStartCodeMap_exact
    (z : JointOperationInput p eta) :
    decodeLaterAssignmentStart z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2
        (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z) =
      some (LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2) :=
  LaterAssignmentAnchorMeasurability.decodeLaterAssignmentStart_exact z

section ResultEvents

variable {old : AssignmentStartPayload.Input p eta}
variable {ledger : LaterAssignmentStartOperation.LocalLedger old}
variable {instruction : CoordinatorPhaseClock.AssignmentStartInstruction p}
variable {row : CompletePublicTable.CompleteRow p}
variable {consistent : LaterAssignmentStartOperation.LocalConsistency old ledger}

theorem codeOfResult_eq_reconstructionFailure_iff
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent)
    (reason : AssignmentScoreReconstruction.Failure) :
    codeOfResult p result = .reconstructionFailure reason ↔
      result = .reconstructionFailure reason := by
  cases result <;> simp [codeOfResult]

theorem codeOfResult_eq_prefixFailure_iff
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason) :
    codeOfResult p result = .prefixFailure arm reason ↔
      result = .prefixFailure arm reason := by
  cases result <;> simp [codeOfResult]

theorem codeOfResult_eq_orientationFailure_iff
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent)
    (set : PrefixSetSampler.SetCarrier p.K p.m) :
    codeOfResult p result = .orientationFailure set ↔
      result = .orientationFailure set := by
  cases result <;> simp [codeOfResult]

theorem codeOfResult_mem_success_iff
    (result : LaterAssignmentStartOperation.Result old ledger instruction row consistent) :
    codeOfResult p result ∈ laterAssignmentStartSuccessCodeSet p ↔
      ∃ (output : SuccessfulStart old ledger instruction row)
        (hconsistent : output.localConsistency = consistent),
        result = .success output hconsistent := by
  cases result <;> simp [codeOfResult, laterAssignmentStartSuccessCodeSet]
  rename_i output hconsistent
  exact hconsistent

end ResultEvents

/-- Every exact output fiber is ambient measurable on the full new domain. -/
theorem measurableSet_laterAssignmentStartCode_eq
    (code : LaterAssignmentStartCode p) :
    MeasurableSet {z : JointOperationInput p eta |
      LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z = code} :=
  (measurableSet_singleton code).preimage measurable_laterAssignmentStartCodeMap

/-- Exact output events after separately measurable local-input and row maps. -/
theorem measurableSet_laterAssignmentStartCode_eq_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (row : X → CompletePublicTable.CompleteRow p)
    (hinput : Measurable input) (hrow : Measurable row)
    (code : LaterAssignmentStartCode p) :
    MeasurableSet {x |
      LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap (input x, row x) = code} :=
  (measurableSet_singleton code).preimage
    (measurable_laterAssignmentStartCodeMap_comp input row hinput hrow)

/-- The success event, with no substitution of a failure slow set. -/
def jointSuccessSet : Set (JointOperationInput p eta) :=
  LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap ⁻¹'
    laterAssignmentStartSuccessCodeSet p

theorem measurableSet_jointSuccessSet :
    MeasurableSet (jointSuccessSet (p := p) (eta := eta)) :=
  measurable_laterAssignmentStartCodeMap MeasurableSet.of_discrete

/-- Success of the code is exactly success of the original dependent result. -/
theorem mem_jointSuccessSet_iff (z : JointOperationInput p eta) :
    z ∈ jointSuccessSet ↔
      ∃ (output : SuccessfulStart z.1.1 z.1.2.1 z.1.2.2.1 z.2)
        (hconsistent : output.localConsistency = z.1.2.2.2),
        LaterAssignmentStartOperation.laterAssignmentStart
          z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 =
            .success output hconsistent :=
  codeOfResult_mem_success_iff _

/-- The literal dependent operation's success event is ambient measurable. -/
theorem measurableSet_laterAssignmentStartSuccess :
    MeasurableSet {z : JointOperationInput p eta |
      ∃ (output : SuccessfulStart z.1.1 z.1.2.1 z.1.2.2.1 z.2)
        (hconsistent : output.localConsistency = z.1.2.2.2),
        LaterAssignmentStartOperation.laterAssignmentStart
          z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 =
            .success output hconsistent} := by
  have heq : {z : JointOperationInput p eta |
      ∃ (output : SuccessfulStart z.1.1 z.1.2.1 z.1.2.2.1 z.2)
        (hconsistent : output.localConsistency = z.1.2.2.2),
        LaterAssignmentStartOperation.laterAssignmentStart
          z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 =
            .success output hconsistent} = jointSuccessSet :=
    Set.ext (fun z => (mem_jointSuccessSet_iff z).symm)
  rw [heq]
  exact measurableSet_jointSuccessSet

/-- All seven reconstruction failure reasons are preserved literally. -/
theorem measurableSet_laterAssignmentStartReconstructionFailure
    (reason : AssignmentScoreReconstruction.Failure) :
    MeasurableSet {z : JointOperationInput p eta |
      LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 =
          .reconstructionFailure reason} := by
  have heq : {z : JointOperationInput p eta |
      LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 = .reconstructionFailure reason} =
      {z | LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z =
        .reconstructionFailure reason} :=
    Set.ext (fun _ => (codeOfResult_eq_reconstructionFailure_iff _ reason).symm)
  rw [heq]
  exact measurableSet_laterAssignmentStartCode_eq _

/-- Prefix failure retains the original first failed arm and failure reason. -/
theorem measurableSet_laterAssignmentStartPrefixFailure
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason) :
    MeasurableSet {z : JointOperationInput p eta |
      LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 = .prefixFailure arm reason} := by
  have heq : {z : JointOperationInput p eta |
      LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 = .prefixFailure arm reason} =
      {z | LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z =
        .prefixFailure arm reason} :=
    Set.ext (fun _ => (codeOfResult_eq_prefixFailure_iff _ arm reason).symm)
  rw [heq]
  exact measurableSet_laterAssignmentStartCode_eq _

/-- Orientation failure retains the actual prefix set that succeeded. -/
theorem measurableSet_laterAssignmentStartOrientationFailure
    (set : PrefixSetSampler.SetCarrier p.K p.m) :
    MeasurableSet {z : JointOperationInput p eta |
      LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 = .orientationFailure set} := by
  have heq : {z : JointOperationInput p eta |
      LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 = .orientationFailure set} =
      {z | LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z =
        .orientationFailure set} :=
    Set.ext (fun _ => (codeOfResult_eq_orientationFailure_iff _ set).symm)
  rw [heq]
  exact measurableSet_laterAssignmentStartCode_eq _

/-- Exact full sampled outcomes, before the successful slow-set projection. -/
theorem measurableSet_laterAssignmentStartSampled
    (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m) :
    MeasurableSet {z : JointOperationInput p eta |
      LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z = .sampled outcome} :=
  measurableSet_laterAssignmentStartCode_eq _

/-- Graph of the exact code on the ambient full new domain. -/
theorem measurableSet_laterAssignmentStartCodeGraph :
    MeasurableSet {q : JointOperationInput p eta × LaterAssignmentStartCode p |
      q.2 = LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1} :=
  measurableSet_eq_fun measurable_snd
    (measurable_laterAssignmentStartCodeMap.comp measurable_fst)

/-- Every restriction of the code graph to a set of outputs is ambient
measurable. This includes all failure graphs with their full payloads. -/
theorem measurableSet_laterAssignmentStartCodeGraph_restrict
    (outputs : Set (LaterAssignmentStartCode p)) :
    MeasurableSet {q : JointOperationInput p eta × LaterAssignmentStartCode p |
      q.2 = LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1 ∧
        q.2 ∈ outputs} :=
  measurableSet_laterAssignmentStartCodeGraph.inter
    (MeasurableSet.of_discrete.preimage measurable_snd)

theorem measurableSet_laterAssignmentStartSuccessGraph :
    MeasurableSet {q : JointOperationInput p eta × LaterAssignmentStartCode p |
      q.2 = LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1 ∧
        q.2 ∈ laterAssignmentStartSuccessCodeSet p} :=
  measurableSet_laterAssignmentStartCodeGraph_restrict _

theorem measurableSet_laterAssignmentStartReconstructionFailureGraph :
    MeasurableSet {q : JointOperationInput p eta × LaterAssignmentStartCode p |
      q.2 = LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1 ∧
        ∃ reason, q.2 = .reconstructionFailure reason} :=
  measurableSet_laterAssignmentStartCodeGraph_restrict
    {code | ∃ reason, code = .reconstructionFailure reason}

theorem measurableSet_laterAssignmentStartPrefixFailureGraph :
    MeasurableSet {q : JointOperationInput p eta × LaterAssignmentStartCode p |
      q.2 = LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1 ∧
        ∃ arm reason, q.2 = .prefixFailure arm reason} :=
  measurableSet_laterAssignmentStartCodeGraph_restrict
    {code | ∃ arm reason, code = .prefixFailure arm reason}

theorem measurableSet_laterAssignmentStartOrientationFailureGraph :
    MeasurableSet {q : JointOperationInput p eta × LaterAssignmentStartCode p |
      q.2 = LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1 ∧
        ∃ set, q.2 = .orientationFailure set} :=
  measurableSet_laterAssignmentStartCodeGraph_restrict
    {code | ∃ set, code = .orientationFailure set}

/-- Successful slow-set graph. The accepted erasure projection is used only
on success, so failure never contributes a default slow set to this graph. -/
def jointSlowSetGraph :
    Set (JointOperationInput p eta × Finset (Fin p.K)) :=
  {q | q.1 ∈ jointSuccessSet ∧ q.2 = slowSetErasureOfCode
    (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap q.1)}

theorem measurableSet_jointSlowSetGraph :
    MeasurableSet (jointSlowSetGraph (p := p) (eta := eta)) := by
  have hslow : Measurable (fun z : JointOperationInput p eta =>
      slowSetErasureOfCode
        (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z)) :=
    measurable_slowSetErasureOfCode.comp measurable_laterAssignmentStartCodeMap
  exact (measurableSet_jointSuccessSet.preimage measurable_fst).inter
    (measurableSet_eq_fun measurable_snd (hslow.comp measurable_fst))

/-- The slow-set graph records the actual successful output's slow set. -/
theorem mem_jointSlowSetGraph_of_success
    (z : JointOperationInput p eta)
    (output : SuccessfulStart z.1.1 z.1.2.1 z.1.2.2.1 z.2)
    (hconsistent : output.localConsistency = z.1.2.2.2)
    (hsuccess : LaterAssignmentStartOperation.laterAssignmentStart
      z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 = .success output hconsistent) :
    (z, output.slowSet.1) ∈ jointSlowSetGraph := by
  refine ⟨(mem_jointSuccessSet_iff z).mpr ⟨output, hconsistent, hsuccess⟩, ?_⟩
  rw [laterAssignmentStartCodeMap_eq_codeOfResult, hsuccess]
  exact successful_slowSet_matches_code output

/-- Exact characterization of the slow-set graph by the original dependent
operation. No payload, rates or output-observation measurability is asserted. -/
theorem mem_jointSlowSetGraph_iff
    (z : JointOperationInput p eta) (slowSet : Finset (Fin p.K)) :
    (z, slowSet) ∈ jointSlowSetGraph ↔
      ∃ (output : SuccessfulStart z.1.1 z.1.2.1 z.1.2.2.1 z.2)
        (hconsistent : output.localConsistency = z.1.2.2.2),
        LaterAssignmentStartOperation.laterAssignmentStart
          z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2 =
            .success output hconsistent ∧ slowSet = output.slowSet.1 := by
  constructor
  · rintro ⟨hsuccess, hslow⟩
    obtain ⟨output, hconsistent, hcall⟩ := (mem_jointSuccessSet_iff z).mp hsuccess
    have hout : output.slowSet.1 = slowSetErasureOfCode
        (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z) :=
      (mem_jointSlowSetGraph_of_success z output hconsistent hcall).2
    exact ⟨output, hconsistent, hcall, hslow.trans hout.symm⟩
  · rintro ⟨output, hconsistent, hcall, rfl⟩
    exact mem_jointSlowSetGraph_of_success z output hconsistent hcall

/-- Ambient measurability of every successful slow-set event. -/
theorem measurableSet_laterAssignmentStartSlowSet
    (slowSet : Finset (Fin p.K)) :
    MeasurableSet {z : JointOperationInput p eta |
      (z, slowSet) ∈ jointSlowSetGraph} :=
  measurableSet_jointSlowSetGraph.preimage (measurable_id.prodMk measurable_const)

/-- The successful slow-set graph under arbitrary separately measurable
actual local-input and complete-row maps remains ambient measurable. -/
theorem measurableSet_jointSlowSetGraph_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (row : X → CompletePublicTable.CompleteRow p)
    (hinput : Measurable input) (hrow : Measurable row) :
    MeasurableSet {q : X × Finset (Fin p.K) |
      ((input q.1, row q.1), q.2) ∈ jointSlowSetGraph} :=
  measurableSet_jointSlowSetGraph.preimage
    (((hinput.prodMk hrow).comp measurable_fst).prodMk measurable_snd)

end Bandits.Support.LaterAssignmentJointCodeMeasurability

end
