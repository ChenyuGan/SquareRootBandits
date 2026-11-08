/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.AssignmentPayloadDerivedMeasurability
public import Bandits.Support.LaterAssignmentJointCodeMeasurability

/-!
# Full output observation for a varying later assignment start

The local start is observed on the existing varying-anchor input carrier and
the original complete row. Its full observation keeps the exact operation
code, optional selected law, existing payload observation with base scores,
the original complete assignment vector at the actual instruction time, and
the successful payload's literal derived fields.

Sources: sources/zip4/manuscript/06_interruptions.tex:16-61,80-100 and
sources/zip4/manuscript/appendix_b_communication.tex:25-55.
-/

@[expose] public section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.AssignmentStartPayload
open Bandits.Support.AssignmentPayloadDerivedMeasurability
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.LaterAssignmentStartOperation
open Bandits.Support.LaterAssignmentAnchorMeasurability
open Bandits.Support.LaterAssignmentJointCodeMeasurability
open Bandits.Support.CheckedAssignmentJointMeasurability
open Bandits.Support.CompletePublicTable

namespace Bandits.Support.LaterAssignmentFullOutputMeasurability

universe uX uY uZ

variable {p : ConstructorDimensions.Parameters}
abbrev LearningRate := Bandits.Support.ReferencePrelaunchFollower.LearningRate
variable {eta : LearningRate}

/-- The unchanged dependent local input, including its retained anchor. -/
abbrev JointLocalStartInput (p : ConstructorDimensions.Parameters)
    (eta : LearningRate) :=
  LaterAssignmentAnchorMeasurability.JointLocalStartInput p eta

/-- The actual varying local input paired with its original complete row. -/
abbrev JointOperationInput (p : ConstructorDimensions.Parameters)
    (eta : LearningRate) :=
  LaterAssignmentAnchorMeasurability.JointOperationInput p eta

/-- The existing payload observation paired with its retained base scores. -/
abbrev PayloadScoreObservation (p : ConstructorDimensions.Parameters) :=
  LaterAssignmentStartMeasurability.PayloadObservation p × (Fin (p.m - 1) → ℕ)

/-- The existing optional parameters selected by the actual reconstruction. -/
abbrev SelectedParameters? (p : ConstructorDimensions.Parameters) :=
  Option (CheckedAssignmentJointMeasurability.RawMass p ×
    CheckedAssignmentJointMeasurability.Anchor p)

/-- The optional actual payload and score projection before applying the
existing payload observation. This is used only as an intermediate carrier. -/
abbrev PayloadScore? (p : ConstructorDimensions.Parameters) (eta : LearningRate) :=
  Option (AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ))

/-- The existing full K+1 assignment-vector type. -/
abbrev OriginalAssignmentVector (p : ConstructorDimensions.Parameters) :=
  CheckedAssignmentSample.AssignmentVector p

/-- Literal anchor, complete rate vector, exponent vector and auxiliary-arm
fields carried by a successful output payload. -/
abbrev DerivedOutputFields (p : ConstructorDimensions.Parameters) :=
  (Fin p.K → ℝ) × ((Fin p.K → ℝ) × ((Fin p.K → ℕ) × Fin p.K))

/-- A transparent product observation. The row, payload anchor and rate
vectors retain their ordinary Borel structures; only the existing operation
code and the already finite-valued coordinates are discrete. -/
abbrev FullOutputObservation (p : ConstructorDimensions.Parameters) :=
  LaterAssignmentStartMeasurability.LaterAssignmentStartCode p ×
    (SelectedParameters? p ×
      (Option (PayloadScoreObservation p) ×
        (OriginalAssignmentVector p × Option (DerivedOutputFields p))))

/-- Measurable some injection for the existing Option measurable-space
convention, whose sigma algebra is induced from a sum. -/
theorem measurable_some_of_measurable {X : Type uX} [MeasurableSpace X]
    {Y : Type uY} [MeasurableSpace Y] (f : X → Y) (hf : Measurable f) :
    Measurable (fun x => (some (f x) : Option Y)) := by
  have hs : Measurable (some : Y → Option Y) := by
    apply measurable_comap_iff.mpr
    exact measurable_inl
  exact hs.comp hf

/-- Option.map preserves measurability for the existing Option sigma
algebra. -/
theorem measurable_optionMap {X : Type uX} [MeasurableSpace X]
    {Y : Type uY} {Z : Type uZ} [MeasurableSpace Y] [MeasurableSpace Z]
    (f : Y → Z) (hf : Measurable f) (g : X → Option Y) (hg : Measurable g) :
    Measurable (fun x => (g x).map f) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun x =>
    Equiv.optionEquivSumPUnit Z ((g x).map f))
  have hsource : Measurable (fun x =>
      Equiv.optionEquivSumPUnit Y (g x)) := measurable_comap_iff.mp hg
  let lift : Y ⊕ PUnit.{uY + 1} → Z ⊕ PUnit.{uZ + 1} :=
    Sum.map f (fun _ : PUnit.{uY + 1} => (PUnit.unit : PUnit.{uZ + 1}))
  have hlift : Measurable lift := hf.sumMap measurable_const
  have heq : (fun x =>
      Equiv.optionEquivSumPUnit Z ((g x).map f)) =
      (fun x => lift (Equiv.optionEquivSumPUnit.{uY, uY} Y (g x))) := by
    funext x
    cases g x <;> rfl
  exact heq ▸ hlift.comp hsource

/-- The actual result of the already defined operation, with all original
dependent inputs and the complete row retained. -/
noncomputable def actualResult (z : JointOperationInput p eta) :=
  LaterAssignmentStartOperation.laterAssignmentStart
    z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2

/-- The operation's existing optional payload/base-score projection. -/
noncomputable def actualPayloadScore? (z : JointOperationInput p eta) : PayloadScore? p eta :=
  LaterAssignmentStartMeasurability.resultPayloadScore? (actualResult z)

/-- The variable-time original complete assignment vector. Its time is read
from the existing finite instruction coordinate, while all K+1 scalar
coordinates remain the original row projection. -/
def originalAssignmentVector (z : JointOperationInput p eta) : OriginalAssignmentVector p :=
  LaterAssignmentStartOperation.ownAssignmentVector z.2 z.1.2.2.1.time

/-- Successful payload-derived fields, with their literal full vectors. -/
noncomputable def actualDerivedFields? (z : JointOperationInput p eta) :
    Option (DerivedOutputFields p) :=
  (actualPayloadScore? z).map fun payloadScore =>
    AssignmentPayloadDerivedMeasurability.inputDerivedFields payloadScore.1

/-- The optional actual payload and base scores observed through the existing
payload observation, preserving every continuous and discrete payload field. -/
noncomputable def actualPayloadScoreObservation? (z : JointOperationInput p eta) :
    Option (PayloadScoreObservation p) :=
  (actualPayloadScore? z).map fun payloadScore =>
    (LaterAssignmentStartMeasurability.payloadObservation payloadScore.1,
      payloadScore.2)

/-- One full observation of the exact varying later-assignment operation. -/
noncomputable def laterAssignmentFullOutputObservation
    (z : JointOperationInput p eta) : FullOutputObservation p :=
  (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z,
    (LaterAssignmentStartMeasurability.selectedSamplerParameters?
        z.1.1 z.1.2,
      (actualPayloadScoreObservation? z,
        (originalAssignmentVector z, actualDerivedFields? z))))

/-- The accepted operation code remains the first literal output coordinate. -/
theorem fullOutput_code (z : JointOperationInput p eta) :
    (laterAssignmentFullOutputObservation z).1 =
      LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap z := rfl

/-- The optional raw mass and real anchor are exactly the accepted varying
selected-parameter projection. -/
theorem fullOutput_selectedParameters (z : JointOperationInput p eta) :
    (laterAssignmentFullOutputObservation z).2.1 =
      LaterAssignmentStartMeasurability.selectedSamplerParameters?
        z.1.1 z.1.2 := rfl

/-- The payload-score coordinate is the existing resultPayloadScore? observed
through payloadObservation. -/
theorem fullOutput_payloadScoreObservation (z : JointOperationInput p eta) :
    (laterAssignmentFullOutputObservation z).2.2.1 =
      (actualPayloadScore? z).map fun payloadScore =>
        (LaterAssignmentStartMeasurability.payloadObservation payloadScore.1,
          payloadScore.2) := rfl

/-- The assignment-vector coordinate is the actual row's full K+1 vector at
the instruction's own finite time. -/
theorem fullOutput_originalAssignmentVector (z : JointOperationInput p eta) :
    (laterAssignmentFullOutputObservation z).2.2.2.1 =
      LaterAssignmentStartOperation.ownAssignmentVector z.2 z.1.2.2.1.time := rfl

/-- The last observation coordinate contains every derived payload field on
success and is absent on each actual failure. -/
theorem fullOutput_derivedFields (z : JointOperationInput p eta) :
    (laterAssignmentFullOutputObservation z).2.2.2.2 = actualDerivedFields? z := rfl

/-- Reanchoring one attained discrete observation reconstructs the original
dependent local input without changing its anchor, ledger, instruction,
consistency data, or any runtime coordinate. -/
theorem jointInput_eq_reanchoredRepresentative (z : JointOperationInput p eta) :
    (⟨payloadWithAnchor
        (jointInputRepresentative (jointDiscreteRange z.1)).1
          (jointPositiveAnchor z.1),
      transportLocalStartInput
        (jointInputRepresentative (jointDiscreteRange z.1)).1
          (jointPositiveAnchor z.1)
          (jointInputRepresentative (jointDiscreteRange z.1)).2⟩ :
        JointLocalStartInput p eta) = z.1 := by
  apply jointInput_reanchor_eq_of_discrete_eq
    (jointInputRepresentative (jointDiscreteRange z.1)) z.1
  exact jointDiscreteObservation_representative (jointDiscreteRange z.1)

private theorem transportLocalStartInput_ledger_eq
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) :
    (transportLocalStartInput old anchor input).1 = input.1 := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  rfl

private theorem transportLocalStartInput_instruction_eq
    (old : AssignmentStartPayload.Input p eta) (anchor : PositiveAnchor p)
    (input : LocalStartInput old) :
    (transportLocalStartInput old anchor input).2.1 = input.2.1 := by
  rcases input with ⟨ledger, ⟨instruction, consistent⟩⟩
  rfl

/-- The actual variable-time row vector factors through the accepted
countable instruction coordinate and the untouched complete row. -/
noncomputable def originalAssignmentVectorOnSlice
    (c : JointDiscreteObservationRange p eta)
    (q : PositiveAnchor p × CompletePublicTable.CompleteRow p) :
    OriginalAssignmentVector p :=
  LaterAssignmentStartOperation.ownAssignmentVector q.2
    (jointInputRepresentative c).2.2.1.time

/-- On each discrete input slice the full row-vector projection is measurable
using the existing fixed-time theorem. -/
theorem measurable_originalAssignmentVectorOnSlice
    (c : JointDiscreteObservationRange p eta) :
    Measurable (originalAssignmentVectorOnSlice c) := by
  change Measurable (fun q : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
    LaterAssignmentStartOperation.ownAssignmentVector q.2
      (jointInputRepresentative c).2.2.1.time)
  exact (LaterAssignmentStartMeasurability.measurable_ownAssignmentVector
    (jointInputRepresentative c).2.2.1.time).comp measurable_snd

/-- The variable-time assignment vector is measurable on the exact existing
joint operation carrier; the instruction time remains its original finite
coordinate and the row remains the original complete row. -/
theorem measurable_originalAssignmentVector :
    Measurable (originalAssignmentVector (p := p) (eta := eta)) := by
  have hs : Measurable (fun q : JointDiscreteObservationRange p eta ×
      (PositiveAnchor p × CompletePublicTable.CompleteRow p) =>
      originalAssignmentVectorOnSlice q.1 q.2) :=
    measurable_from_prod_countable_right measurable_originalAssignmentVectorOnSlice
  have heq : originalAssignmentVector (p := p) (eta := eta) = fun z =>
      originalAssignmentVectorOnSlice (jointDiscreteRange z.1)
        (jointPositiveAnchor z.1, z.2) := by
    funext z
    have hin := jointInput_eq_reanchoredRepresentative z
    have htime := congrArg
      (fun input : JointLocalStartInput p eta => input.2.2.1.time) hin
    have hrepresentativeTime :
        (jointInputRepresentative (jointDiscreteRange z.1)).2.2.1.time =
          z.1.2.2.1.time := by
      simpa [transportLocalStartInput] using htime
    change LaterAssignmentStartOperation.ownAssignmentVector z.2
        z.1.2.2.1.time =
      LaterAssignmentStartOperation.ownAssignmentVector z.2
        (jointInputRepresentative (jointDiscreteRange z.1)).2.2.1.time
    rw [hrepresentativeTime]
  rw [heq]
  exact hs.comp
    ((measurable_jointDiscreteRange.comp measurable_fst).prodMk
      ((measurable_jointPositiveAnchor.comp measurable_fst).prodMk measurable_snd))

/-- Exact output payload/score projection on one attained discrete input
slice, parametrized by the literal countable operation code and the real
positive anchor. The sampled branch uses the actual reconstruction and law;
the three operation-failure branches remain none. -/
noncomputable def payloadScoreFromCodeOnSlice
    (c : JointDiscreteObservationRange p eta)
    (code : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p)
    (anchor : PositiveAnchor p) : PayloadScore? p eta :=
  match code with
  | .sampled outcome =>
      let old := (jointInputRepresentative c).1
      let input := (jointInputRepresentative c).2
      match LaterAssignmentStartOperation.decideReconstruction
          (payloadWithAnchor old anchor) input.1 input.2.1 with
      | .failure _ => none
      | .success reconstructed hcall =>
          let old' := payloadWithAnchor old anchor
          let selection := LaterAssignmentStartMeasurability.successfulLawSelection
            old' input.1 input.2.1 reconstructed hcall
          let slowSet := CheckedAssignmentOrientation.slowSetAfter p
            outcome.1.1 outcome.1.2 outcome.2
          let payload := LaterAssignmentStartOperation.payloadInput old' input.2.1
            reconstructed selection.law slowSet
          some (payload,
            LaterAssignmentStartOperation.retainedBaseScore reconstructed payload)
  | _ => none

/-- On a successful fixed reconstruction and a fixed sampled outcome, the
existing payload observation varies only through the actual selected law's
real anchor; queue, slow-set, clock and source fields remain literal. -/
private theorem measurable_payloadScore_successSlice
    (c : JointDiscreteObservationRange p eta)
    (outcome : OrientedAssignmentLaw.AssignmentOutcome p.K p.m)
    (reconstructed : AssignmentScoreReconstruction.ReconstructedStart
      (jointInputRepresentative c).2.1
      (jointInputRepresentative c).2.2.1)
    (hcall : AssignmentScoreReconstruction.reconstructLaterStart
      (jointInputRepresentative c).2.1 (jointInputRepresentative c).2.2.1 =
        .success (jointInputRepresentative c).2.1
          (jointInputRepresentative c).2.2.1 reconstructed)
    (hdecision : LaterAssignmentStartOperation.decideReconstruction
      (jointInputRepresentative c).1
      (jointInputRepresentative c).2.1
      (jointInputRepresentative c).2.2.1 = .success reconstructed hcall) :
    Measurable (fun anchor : PositiveAnchor p =>
      payloadScoreFromCodeOnSlice c (.sampled outcome) anchor) := by
  let old := (jointInputRepresentative c).1
  let input := (jointInputRepresentative c).2
  let ledger := input.1
  let instruction := input.2.1
  let selected (anchor : PositiveAnchor p) :=
    LaterAssignmentStartMeasurability.successfulLawSelection
      (payloadWithAnchor old anchor) ledger instruction reconstructed hcall
  let parameters (anchor : PositiveAnchor p) :=
    LaterAssignmentStartMeasurability.selectedSamplerParameters
      (payloadWithAnchor old anchor) ledger instruction reconstructed hcall
  have hparameters : Measurable parameters :=
    (LaterAssignmentJointCodeMeasurability.continuous_selectedSamplerParameters_withAnchor
      old ledger instruction reconstructed hcall).measurable
  let slowSet := CheckedAssignmentOrientation.slowSetAfter p
    outcome.1.1 outcome.1.2 outcome.2
  let payload (anchor : PositiveAnchor p) :=
    LaterAssignmentStartOperation.payloadInput (payloadWithAnchor old anchor)
      instruction reconstructed (selected anchor).law slowSet
  have hpayloadObservation : Measurable (fun anchor : PositiveAnchor p =>
      LaterAssignmentStartMeasurability.payloadObservation (payload anchor)) := by
    have heq : (fun anchor : PositiveAnchor p =>
        LaterAssignmentStartMeasurability.payloadObservation (payload anchor)) =
        fun anchor => (old.n, (instruction.time,
          (slowSet.1, ((parameters anchor).2,
            AssignmentScoreReconstruction.initialQueue reconstructed)))) := by
      funext anchor
      simp [payload, parameters, selected, payloadWithAnchor,
        LaterAssignmentStartMeasurability.successfulLawSelection,
        LaterAssignmentStartMeasurability.selectedSamplerParameters,
        LaterAssignmentStartOperation.payloadInput,
        LaterAssignmentStartMeasurability.payloadObservation]
    rw [heq]
    exact measurable_const.prodMk
      (measurable_const.prodMk
        (measurable_const.prodMk
          ((measurable_snd.comp hparameters).prodMk measurable_const)))
  have hpayload : Measurable payload := by
    apply measurable_comap_iff.mpr
    simpa only [Function.comp_def] using hpayloadObservation
  have hscore : Measurable (fun anchor : PositiveAnchor p =>
      LaterAssignmentStartOperation.retainedBaseScore reconstructed (payload anchor)) := by
    have heq : (fun anchor : PositiveAnchor p =>
        LaterAssignmentStartOperation.retainedBaseScore reconstructed (payload anchor)) =
        fun _ => fun i : Fin (p.m - 1) =>
          AssignmentScoreReconstruction.sourceScore reconstructed
            (CanonicalAssignmentVector.followerArm p.two_le_m slowSet i) := by
      funext anchor
      funext i
      simp [payload, LaterAssignmentStartOperation.retainedBaseScore,
        LaterAssignmentStartOperation.payloadInput,
        AssignmentStartPayload.Input.assignment]
    rw [heq]
    exact measurable_const
  have hpair : Measurable (fun anchor : PositiveAnchor p =>
      (payload anchor,
        LaterAssignmentStartOperation.retainedBaseScore reconstructed (payload anchor))) :=
    hpayload.prodMk hscore
  have hsome : Measurable (fun anchor : PositiveAnchor p =>
      (some (payload anchor,
        LaterAssignmentStartOperation.retainedBaseScore reconstructed (payload anchor)) :
          PayloadScore? p eta)) := measurable_some_of_measurable _ hpair
  have hdecisionAt (anchor : PositiveAnchor p) :
      LaterAssignmentStartOperation.decideReconstruction
        (payloadWithAnchor old anchor) ledger instruction =
          .success reconstructed hcall := by
    rw [LaterAssignmentJointCodeMeasurability.decideReconstruction_payloadWithAnchor
      old anchor ledger instruction]
    rw [hdecision]
  have heq : (fun anchor : PositiveAnchor p =>
      payloadScoreFromCodeOnSlice c (.sampled outcome) anchor) =
      fun anchor => (some (payload anchor,
        LaterAssignmentStartOperation.retainedBaseScore reconstructed (payload anchor)) :
          PayloadScore? p eta) := by
    funext anchor
    simp [payloadScoreFromCodeOnSlice, old, input, ledger, instruction,
      hdecisionAt anchor, payload, selected, slowSet]
  rw [heq]
  exact hsome

/-- Measurability of the slice payload/score map for each fixed code. -/
private theorem measurable_payloadScoreFromCodeOnSlice
    (c : JointDiscreteObservationRange p eta) :
    Measurable (fun q : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p ×
      PositiveAnchor p => payloadScoreFromCodeOnSlice c q.1 q.2) := by
  apply measurable_from_prod_countable_right
  intro code
  cases code with
  | reconstructionFailure reason => exact measurable_const
  | prefixFailure arm reason => exact measurable_const
  | orientationFailure set => exact measurable_const
  | sampled outcome =>
      cases hdecision : LaterAssignmentStartOperation.decideReconstruction
          (jointInputRepresentative c).1
          (jointInputRepresentative c).2.1
          (jointInputRepresentative c).2.2.1 with
      | failure reason =>
          have hdecisionAt (anchor : PositiveAnchor p) :
              LaterAssignmentStartOperation.decideReconstruction
                (payloadWithAnchor (jointInputRepresentative c).1 anchor)
                (jointInputRepresentative c).2.1
                (jointInputRepresentative c).2.2.1 = .failure reason := by
            rw [LaterAssignmentJointCodeMeasurability.decideReconstruction_payloadWithAnchor]
            rw [hdecision]
          have heq : (fun anchor : PositiveAnchor p =>
              payloadScoreFromCodeOnSlice c (.sampled outcome) anchor) = fun _ => none := by
            funext anchor
            simp [payloadScoreFromCodeOnSlice, hdecisionAt anchor]
          rw [heq]
          exact measurable_const
      | success reconstructed hcall =>
          exact measurable_payloadScore_successSlice c outcome reconstructed hcall hdecision

/-- Measurability of the actual operation's payload/score projection on a
fixed input slice while the genuine anchor and entire complete row vary. -/
private theorem measurable_payloadScoreOnSlice
    (c : JointDiscreteObservationRange p eta) :
    Measurable (fun q : PositiveAnchor p × CompletePublicTable.CompleteRow p =>
      payloadScoreFromCodeOnSlice c
        (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c q) q.1) := by
  exact (measurable_payloadScoreFromCodeOnSlice c).comp
    ((LaterAssignmentJointCodeMeasurability.measurable_operationCodeOnDiscreteSlice c).prodMk
      measurable_fst)

/-- On a fixed slice, the output fields computed from the actual code agree
with the existing optional result projection. -/
theorem payloadScoreFromCodeOnSlice_eq_result
    (c : JointDiscreteObservationRange p eta)
    (anchor : PositiveAnchor p)
    (row : CompletePublicTable.CompleteRow p) :
    payloadScoreFromCodeOnSlice c
        (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
          (anchor, row)) anchor =
      LaterAssignmentStartMeasurability.resultPayloadScore?
        (LaterAssignmentStartOperation.laterAssignmentStart
          (payloadWithAnchor (jointInputRepresentative c).1 anchor)
          (transportLocalStartInput (jointInputRepresentative c).1 anchor
            (jointInputRepresentative c).2).1
          (transportLocalStartInput (jointInputRepresentative c).1 anchor
            (jointInputRepresentative c).2).2.1 row
          (transportLocalStartInput (jointInputRepresentative c).1 anchor
            (jointInputRepresentative c).2).2.2) := by
  let old := (jointInputRepresentative c).1
  let input := (jointInputRepresentative c).2
  let ledger := input.1
  let instruction := input.2.1
  let consistent := input.2.2
  let old' := payloadWithAnchor old anchor
  let input' := transportLocalStartInput old anchor input
  have hledgerInput : input'.1 = ledger :=
    transportLocalStartInput_ledger_eq old anchor input
  have hinstructionInput : input'.2.1 = instruction :=
    transportLocalStartInput_instruction_eq old anchor input
  have hcode :
      LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c (anchor, row) =
        LaterAssignmentStartMeasurability.laterAssignmentStartCode
          old' input'.1 input'.2.1 row input'.2.2 := rfl
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason =>
      have hdecision'' : LaterAssignmentStartOperation.decideReconstruction
          old' input'.1 input'.2.1 = .failure reason := by
        change LaterAssignmentStartOperation.decideReconstruction old' ledger instruction =
          .failure reason
        rw [LaterAssignmentJointCodeMeasurability.decideReconstruction_payloadWithAnchor]
        rw [hdecision]
      have hcodeFailure :
          LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
            (anchor, row) = .reconstructionFailure reason := by
        rw [hcode]
        exact LaterAssignmentStartMeasurability.laterAssignmentStartCode_reconstructionFailure
          old' input' row reason hdecision''
      have hresultFailure :
          LaterAssignmentStartOperation.laterAssignmentStart
            old' input'.1 input'.2.1 row input'.2.2 =
              .reconstructionFailure reason := by
        simp [LaterAssignmentStartOperation.laterAssignmentStart,
          LaterAssignmentStartOperation.runReconstructionDecision, hdecision'']
      change payloadScoreFromCodeOnSlice c
          (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
            (anchor, row)) anchor =
        LaterAssignmentStartMeasurability.resultPayloadScore?
          (LaterAssignmentStartOperation.laterAssignmentStart
            old' input'.1 input'.2.1 row input'.2.2)
      rw [hcodeFailure, hresultFailure]
      simp [payloadScoreFromCodeOnSlice,
        LaterAssignmentStartMeasurability.resultPayloadScore?]
  | success reconstructed hcall =>
      have hdecision'' : LaterAssignmentStartOperation.decideReconstruction
          old' input'.1 input'.2.1 = .success reconstructed hcall := by
        change LaterAssignmentStartOperation.decideReconstruction old' ledger instruction =
          .success reconstructed hcall
        rw [LaterAssignmentJointCodeMeasurability.decideReconstruction_payloadWithAnchor]
        simp [hdecision]
      let selection := LaterAssignmentStartMeasurability.successfulLawSelection
        old' ledger instruction reconstructed hcall
      have hdecisionDirect : LaterAssignmentStartOperation.decideReconstruction
          (payloadWithAnchor (jointInputRepresentative c).1 anchor)
          (jointInputRepresentative c).2.1
          (jointInputRepresentative c).2.2.1 = .success reconstructed hcall := by
        change LaterAssignmentStartOperation.decideReconstruction
          old' ledger instruction = .success reconstructed hcall
        rw [LaterAssignmentJointCodeMeasurability.decideReconstruction_payloadWithAnchor
          old anchor ledger instruction, hdecision]
      have hparameters :
          LaterAssignmentStartMeasurability.selectedSamplerParameters
            old' input'.1 input'.2.1 reconstructed hcall =
          (selection.law.mass, selection.law.anchor) := rfl
      have htimeInput : input'.2.1.time = instruction.time := rfl
      have hrun :
          LaterAssignmentStartOperation.laterAssignmentStart
            old' input'.1 input'.2.1 row input'.2.2 =
          LaterAssignmentStartOperation.finishCheckedSample old' input'.1
            input'.2.1 row input'.2.2 reconstructed hcall selection.cutoffReached
            selection.currentWeightPos selection.cutoffWeightPos selection.law
            selection.lawSelected := by
        unfold LaterAssignmentStartOperation.laterAssignmentStart
        rw [hdecision'']
        rfl
      have hrunNormalized := hrun
      dsimp only [input', transportLocalStartInput, old', payloadWithAnchor] at hrunNormalized
      cases hsampleEq : CheckedAssignmentSample.checkedAssignmentSample p
          selection.law.mass selection.law.anchor
          (LaterAssignmentStartOperation.ownAssignmentVector row instruction.time) with
      | prefixFailure arm failureReason =>
          have hsampleTransport : CheckedAssignmentSample.checkedAssignmentSample p
              selection.law.mass selection.law.anchor
              (LaterAssignmentStartOperation.ownAssignmentVector row input'.2.1.time) =
                .prefixFailure arm failureReason := by
            rw [htimeInput]
            exact hsampleEq
          have hcodeFailure :
              LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
                (anchor, row) = .prefixFailure arm failureReason := by
            rw [hcode, LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_reconstructedFirstCode]
            simp only [LaterAssignmentStartMeasurability.reconstructedFirstCode, hdecision'']
            simp only [hparameters, hsampleTransport]
            rfl
          have hresult :
              LaterAssignmentStartMeasurability.resultPayloadScore?
                (LaterAssignmentStartOperation.laterAssignmentStart
                  old' input'.1 input'.2.1 row input'.2.2) = none := by
            dsimp only [input', transportLocalStartInput, old', payloadWithAnchor]
            rw [hrunNormalized]
            unfold LaterAssignmentStartOperation.finishCheckedSample
            split
            · simp [LaterAssignmentStartMeasurability.resultPayloadScore?]
            · simp [LaterAssignmentStartMeasurability.resultPayloadScore?]
            · rename_i sampled hsampleActual
              have hcontra : CheckedAssignmentSample.Result.sampled sampled =
                  .prefixFailure arm failureReason :=
                hsampleActual.symm.trans hsampleTransport
              cases hcontra
          change payloadScoreFromCodeOnSlice c
              (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
                (anchor, row)) anchor = _
          rw [hcodeFailure, hresult]
          simp [payloadScoreFromCodeOnSlice]
      | orientationFailure set =>
          have hsampleTransport : CheckedAssignmentSample.checkedAssignmentSample p
              selection.law.mass selection.law.anchor
              (LaterAssignmentStartOperation.ownAssignmentVector row input'.2.1.time) =
                .orientationFailure set := by
            rw [htimeInput]
            exact hsampleEq
          have hcodeFailure :
              LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
                (anchor, row) = .orientationFailure set := by
            rw [hcode, LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_reconstructedFirstCode]
            simp only [LaterAssignmentStartMeasurability.reconstructedFirstCode, hdecision'']
            simp only [hparameters, hsampleTransport]
            rfl
          have hresult :
              LaterAssignmentStartMeasurability.resultPayloadScore?
                (LaterAssignmentStartOperation.laterAssignmentStart
                  old' input'.1 input'.2.1 row input'.2.2) = none := by
            dsimp only [input', transportLocalStartInput, old', payloadWithAnchor]
            rw [hrunNormalized]
            unfold LaterAssignmentStartOperation.finishCheckedSample
            split
            · simp [LaterAssignmentStartMeasurability.resultPayloadScore?]
            · simp [LaterAssignmentStartMeasurability.resultPayloadScore?]
            · rename_i sampled hsampleActual
              have hcontra : CheckedAssignmentSample.Result.sampled sampled =
                  .orientationFailure set :=
                hsampleActual.symm.trans hsampleTransport
              cases hcontra
          change payloadScoreFromCodeOnSlice c
              (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
                (anchor, row)) anchor = _
          rw [hcodeFailure, hresult]
          simp [payloadScoreFromCodeOnSlice]
      | sampled outcome =>
          have hsampleTransport : CheckedAssignmentSample.checkedAssignmentSample p
              selection.law.mass selection.law.anchor
              (LaterAssignmentStartOperation.ownAssignmentVector row input'.2.1.time) =
                .sampled outcome := by
            rw [htimeInput]
            exact hsampleEq
          have hcodeSample :
              LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
                (anchor, row) = .sampled outcome := by
            rw [hcode, LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_reconstructedFirstCode]
            simp only [LaterAssignmentStartMeasurability.reconstructedFirstCode, hdecision'']
            simp only [hparameters, hsampleTransport]
            rfl
          let slowSet := CheckedAssignmentOrientation.slowSetAfter p
            outcome.1.1 outcome.1.2 outcome.2
          let payload := LaterAssignmentStartOperation.payloadInput old'
            instruction reconstructed selection.law slowSet
          have hresult :
              LaterAssignmentStartMeasurability.resultPayloadScore?
                (LaterAssignmentStartOperation.laterAssignmentStart
                  old' input'.1 input'.2.1 row input'.2.2) =
                some (payload,
                  LaterAssignmentStartOperation.retainedBaseScore reconstructed payload) := by
            dsimp only [input', transportLocalStartInput, old', payloadWithAnchor]
            rw [hrunNormalized]
            unfold LaterAssignmentStartOperation.finishCheckedSample
            split
            · rename_i armActual reasonActual hsampleActual
              have hcontra : CheckedAssignmentSample.Result.prefixFailure
                  armActual reasonActual = .sampled outcome :=
                hsampleActual.symm.trans hsampleTransport
              cases hcontra
            · rename_i setActual hsampleActual
              have hcontra : CheckedAssignmentSample.Result.orientationFailure
                  setActual = .sampled outcome :=
                hsampleActual.symm.trans hsampleTransport
              cases hcontra
            · rename_i sampled hsampleActual
              have hsampleResult : CheckedAssignmentSample.Result.sampled sampled =
                  .sampled outcome := hsampleActual.symm.trans hsampleTransport
              have houtcome : sampled = outcome := by
                injection hsampleResult
              cases houtcome
              simp [LaterAssignmentStartMeasurability.resultPayloadScore?,
                payload, slowSet, instruction, old', payloadWithAnchor]
              rfl
          have hformula : payloadScoreFromCodeOnSlice c (.sampled outcome) anchor =
              some (payload,
                LaterAssignmentStartOperation.retainedBaseScore reconstructed payload) := by
            dsimp only [payloadScoreFromCodeOnSlice]
            rw [LaterAssignmentJointCodeMeasurability.decideReconstruction_payloadWithAnchor
              old anchor ledger instruction]
            rw [hdecision]
          change payloadScoreFromCodeOnSlice c
              (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
                (anchor, row)) anchor = _
          rw [hcodeSample, hresult]
          exact hformula

/-- The actual output payload and score equal the slice formula, by the
accepted faithful input reanchoring and the operation's exact sampled code. -/
theorem actualPayloadScore_eq_slice (z : JointOperationInput p eta) :
    actualPayloadScore? z =
      payloadScoreFromCodeOnSlice (jointDiscreteRange z.1)
        (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice
          (jointDiscreteRange z.1)
          (jointPositiveAnchor z.1, z.2))
        (jointPositiveAnchor z.1) := by
  let c := jointDiscreteRange z.1
  have hin := jointInput_eq_reanchoredRepresentative z
  have hslice := payloadScoreFromCodeOnSlice_eq_result c (jointPositiveAnchor z.1) z.2
  let rep : JointLocalStartInput p eta :=
    ⟨payloadWithAnchor (jointInputRepresentative c).1 (jointPositiveAnchor z.1),
      transportLocalStartInput (jointInputRepresentative c).1
        (jointPositiveAnchor z.1) (jointInputRepresentative c).2⟩
  have hprojection : actualPayloadScore? (rep, z.2) =
      actualPayloadScore? z := congrArg (fun input : JointLocalStartInput p eta =>
        actualPayloadScore? (input, z.2)) hin
  calc
    actualPayloadScore? z = actualPayloadScore? (rep, z.2) :=
      hprojection.symm
    _ = payloadScoreFromCodeOnSlice c
        (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice c
          (jointPositiveAnchor z.1, z.2)) (jointPositiveAnchor z.1) := by
      change LaterAssignmentStartMeasurability.resultPayloadScore?
        (actualResult (rep, z.2)) = _
      dsimp [actualResult, rep]
      exact hslice.symm

/-- The payload score observation on a slice is the existing payload
observation applied to the exact actual payload. -/
noncomputable def payloadScoreObservationFromInput? (values : PayloadScore? p eta) :
    Option (PayloadScoreObservation p) :=
  values.map fun payloadScore =>
    (LaterAssignmentStartMeasurability.payloadObservation payloadScore.1,
      payloadScore.2)

/-- The derived-field observation is the existing literal payload producer,
applied only on the actual successful output branch. -/
noncomputable def derivedFieldsFromInput? (values : PayloadScore? p eta) :
    Option (DerivedOutputFields p) :=
  values.map fun payloadScore =>
    AssignmentPayloadDerivedMeasurability.inputDerivedFields payloadScore.1

/-- The payload/score projection is Borel on the actual varying domain. -/
theorem measurable_actualPayloadScore? :
    Measurable (actualPayloadScore? (p := p) (eta := eta)) := by
  have hs : Measurable (fun q : JointDiscreteObservationRange p eta ×
      (PositiveAnchor p × CompletePublicTable.CompleteRow p) =>
      payloadScoreFromCodeOnSlice q.1
        (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice q.1 q.2)
        q.2.1) :=
    measurable_from_prod_countable_right measurable_payloadScoreOnSlice
  have heq : actualPayloadScore? (p := p) (eta := eta) = fun z =>
      payloadScoreFromCodeOnSlice (jointDiscreteRange z.1)
        (LaterAssignmentAnchorMeasurability.operationCodeOnDiscreteSlice
          (jointDiscreteRange z.1)
          (jointPositiveAnchor z.1, z.2))
        (jointPositiveAnchor z.1) := funext actualPayloadScore_eq_slice
  rw [heq]
  exact hs.comp
    ((measurable_jointDiscreteRange.comp measurable_fst).prodMk
      ((measurable_jointPositiveAnchor.comp measurable_fst).prodMk measurable_snd))

/-- The full optional payload/score observation is Borel in the existing
payloadObservation comap space. -/
theorem measurable_actualPayloadScoreObservation? :
    Measurable (actualPayloadScoreObservation? (p := p) (eta := eta)) := by
  have hpayloadObservation : Measurable
      (LaterAssignmentStartMeasurability.payloadObservation
        (p := p) (eta := eta)) := comap_measurable _
  exact measurable_optionMap
    (fun payloadScore : AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ) =>
      (LaterAssignmentStartMeasurability.payloadObservation payloadScore.1,
        payloadScore.2))
    ((hpayloadObservation.comp measurable_fst).prodMk measurable_snd)
    (actualPayloadScore? (p := p) (eta := eta)) measurable_actualPayloadScore?

/-- The optional full rate/exponent/auxiliary output tuple is Borel. -/
theorem measurable_actualDerivedFields? :
    Measurable (actualDerivedFields? (p := p) (eta := eta)) := by
  exact measurable_optionMap
    (fun payloadScore : AssignmentStartPayload.Input p eta × (Fin (p.m - 1) → ℕ) =>
      AssignmentPayloadDerivedMeasurability.inputDerivedFields payloadScore.1)
    (AssignmentPayloadDerivedMeasurability.measurable_inputDerivedFields.comp
      measurable_fst)
    (actualPayloadScore? (p := p) (eta := eta)) measurable_actualPayloadScore?

/-- Measurability of the complete actual output observation on the existing
JointLocalStartInput × CompleteRow domain. -/
theorem measurable_laterAssignmentFullOutputObservation :
    Measurable (laterAssignmentFullOutputObservation (p := p) (eta := eta)) := by
  have hcode : Measurable
      (LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap
        (p := p) (eta := eta)) :=
    LaterAssignmentJointCodeMeasurability.measurable_laterAssignmentStartCodeMap
  have hparams : Measurable (fun z : JointOperationInput p eta =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters?
        z.1.1 z.1.2) :=
    LaterAssignmentJointCodeMeasurability.measurable_selectedSamplerParameters?_joint.comp
      measurable_fst
  exact hcode.prodMk
    (hparams.prodMk
      (measurable_actualPayloadScoreObservation?.prodMk
        (measurable_originalAssignmentVector.prodMk measurable_actualDerivedFields?)))

/-- The complete observation reconstructs the exact existing Result, using
its first (actual code) coordinate and retaining the original varying input
and complete row. -/
theorem decode_laterAssignmentFullOutputObservation_exact
    (z : JointOperationInput p eta) :
    LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2
        (laterAssignmentFullOutputObservation z).1 =
      some (LaterAssignmentStartOperation.laterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2) := by
  rw [fullOutput_code]
  exact LaterAssignmentJointCodeMeasurability.decode_laterAssignmentStartCodeMap_exact z

/-- On a successful result, the payload/score observation is precisely the
literal SuccessfulStart payload and reconstructed base-score vector. -/
theorem fullOutput_success_payloadScore
    (z : JointOperationInput p eta)
    (output : LaterAssignmentStartOperation.SuccessfulStart
      z.1.1 z.1.2.1 z.1.2.2.1 z.2)
    (hconsistent : output.localConsistency = z.1.2.2.2)
    (hresult : actualResult z = .success output hconsistent) :
    (laterAssignmentFullOutputObservation z).2.2.1 =
      some (LaterAssignmentStartMeasurability.payloadObservation output.payload,
        output.baseScore) := by
  change (LaterAssignmentStartMeasurability.resultPayloadScore? (actualResult z)).map
      (fun payloadScore =>
        (LaterAssignmentStartMeasurability.payloadObservation payloadScore.1,
          payloadScore.2)) = _
  rw [hresult]
  rfl

/-- On success, the rate/exponent/auxiliary coordinate is the literal derived
projection of the exact emitted payload. -/
theorem fullOutput_success_derivedFields
    (z : JointOperationInput p eta)
    (output : LaterAssignmentStartOperation.SuccessfulStart
      z.1.1 z.1.2.1 z.1.2.2.1 z.2)
    (hconsistent : output.localConsistency = z.1.2.2.2)
    (hresult : actualResult z = .success output hconsistent) :
    (laterAssignmentFullOutputObservation z).2.2.2.2 =
      some (AssignmentPayloadDerivedMeasurability.inputDerivedFields output.payload) := by
  change (LaterAssignmentStartMeasurability.resultPayloadScore? (actualResult z)).map
      (fun payloadScore =>
        AssignmentPayloadDerivedMeasurability.inputDerivedFields payloadScore.1) = _
  rw [hresult]
  rfl

/-- The result decoder is exact for every failure constructor as well as
success; in particular each actual failure payload is retained by the first
output coordinate. -/
theorem fullOutput_code_decodes_exactly
    (z : JointOperationInput p eta) :
    LaterAssignmentStartMeasurability.decodeLaterAssignmentStart
        z.1.1 z.1.2.1 z.1.2.2.1 z.2 z.1.2.2.2
        (laterAssignmentFullOutputObservation z).1 =
      some (actualResult z) :=
  decode_laterAssignmentFullOutputObservation_exact z

/-- Arbitrary-base composition: callers provide separately measurable maps
to the existing varying local input and the whole original complete row. No
opaque assembled-input measurability premise is introduced. -/
theorem measurable_laterAssignmentFullOutputObservation_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (row : X → CompletePublicTable.CompleteRow p)
    (hinput : Measurable input) (hrow : Measurable row) :
    Measurable (fun x => laterAssignmentFullOutputObservation (input x, row x)) := by
  exact measurable_laterAssignmentFullOutputObservation.comp (hinput.prodMk hrow)

/-- Arbitrary-base composition for the original variable-time full K+1 row
vector. -/
theorem measurable_originalAssignmentVector_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (row : X → CompletePublicTable.CompleteRow p)
    (hinput : Measurable input) (hrow : Measurable row) :
    Measurable (fun x =>
      LaterAssignmentStartOperation.ownAssignmentVector (row x)
        (input x).2.2.1.time) :=
  measurable_originalAssignmentVector.comp (hinput.prodMk hrow)

/-- Arbitrary-base composition for the optional actual selected raw mass and
real anchor. -/
theorem measurable_selectedSamplerParameters?_comp
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (hinput : Measurable input) :
    Measurable (fun x =>
      LaterAssignmentStartMeasurability.selectedSamplerParameters?
        (input x).1 (input x).2) :=
  LaterAssignmentJointCodeMeasurability.measurable_selectedSamplerParameters?_comp
    input hinput

/-- The exported product observation keeps the fieldwise component
obligations explicit: the actual joint input and full complete row must each
be measurable on the caller's base. -/
theorem measurable_fullOutput_of_components
    {X : Type*} [MeasurableSpace X]
    (input : X → JointLocalStartInput p eta)
    (row : X → CompletePublicTable.CompleteRow p)
    (hinput : Measurable input) (hrow : Measurable row) :
    Measurable (fun x => laterAssignmentFullOutputObservation (input x, row x)) :=
  measurable_laterAssignmentFullOutputObservation_comp input row hinput hrow

end Bandits.Support.LaterAssignmentFullOutputMeasurability

end
