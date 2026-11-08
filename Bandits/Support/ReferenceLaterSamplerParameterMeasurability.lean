/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCollectionDispatchMeasurability
public import Bandits.Support.ReferenceLaterPhysicalFibreResampling

/-!
# Borel measurability of the actual later-sampler parameter selector

The optional parameter is the exact value returned by the physical
collection selector. The local proof feeds the actual checked core and
instruction into the varying-payload, varying-anchor later-start observation;
the canonical proof then uses the physical cutoff and existing collection
coordinates. The paired kernel is pulled back only to inputs where this
selector actually returns `some`.

Sources: `sources/zip4/manuscript/06_interruptions.tex:30-69,376-423`,
`sources/zip4/manuscript/appendix_a_local_protocol.tex:6-14`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-55`.

This internal Borel kernel does not supply the chronological original-row
coupling, a conditional law given adaptive history, a full STEP or horizon
theorem, source approval, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open ProbabilityTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceCollectionDispatchMeasurability
open Bandits.Support.ReferenceLaterAssignmentFibreStep
open Bandits.Support.ReferenceLaterPhysicalFibreResampling
open Bandits.Support.LaterAssignmentStartMeasurability
open Bandits.Support.LaterAssignmentFullOutputMeasurability

namespace Bandits.Support.ReferenceLaterSamplerParameterMeasurability

variable {p : ConstructorDimensions.Parameters}
  {rate : ReferenceActivePhysicalStep.RateInput p}

local instance startResultMeasurableSpace :
    MeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⊤
local instance startResultDiscrete :
    DiscreteMeasurableSpace (CoordinatorPhaseClock.StartRoundResult p) := ⟨fun _ => trivial⟩
local instance clockFailureMeasurableSpace :
    MeasurableSpace CoordinatorPhaseClock.ClockFailure := ⊤
local instance clockFailureDiscrete :
    DiscreteMeasurableSpace CoordinatorPhaseClock.ClockFailure := ⟨fun _ => trivial⟩
local instance clockObservationMeasurableSpace :
    MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤
local instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace
local instance pairedKernel_isMarkovKernel (p : ConstructorDimensions.Parameters) :
    IsMarkovKernel (ReferenceLaterPhysicalFibreResampling.pairedKernel p) :=
  ReferenceLaterPhysicalFibreResampling.instIsMarkovKernelPairedKernel p

abbrev LaterOutputObservation (p : ConstructorDimensions.Parameters) :=
  LaterAssignmentFullOutputMeasurability.FullOutputObservation p

private theorem measurable_optionBind {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (input : X → Option Y) (hinput : Measurable input)
    (f : Y → Option Z) (hf : Measurable f) :
    Measurable (fun x => (input x).bind f) := by
  classical
  intro s hs
  let someImage : Set (Option Y) := some '' (f ⁻¹' s)
  have hsome : MeasurableSet someImage := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit Y)] someImage
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨Sum.inl '' (f ⁻¹' s), measurableSet_inl_image.mpr (hf hs), ?_⟩
    ext value
    cases value <;> simp [someImage]
  have hnone : MeasurableSet ({none} : Set (Option Y)) := by
    change MeasurableSet[
      (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
        (Equiv.optionEquivSumPUnit Y)] {none}
    rw [MeasurableSpace.measurableSet_comap]
    refine ⟨{Sum.inr PUnit.unit}, ?_, ?_⟩
    · convert measurableSet_inr_image.mpr (measurableSet_singleton PUnit.unit) using 1
      ext value
      simp
    ext value
    cases value <;> simp
  have hpre :
      (fun x => (input x).bind f) ⁻¹' s = input ⁻¹'
        (someImage ∪ if (none : Option Z) ∈ s then
          ({(none : Option Y)} : Set (Option Y)) else ∅) := by
    ext x
    cases h : input x <;> simp [h, someImage]
  have hrest : MeasurableSet (if (none : Option Z) ∈ s then
      ({(none : Option Y)} : Set (Option Y)) else ∅) := by
    by_cases h : (none : Option Z) ∈ s
    · simpa [h] using hnone
    · simp [h]
  have hmeas := hinput (hsome.union hrest)
  rw [← hpre] at hmeas
  exact hmeas

/-- Read exactly the optional parameter coordinate from an existing full
later-start observation. Reconstruction failure remains `none` in this
coordinate. Later prefix and orientation failures stay in the separate first
code coordinate and do not erase the already selected parameter. -/
def parametersFromLaterOutput? (output : Option (LaterOutputObservation p)) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  output.bind fun observation => observation.2.1

theorem measurable_parametersFromLaterOutput? :
    Measurable (parametersFromLaterOutput? (p := p)) := by
  exact measurable_optionBind id measurable_id
    (fun observation : LaterOutputObservation p => observation.2.1)
    (measurable_fst.comp measurable_snd)

/-- The pre-sampler parameters from an unrestricted canonical collection
product. This is literally the accepted full-output selector after the
actual clock, core, empty-pending, and instruction checks. -/
def localParameters? (z : ReferenceCollectionDispatchMeasurability.LocalInput p rate) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  parametersFromLaterOutput? (ReferenceCollectionDispatchMeasurability.laterObservation? z)

theorem measurable_localParameters? : Measurable (localParameters? (p := p) (rate := rate)) :=
  measurable_parametersFromLaterOutput?.comp
    ReferenceCollectionDispatchMeasurability.measurable_laterObservation?

/-- The local observation runs the same selected-parameter operation as the
literal collection selector, including its absence on every no-call path. -/
theorem collectionParameters?_eq_localParameters?
    (z : ReferenceCollectionDispatchMeasurability.LocalInput p rate) :
    ReferenceLaterAssignmentFibreStep.collectionParameters?
        (ReferenceCollectionDispatchMeasurability.assemble z) = localParameters? z := by
  classical
  cases hclock : CoordinatorPhaseClock.startRound p rate.eta.val z.2.2.2.2.1
      (ReferenceActivePhysicalStep.collectionClock z.1.1 z.2.1 z.2.2.1 z.2.2.2.2.2)
      z.2.1.pending with
  | error reason =>
      have hclockObs : ReferenceCollectionDispatchMeasurability.clockObservation z = .inl reason := by
        simp [ReferenceCollectionDispatchMeasurability.clockObservation,
          ReferenceCollectionDispatchMeasurability.assemble, hclock]
      have hclockAssembled : CoordinatorPhaseClock.startRound p
          (ReferenceCollectionDispatchMeasurability.assemble z).etaReal
          (ReferenceCollectionDispatchMeasurability.assemble z).time
          (ReferenceCollectionDispatchMeasurability.assemble z).clock
          (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending = .error reason := by
        simpa [ReferenceCollectionDispatchMeasurability.assemble] using hclock
      by_cases hcore : CoordinatorRoundDispatch.CollectionCoreValid
          (ReferenceCollectionDispatchMeasurability.assemble z)
      · simp [localParameters?, parametersFromLaterOutput?,
          ReferenceCollectionDispatchMeasurability.laterObservation?,
          ReferenceCollectionDispatchMeasurability.laterObservationAtClock,
          ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
          ReferenceCollectionDispatchMeasurability.laterObservationForInstruction,
          ReferenceLaterAssignmentFibreStep.collectionParameters?,
          hclockAssembled, hclockObs, dite_eq_left hcore]
      · simp [localParameters?, parametersFromLaterOutput?,
          ReferenceCollectionDispatchMeasurability.laterObservation?,
          ReferenceCollectionDispatchMeasurability.laterObservationAtClock,
          ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
          ReferenceCollectionDispatchMeasurability.laterObservationForInstruction,
          ReferenceLaterAssignmentFibreStep.collectionParameters?,
          hclockAssembled, hclockObs, dite_eq_right hcore]
  | ok started =>
      have hclockObs : ReferenceCollectionDispatchMeasurability.clockObservation z = .inr started := by
        simp [ReferenceCollectionDispatchMeasurability.clockObservation,
          ReferenceCollectionDispatchMeasurability.assemble, hclock]
      have hclockAssembled : CoordinatorPhaseClock.startRound p
          (ReferenceCollectionDispatchMeasurability.assemble z).etaReal
          (ReferenceCollectionDispatchMeasurability.assemble z).time
          (ReferenceCollectionDispatchMeasurability.assemble z).clock
          (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending = .ok started := by
        simpa [ReferenceCollectionDispatchMeasurability.assemble] using hclock
      by_cases hcore : CoordinatorRoundDispatch.CollectionCoreValid (ReferenceCollectionDispatchMeasurability.assemble z)
      · by_cases hpending : z.2.1.pending.Nonempty
        · have hpendingAssembled :
              (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending.Nonempty := by
            simpa [ReferenceCollectionDispatchMeasurability.assemble] using hpending
          simp [localParameters?, parametersFromLaterOutput?,
            ReferenceCollectionDispatchMeasurability.laterObservation?,
            ReferenceCollectionDispatchMeasurability.laterObservationAtClock,
            ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
            ReferenceCollectionDispatchMeasurability.laterObservationForInstruction,
            ReferenceLaterAssignmentFibreStep.collectionParameters?,
            hclockAssembled, dite_eq_left hcore, hpending, hpendingAssembled]
        · cases hstart : started.assignmentStart with
          | none =>
              have hpendingAssembled :
                  ¬ (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending.Nonempty := by
                simpa [ReferenceCollectionDispatchMeasurability.assemble] using hpending
              simp [localParameters?, parametersFromLaterOutput?,
                ReferenceCollectionDispatchMeasurability.laterObservation?,
                ReferenceCollectionDispatchMeasurability.laterObservationAtClock,
                ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
                ReferenceCollectionDispatchMeasurability.laterObservationForInstruction,
                ReferenceLaterAssignmentFibreStep.collectionParameters?,
                hclockAssembled, hclockObs, dite_eq_left hcore,
                hpending, hpendingAssembled, hstart]
          | some instruction =>
              have hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction z = some instruction := by
                change (if z.2.1.pending.Nonempty then none else
                  match ReferenceCollectionDispatchMeasurability.clockObservation z with
                  | .inl _ => none
                  | .inr started => started.assignmentStart) = some instruction
                simp [hclockObs, hpending, hstart]
              have hcons :
                  ReferenceLaterAssignmentFibreStep.collectionConsistency (ReferenceCollectionDispatchMeasurability.assemble z) hcore = ReferenceCollectionDispatchMeasurability.localConsistency ⟨z, hcore⟩ :=
                by
                  unfold ReferenceLaterAssignmentFibreStep.collectionConsistency
                    ReferenceCollectionDispatchMeasurability.localConsistency
                  cases ReferenceLaterAssignmentFibreStep.collectionConsistency
                    (ReferenceCollectionDispatchMeasurability.assemble z) hcore with
                  | mk a b c d =>
                    cases ReferenceCollectionDispatchMeasurability.localConsistency
                      ⟨z, hcore⟩ with
                    | mk a' b' c' d' => rfl
              have hselector :
                  ReferenceLaterAssignmentFibreStep.collectionParameters?
                      (ReferenceCollectionDispatchMeasurability.assemble z) =
                    LaterAssignmentStartMeasurability.selectedSamplerParameters?
                      z.1.1
                      ⟨CoordinatorRoundDispatch.collectionOperationLedger
                          (ReferenceCollectionDispatchMeasurability.assemble z)
                          hcore.payload_n_eq,
                        instruction,
                        ReferenceCollectionDispatchMeasurability.localConsistency ⟨z, hcore⟩⟩ := by
                have hpendingAssembled :
                    ¬ (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending.Nonempty := by
                  simpa [ReferenceCollectionDispatchMeasurability.assemble] using hpending
                simp only [ReferenceLaterAssignmentFibreStep.collectionParameters?,
                  hclockAssembled, dite_eq_left hcore, ite_eq_right hpendingAssembled, hstart]
                rw [hcons]
                rfl
              calc
                ReferenceLaterAssignmentFibreStep.collectionParameters? (ReferenceCollectionDispatchMeasurability.assemble z) =
                    LaterAssignmentStartMeasurability.selectedSamplerParameters?
                      z.1.1
                      ⟨CoordinatorRoundDispatch.collectionOperationLedger (ReferenceCollectionDispatchMeasurability.assemble z)
                          hcore.payload_n_eq,
                        instruction, ReferenceCollectionDispatchMeasurability.localConsistency ⟨z, hcore⟩⟩ := hselector
                _ = (ReferenceCollectionDispatchMeasurability.laterObservation ⟨z, hcore⟩ instruction).2.1 := by
                  rw [ReferenceCollectionDispatchMeasurability.laterObservation,
                    LaterAssignmentFullOutputMeasurability.fullOutput_selectedParameters]
                  rfl
                _ = localParameters? z := by
                  rw [localParameters?, parametersFromLaterOutput?,
                    ReferenceCollectionDispatchMeasurability.laterObservation?_of_instruction
                      z hcore instruction hrequest]
                  rfl
      · simp [localParameters?, parametersFromLaterOutput?,
          ReferenceCollectionDispatchMeasurability.laterObservation?,
          ReferenceCollectionDispatchMeasurability.laterObservationAtClock,
          ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
          ReferenceCollectionDispatchMeasurability.laterObservationForInstruction,
          ReferenceLaterAssignmentFibreStep.collectionParameters?,
          hclockAssembled, hclockObs, dite_eq_right hcore]

/-- A later operation code other than a reconstruction failure can only be
formed after the actual selected parameter was produced. -/
private theorem selectedSamplerParameters?_isSome_of_code
    (old : AssignmentStartPayload.Input p rate.eta)
    (input : LaterAssignmentStartMeasurability.LocalStartInput old)
    (row : CompletePublicTable.CompleteRow p)
    (code : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p)
    (hcode : LaterAssignmentStartMeasurability.laterAssignmentStartCode
      old input.1 input.2.1 row input.2.2 = code)
    (hnotReconstructionFailure : ∀ failure,
      code ≠ .reconstructionFailure failure) :
    (LaterAssignmentStartMeasurability.selectedSamplerParameters? old input).isSome := by
  classical
  cases hdecision : LaterAssignmentStartOperation.decideReconstruction
      old input.1 input.2.1 with
  | failure failure =>
      have hfailure := LaterAssignmentStartMeasurability.laterAssignmentStartCode_reconstructionFailure
        old input row failure hdecision
      exact False.elim (hnotReconstructionFailure failure (hcode.symm.trans hfailure))
  | success output hcall =>
      rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
      simp [hdecision]

/-- The actual pre-sampler parameter is absent on the accepted reconstruction
failure path, with its exact failure reason retained by the full output code. -/
theorem collectionParameters?_eq_none_of_laterReconstructionFailure
    (z : ReferenceCollectionDispatchMeasurability.CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction z.val =
      some instruction)
    (reason : AssignmentScoreReconstruction.Failure)
    (hdecision : LaterAssignmentStartOperation.decideReconstruction
      (ReferenceCollectionDispatchMeasurability.laterInput z instruction).1
      (ReferenceCollectionDispatchMeasurability.laterInput z instruction).2.1
      (ReferenceCollectionDispatchMeasurability.laterInput z instruction).2.2.1 =
        .failure reason) :
    ReferenceLaterAssignmentFibreStep.collectionParameters?
      (ReferenceCollectionDispatchMeasurability.assemble z.val) = none := by
  let laterInput := ReferenceCollectionDispatchMeasurability.laterInput z instruction
  have hdecision' : LaterAssignmentStartOperation.decideReconstruction
      laterInput.1 laterInput.2.1 laterInput.2.2.1 = .failure reason := by
    simpa [laterInput] using hdecision
  have hselected : LaterAssignmentStartMeasurability.selectedSamplerParameters?
      laterInput.1 laterInput.2 = none := by
    rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match]
    rw [hdecision']
  have houtput : (ReferenceCollectionDispatchMeasurability.laterObservation
      z instruction).2.1 =
      LaterAssignmentStartMeasurability.selectedSamplerParameters?
        laterInput.1 laterInput.2 := by
    rw [ReferenceCollectionDispatchMeasurability.laterObservation,
      LaterAssignmentFullOutputMeasurability.fullOutput_selectedParameters]
  have hlocal : localParameters? z.val =
      (ReferenceCollectionDispatchMeasurability.laterObservation z instruction).2.1 := by
    rw [localParameters?, parametersFromLaterOutput?,
      ReferenceCollectionDispatchMeasurability.laterObservation?_of_instruction
        z.val z.property instruction hrequest]
    rfl
  rw [collectionParameters?_eq_localParameters? z.val, hlocal, houtput]
  exact hselected

/-- A real checked-prefix sampler failure still has the parameter selected
before that sampler call. Its exact failure code remains a separate output. -/
theorem collectionParameters?_isSome_of_laterPrefixFailure
    (z : ReferenceCollectionDispatchMeasurability.CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction z.val =
      some instruction)
    (arm : Option (Fin p.K)) (reason : CheckedPrefixSampler.FailureReason)
    (hcode : (ReferenceCollectionDispatchMeasurability.laterObservation z instruction).1 =
      .prefixFailure arm reason) :
    (ReferenceLaterAssignmentFibreStep.collectionParameters?
      (ReferenceCollectionDispatchMeasurability.assemble z.val)).isSome := by
  let laterInput := ReferenceCollectionDispatchMeasurability.laterInput z instruction
  have hoperationCode : LaterAssignmentStartMeasurability.laterAssignmentStartCode
      laterInput.1 laterInput.2.1 laterInput.2.2.1 z.val.1.2 laterInput.2.2.2 =
      .prefixFailure arm reason := by
    change LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap
        (laterInput, z.val.1.2) = .prefixFailure arm reason at hcode
    exact hcode
  have hselected :
      (LaterAssignmentStartMeasurability.selectedSamplerParameters?
        laterInput.1 laterInput.2).isSome :=
    selectedSamplerParameters?_isSome_of_code laterInput.1 laterInput.2
      z.val.1.2 (.prefixFailure arm reason) hoperationCode
      (by intro failure h; cases h)
  have houtput : (ReferenceCollectionDispatchMeasurability.laterObservation
      z instruction).2.1 =
      LaterAssignmentStartMeasurability.selectedSamplerParameters?
        laterInput.1 laterInput.2 := by
    rw [ReferenceCollectionDispatchMeasurability.laterObservation,
      LaterAssignmentFullOutputMeasurability.fullOutput_selectedParameters]
  have houtputSome :
      ((ReferenceCollectionDispatchMeasurability.laterObservation
        z instruction).2.1).isSome := by
    rw [houtput]
    exact hselected
  have hlocal : localParameters? z.val =
      (ReferenceCollectionDispatchMeasurability.laterObservation z instruction).2.1 := by
    rw [localParameters?, parametersFromLaterOutput?,
      ReferenceCollectionDispatchMeasurability.laterObservation?_of_instruction
        z.val z.property instruction hrequest]
    rfl
  rw [collectionParameters?_eq_localParameters? z.val, hlocal]
  exact houtputSome

/-- A later orientation failure likewise keeps the parameter of the sampler
call that returned that exact failure code. -/
theorem collectionParameters?_isSome_of_laterOrientationFailure
    (z : ReferenceCollectionDispatchMeasurability.CoreInput p rate)
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction z.val =
      some instruction)
    (set : PrefixSetSampler.SetCarrier p.K p.m)
    (hcode : (ReferenceCollectionDispatchMeasurability.laterObservation z instruction).1 =
      .orientationFailure set) :
    (ReferenceLaterAssignmentFibreStep.collectionParameters?
      (ReferenceCollectionDispatchMeasurability.assemble z.val)).isSome := by
  let laterInput := ReferenceCollectionDispatchMeasurability.laterInput z instruction
  have hoperationCode : LaterAssignmentStartMeasurability.laterAssignmentStartCode
      laterInput.1 laterInput.2.1 laterInput.2.2.1 z.val.1.2 laterInput.2.2.2 =
      .orientationFailure set := by
    change LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap
        (laterInput, z.val.1.2) = .orientationFailure set at hcode
    exact hcode
  have hselected :
      (LaterAssignmentStartMeasurability.selectedSamplerParameters?
        laterInput.1 laterInput.2).isSome :=
    selectedSamplerParameters?_isSome_of_code laterInput.1 laterInput.2
      z.val.1.2 (.orientationFailure set) hoperationCode
      (by intro failure h; cases h)
  have houtput : (ReferenceCollectionDispatchMeasurability.laterObservation
      z instruction).2.1 =
      LaterAssignmentStartMeasurability.selectedSamplerParameters?
        laterInput.1 laterInput.2 := by
    rw [ReferenceCollectionDispatchMeasurability.laterObservation,
      LaterAssignmentFullOutputMeasurability.fullOutput_selectedParameters]
  have houtputSome :
      ((ReferenceCollectionDispatchMeasurability.laterObservation
        z instruction).2.1).isSome := by
    rw [houtput]
    exact hselected
  have hlocal : localParameters? z.val =
      (ReferenceCollectionDispatchMeasurability.laterObservation z instruction).2.1 := by
    rw [localParameters?, parametersFromLaterOutput?,
      ReferenceCollectionDispatchMeasurability.laterObservation?_of_instruction
        z.val z.property instruction hrequest]
    rfl
  rw [collectionParameters?_eq_localParameters? z.val, hlocal]
  exact houtputSome

/-- Extract the selector from the pre-choice diagnostic's actual full-output
coordinate. -/
def parametersFromPrechoice (diagnostics :
    ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  parametersFromLaterOutput? diagnostics.2.2.2.2

theorem measurable_parametersFromPrechoice :
    Measurable (parametersFromPrechoice (p := p)) := by
  exact measurable_parametersFromLaterOutput?.comp
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id))))

/-- Decode only a present valid-boundary diagnostic. A malformed physical
cutoff carries `.inl ()` and therefore yields no sampler parameter. -/
def parametersFromBoundary (diagnostics : Unit ⊕
    ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  Sum.elim (fun _ : Unit => none) parametersFromPrechoice diagnostics

theorem measurable_parametersFromBoundary :
    Measurable (parametersFromBoundary (p := p)) :=
  measurable_fun_sum measurable_const measurable_parametersFromPrechoice

/-- The boundary diagnostic selector is exactly the local collection
selector on a valid physical cutoff. -/
theorem parametersFromBoundary_eq_collectionParameters?
    (z : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate)
    (hcutoff : ReferenceCollectionDispatchMeasurability.cutoffValid z) :
    parametersFromBoundary (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics z) =
      ReferenceLaterAssignmentFibreStep.collectionParameters?
        (ReferenceCollectionDispatchMeasurability.assemble
          (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨z, hcutoff⟩)) := by
  simp only [ReferenceCollectionDispatchMeasurability.boundaryDiagnostics, hcutoff,
    parametersFromBoundary,
    ReferenceCollectionDispatchMeasurability.prechoiceDiagnostics]
  exact (collectionParameters?_eq_localParameters?
    (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨z, hcutoff⟩)).symm

/-- Read the optional canonical collection coordinate while keeping all
non-collection and malformed-cutoff cases absent. -/
def parametersFromCanonicalDiagnostics (diagnostics : Option
    (Unit ⊕ ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p)) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  diagnostics.bind parametersFromBoundary

theorem measurable_parametersFromCanonicalDiagnostics :
    Measurable (parametersFromCanonicalDiagnostics (p := p)) :=
  measurable_optionBind id measurable_id parametersFromBoundary measurable_parametersFromBoundary

/-- The exact `ReferenceLaterAssignmentFibreStep.parameters?` projection on
the existing physical round input and its canonical schema. -/
def parameters? (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  ReferenceLaterAssignmentFibreStep.parameters? x

/-- The physical parameter selector depends on the original state and time.
All other RoundInput coordinates, including the selected complete row, are
irrelevant by the literal collection row-independence theorem. -/
theorem parameters?_eq_of_state_eq_time_eq
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hstate : x.state = y.state) (htime : x.time = y.time) :
    parameters? x = parameters? y := by
  cases x with
  | mk xstate xrows xselected xtime xactive xrewards =>
    cases y with
    | mk ystate yrows yselected ytime yactive yrewards =>
      dsimp at hstate htime
      subst ystate
      subst ytime
      change ReferenceLaterAssignmentFibreStep.parameters?
          ⟨xstate, xrows, xselected, xtime, xactive, xrewards⟩ =
        ReferenceLaterAssignmentFibreStep.parameters?
          ⟨xstate, yrows, yselected, xtime, yactive, yrewards⟩
      cases hcoord : xstate.coordinator with
      | first => simp [ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
      | live registers owned baseScores =>
          simp [ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
      | dagger => simp [ReferenceLaterAssignmentFibreStep.parameters?, hcoord]
      | collection payload ledger proposal =>
          by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
          · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
            let inputX := ReferenceActivePhysicalStep.collectionInput
              ⟨xstate, xrows, xselected, xtime, xactive, xrewards⟩ payload ledger
              (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff
            let inputY := ReferenceActivePhysicalStep.collectionInput
              ⟨xstate, yrows, yselected, xtime, yactive, yrewards⟩ payload ledger
              (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff) cutoff
            have hx : ReferenceLaterAssignmentFibreStep.parameters?
                ⟨xstate, xrows, xselected, xtime, xactive, xrewards⟩ =
                ReferenceLaterAssignmentFibreStep.collectionParameters? inputX := by
              simp [ReferenceLaterAssignmentFibreStep.parameters?, hcoord, hcutoff,
                cutoff, inputX]
            have hy : ReferenceLaterAssignmentFibreStep.parameters?
                ⟨xstate, yrows, yselected, xtime, yactive, yrewards⟩ =
                ReferenceLaterAssignmentFibreStep.collectionParameters? inputY := by
              simp [ReferenceLaterAssignmentFibreStep.parameters?, hcoord, hcutoff,
                cutoff, inputY]
            have hinput : inputY = {inputX with row := yrows yselected} := by
              simp [inputX, inputY, ReferenceActivePhysicalStep.collectionInput,
                ReferenceActivePhysicalStep.RoundInput.row]
            rw [hx, hy, hinput]
            exact (ReferenceLaterAssignmentFibreStep.collectionParameters?_row inputX
              (yrows yselected)).symm
          · simp [ReferenceLaterAssignmentFibreStep.parameters?, hcoord, hcutoff]

theorem parameters?_eq_canonicalDiagnostics (x :
    ReferenceActivePhysicalStep.RoundInput p rate) :
    parameters? x = parametersFromCanonicalDiagnostics
      (ReferenceCollectionDispatchMeasurability.canonicalDiagnostics x) := by
  classical
  cases hphase : x.state.coordinator with
  | first =>
      simp [parameters?, parametersFromCanonicalDiagnostics,
        ReferenceCollectionDispatchMeasurability.canonicalDiagnostics,
        ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics,
        ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceLaterAssignmentFibreStep.parameters?, hphase]
  | live registers owned baseScores =>
      simp [parameters?, parametersFromCanonicalDiagnostics,
        ReferenceCollectionDispatchMeasurability.canonicalDiagnostics,
        ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics,
        ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceLaterAssignmentFibreStep.parameters?, hphase]
  | collection payload ledger proposal =>
      let boundary : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
        ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time)
      have hcanon : ReferenceCollectionDispatchMeasurability.canonicalDiagnostics x =
          some (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics boundary) :=
        ReferenceCollectionDispatchMeasurability.canonicalDiagnostics_collection
          x payload ledger proposal hphase
      by_cases hcutoff : 1 ≤ ledger.cutoff ∧ ledger.cutoff ≤ p.T
      · let cutoff : Fin p.T := ⟨ledger.cutoff - 1, by omega⟩
        have hlocal : ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary, hcutoff⟩ =
            ((payload, x.row), ledger, proposal, x.state.upDecoderBank, x.time, cutoff) := by
          rfl
        have hassemble : ReferenceCollectionDispatchMeasurability.assemble (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary, hcutoff⟩) =
            ReferenceActivePhysicalStep.collectionInput x payload ledger
              (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff)
              cutoff := by
          rw [hlocal]
          exact ReferenceCollectionDispatchMeasurability.assemble_eq_collectionInput x payload ledger proposal cutoff
        calc
          ReferenceLaterAssignmentFibreStep.parameters? x = ReferenceLaterAssignmentFibreStep.collectionParameters?
              (ReferenceActivePhysicalStep.collectionInput x payload ledger
                (ReferenceActivePhysicalStep.collectionClock payload ledger proposal cutoff)
                cutoff) := by
                simp [ReferenceLaterAssignmentFibreStep.parameters?, hphase, hcutoff, cutoff]
          _ = ReferenceLaterAssignmentFibreStep.collectionParameters? (ReferenceCollectionDispatchMeasurability.assemble (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary, hcutoff⟩)) := by
                rw [hassemble]
          _ = parametersFromBoundary (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics boundary) :=
                (parametersFromBoundary_eq_collectionParameters? boundary hcutoff).symm
          _ = parametersFromCanonicalDiagnostics
              (ReferenceCollectionDispatchMeasurability.canonicalDiagnostics x) := by
                rw [hcanon]
                rfl
      · rw [ReferenceCollectionDispatchMeasurability.canonicalDiagnostics_invalid
          x payload ledger proposal hphase hcutoff]
        simp [parameters?, parametersFromCanonicalDiagnostics,
          parametersFromBoundary, ReferenceLaterAssignmentFibreStep.parameters?,
          hphase, hcutoff]
  | dagger =>
      simp [parameters?, parametersFromCanonicalDiagnostics,
        ReferenceCollectionDispatchMeasurability.canonicalDiagnostics,
        ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics,
        ReferenceCollectionDispatchMeasurability.collectionCoordinates?,
        ReferenceActivePhysicalStepMeasurability.encodeCoordinator,
        ReferenceLaterAssignmentFibreStep.parameters?, hphase]

theorem measurable_parameters? :
    Measurable (parameters? (p := p) (rate := rate)) := by
  rw [show parameters? = fun x => parametersFromCanonicalDiagnostics
      (ReferenceCollectionDispatchMeasurability.canonicalDiagnostics x) from
        funext parameters?_eq_canonicalDiagnostics]
  exact measurable_parametersFromCanonicalDiagnostics.comp
    (ReferenceCollectionDispatchMeasurability.measurable_canonicalDiagnostics
      (p := p) (rate := rate))

/-- Arbitrary-base composition for the exact physical optional selector. -/
theorem measurable_parameters?_comp {X : Type*} [MeasurableSpace X]
    (input : X → ReferenceActivePhysicalStep.RoundInput p rate)
    (hinput : Measurable input) :
    Measurable (fun x => parameters? (input x)) :=
  measurable_parameters?.comp hinput

private theorem measurableSet_option_some (theta : AssignmentParameterFibreKernel.Theta p) :
    MeasurableSet ({some theta} : Set (Option (AssignmentParameterFibreKernel.Theta p))) := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace
      (AssignmentParameterFibreKernel.Theta p ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit (AssignmentParameterFibreKernel.Theta p))]
    ({some theta} : Set (Option (AssignmentParameterFibreKernel.Theta p)))
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{Sum.inl theta}, ?_, ?_⟩
  · convert measurableSet_inl_image.mpr (measurableSet_singleton theta) using 1
    ext value
    simp
  ext value
  cases value <;> simp

private theorem measurableSet_option_none :
    MeasurableSet ({none} : Set (Option (AssignmentParameterFibreKernel.Theta p))) := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace
      (AssignmentParameterFibreKernel.Theta p ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit (AssignmentParameterFibreKernel.Theta p))]
    ({none} : Set (Option (AssignmentParameterFibreKernel.Theta p)))
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨{Sum.inr PUnit.unit}, ?_, ?_⟩
  · convert measurableSet_inr_image.mpr (measurableSet_singleton PUnit.unit) using 1
    ext value
    simp
  ext value
  cases value <;> simp

/-- Exact measurable event for any fixed raw-mass and orientation-weight
parameter in the original Borel `Theta` carrier. -/
theorem measurableSet_parameters?_eq_some
    (theta : AssignmentParameterFibreKernel.Theta p) :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      parameters? x = some theta} := by
  exact measurable_parameters? (measurableSet_option_some theta)

/-- Exact measurable event for every clock, core, pending, or reconstruction
failure represented by the optional selector. -/
theorem measurableSet_parameters?_eq_none :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      parameters? x = none} :=
  measurable_parameters? measurableSet_option_none

private theorem measurableSet_option_isSome :
    MeasurableSet {value : Option (AssignmentParameterFibreKernel.Theta p) |
      value.isSome} := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace
      (AssignmentParameterFibreKernel.Theta p ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit (AssignmentParameterFibreKernel.Theta p))]
    {value : Option (AssignmentParameterFibreKernel.Theta p) | value.isSome}
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Set.range (Sum.inl : AssignmentParameterFibreKernel.Theta p →
    AssignmentParameterFibreKernel.Theta p ⊕ PUnit), ?_, ?_⟩
  · exact measurableSet_range_inl
  · ext value
    cases value <;> simp

/-- Exact measurable event on which the actual later sampler is called. -/
theorem measurableSet_parameters?_isSome :
    MeasurableSet {x : ReferenceActivePhysicalStep.RoundInput p rate |
      (parameters? x).isSome} :=
  measurable_parameters? measurableSet_option_isSome

/-- The actual sampler-call domain is a subtype of the existing physical
round input; its witness records precisely that the real selector succeeds. -/
abbrev ActualSamplerCall :=
  {x : ReferenceActivePhysicalStep.RoundInput p rate // (parameters? x).isSome}

/-- The subtype projection is the parameter returned by the actual selector.
It is undefined outside the actual-call domain rather than defaulted. -/
def actualParameter (x : ActualSamplerCall (p := p) (rate := rate)) :
    AssignmentParameterFibreKernel.Theta p :=
  (parameters? x.val).get x.property

private theorem measurable_some_image {Y : Type*} [MeasurableSpace Y]
    {s : Set Y} (hs : MeasurableSet s) :
    MeasurableSet (some '' s : Set (Option Y)) := by
  change MeasurableSet[(inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
    (Equiv.optionEquivSumPUnit Y)] (some '' s)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' s, measurableSet_inl_image.mpr hs, ?_⟩
  ext value
  cases value <;> simp

/-- Measurability of `Option.get` on the subtype where the option is present.
No value is assigned on the absent branch. -/
private theorem measurable_get_on_isSome {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Option Y) (hf : Measurable f) :
    Measurable (fun x : {x : X // (f x).isSome} => (f x.val).get x.property) := by
  intro s hs
  have hoption : MeasurableSet (some '' s : Set (Option Y)) := measurable_some_image hs
  have hf' : Measurable (fun x : {x : X // (f x).isSome} => f x.val) :=
    hf.comp measurable_subtype_coe
  have hpre :
      (fun x : {x : X // (f x).isSome} => (f x.val).get x.property) ⁻¹' s =
        (fun x : {x : X // (f x).isSome} => f x.val) ⁻¹' (some '' s) := by
    ext x
    cases hfx : f x.val with
    | none =>
        have hx := x.property
        simp [hfx] at hx
    | some value => simp [hfx]
  rw [hpre]
  exact hf' hoption

theorem measurable_actualParameter :
    Measurable (actualParameter (p := p) (rate := rate)) := by
  exact measurable_get_on_isSome parameters? measurable_parameters?

/-- The paired full-vector kernel at the parameter actually selected by the
physical input, pulled back to the genuine sampler-call subtype. -/
def actualPairedKernel : Kernel (ActualSamplerCall (p := p) (rate := rate))
    (CheckedAssignmentSample.AssignmentVector p ×
      CheckedAssignmentSample.AssignmentVector p) :=
  ReferenceLaterPhysicalFibreResampling.pairedKernel p |>.comap actualParameter
    measurable_actualParameter

@[simp] theorem actualPairedKernel_apply
    (x : ActualSamplerCall (p := p) (rate := rate)) :
    actualPairedKernel x =
      ReferenceLaterPhysicalFibreResampling.pairedKernel p (actualParameter x) := rfl

instance actualPairedKernel_isMarkovKernel : IsMarkovKernel
    (actualPairedKernel (p := p) (rate := rate)) := by
  change IsMarkovKernel (Kernel.comap
    (ReferenceLaterPhysicalFibreResampling.pairedKernel p)
    actualParameter measurable_actualParameter)
  infer_instance

/-- The first whole K+1-vector marginal remains the original assignment law. -/
theorem actualPairedKernel_fst (x : ActualSamplerCall (p := p) (rate := rate)) :
    (actualPairedKernel x).fst = ContinuousControlSlice.assignmentLaw p.K := by
  rw [actualPairedKernel_apply, ReferenceLaterPhysicalFibreResampling.pairedKernel_apply]
  exact ReferenceLaterPhysicalFibreResampling.pairedMeasure_fst p (actualParameter x)

/-- The second whole K+1-vector marginal remains the original assignment law. -/
theorem actualPairedKernel_snd (x : ActualSamplerCall (p := p) (rate := rate)) :
    (actualPairedKernel x).snd = ContinuousControlSlice.assignmentLaw p.K := by
  rw [actualPairedKernel_apply, ReferenceLaterPhysicalFibreResampling.pairedKernel_apply]
  exact ReferenceLaterPhysicalFibreResampling.pairedMeasure_snd p (actualParameter x)

end Bandits.Support.ReferenceLaterSamplerParameterMeasurability

end
