/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCompleteObservationPrefixInformation

/-!
# Predictability of the fixed-calendar later-sampler parameters

The selector is read from the actual incoming state at its calendar date.
This module proves its literal Borelness, row independence, and adaptation to
the inspected and original-source prefix fields. It does not assert a sampler
law, physical-field equality, or manuscript closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceCalendarLaterSamplerPredictability

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- Literal administrative decoder for the optional later-sampler parameter. -/
def parameterDecoder (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (c : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  c.bind fun s => ReferenceLaterSamplerParameterMeasurability.parametersFromCanonicalDiagnostics
    (ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
      (ReferenceCollectionDispatchMeasurability.collectionCoordinates? s.1,
        row, s.2.1, t))

/-- Read the actual record's existing later-sampler parameter at calendar `t`. -/
def calendarParameters (t : Fin p.T) (z : SourceInput p) :
    Option (AssignmentParameterFibreKernel.Theta p) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
    (fun r => ReferenceLaterSamplerParameterMeasurability.parameters? r.input)

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

/-- Borelness on the original optional-state/product row/time carrier. -/
theorem parameterDecoder_measurable :
    Measurable (fun x : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) ×
      (CompletePublicTable.CompleteRow p × Fin p.T) =>
        parameterDecoder rate x.2.1 x.2.2 x.1) := by
  let Rest := CompletePublicTable.CompleteRow p × Fin p.T
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv
    (ReferenceActivePhysicalStepMeasurability.StateCode p rate) Rest
  let decode :
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate × Rest) ⊕
        (PUnit × Rest) → Option (AssignmentParameterFibreKernel.Theta p) :=
    Sum.elim
      (fun x => ReferenceLaterSamplerParameterMeasurability.parametersFromCanonicalDiagnostics
        (ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
          (ReferenceCollectionDispatchMeasurability.collectionCoordinates? x.1.1,
            x.2.1, x.1.2.1, x.2.2)))
      (fun _ => none)
  have hcoords : Measurable (fun x :
      ReferenceActivePhysicalStepMeasurability.StateCode p rate × Rest =>
      (ReferenceCollectionDispatchMeasurability.collectionCoordinates? x.1.1,
        x.2.1, x.1.2.1, x.2.2)) := by
    exact (ReferenceCollectionDispatchMeasurability.measurable_collectionCoordinates?.comp
        (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_snd)))
  have hsome : Measurable (fun x :
      ReferenceActivePhysicalStepMeasurability.StateCode p rate × Rest =>
      ReferenceLaterSamplerParameterMeasurability.parametersFromCanonicalDiagnostics
        (ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
          (ReferenceCollectionDispatchMeasurability.collectionCoordinates? x.1.1,
            x.2.1, x.1.2.1, x.2.2))) :=
    ReferenceLaterSamplerParameterMeasurability.measurable_parametersFromCanonicalDiagnostics.comp
      (ReferenceCollectionDispatchMeasurability.measurable_optionalBoundaryDiagnostics.comp
        hcoords)
  have hdecode : Measurable decode := measurable_fun_sum hsome measurable_const
  have heq : (fun x : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) × Rest =>
      parameterDecoder rate x.2.1 x.2.2 x.1) = fun x => decode (e x) := by
    funext x
    rcases x with ⟨c, row, t⟩
    cases c <;> rfl
  rw [heq]
  exact hdecode.comp e.measurable

private theorem parameterDecoder_row_independent_present
    (row row' : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (s : ReferenceActivePhysicalStepMeasurability.StateCode p rate) :
    ReferenceLaterSamplerParameterMeasurability.parametersFromCanonicalDiagnostics
      (ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
        (ReferenceCollectionDispatchMeasurability.collectionCoordinates? s.1,
          row, s.2.1, t)) =
    ReferenceLaterSamplerParameterMeasurability.parametersFromCanonicalDiagnostics
      (ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
        (ReferenceCollectionDispatchMeasurability.collectionCoordinates? s.1,
          row', s.2.1, t)) := by
  classical
  cases hc : ReferenceCollectionDispatchMeasurability.collectionCoordinates? s.1 with
  | none => rfl
  | some coordinates =>
      let boundary : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
        ReferenceCollectionDispatchMeasurability.attachBoundary coordinates (row, (s.2.1, t))
      let boundary' : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
        ReferenceCollectionDispatchMeasurability.attachBoundary coordinates (row', (s.2.1, t))
      have hvalid : ReferenceCollectionDispatchMeasurability.cutoffValid boundary ↔
          ReferenceCollectionDispatchMeasurability.cutoffValid boundary' := by
        simp [boundary, boundary', ReferenceCollectionDispatchMeasurability.attachBoundary,
          ReferenceCollectionDispatchMeasurability.cutoffValid]
      change ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary
          (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics boundary) =
        ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary
          (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics boundary')
      by_cases hv : ReferenceCollectionDispatchMeasurability.cutoffValid boundary
      · have hv' : ReferenceCollectionDispatchMeasurability.cutoffValid boundary' :=
          hvalid.mp hv
        have hrow :
            ReferenceCollectionDispatchMeasurability.assemble
                (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary', hv'⟩) =
              {ReferenceCollectionDispatchMeasurability.assemble
                (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary, hv⟩) with
                row := row'} := by
          simp [boundary, boundary', ReferenceCollectionDispatchMeasurability.attachBoundary,
            ReferenceCollectionDispatchMeasurability.boundaryLocal,
            ReferenceCollectionDispatchMeasurability.assemble]
        calc
          ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary
              (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics boundary) =
            ReferenceLaterAssignmentFibreStep.collectionParameters?
              (ReferenceCollectionDispatchMeasurability.assemble
                (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary, hv⟩)) :=
              ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary_eq_collectionParameters?
                boundary hv
          _ = ReferenceLaterAssignmentFibreStep.collectionParameters?
              (ReferenceCollectionDispatchMeasurability.assemble
                (ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨boundary', hv'⟩)) := by
              rw [hrow]
              exact (ReferenceLaterAssignmentFibreStep.collectionParameters?_row _ row').symm
          _ = ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary
              (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics boundary') :=
              (ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary_eq_collectionParameters?
                boundary' hv').symm
      · have hv' : ¬ ReferenceCollectionDispatchMeasurability.cutoffValid boundary' :=
          fun h => hv (hvalid.mpr h)
        simp [ReferenceCollectionDispatchMeasurability.boundaryDiagnostics, hv,
          ReferenceLaterSamplerParameterMeasurability.parametersFromBoundary, hv']

/-- The physical selector does not inspect the row on any encoded state. -/
theorem parameterDecoder_row_independent
    (row row' : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (c : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) :
    parameterDecoder rate row t c = parameterDecoder rate row' t c := by
  cases c with
  | none => rfl
  | some s => exact parameterDecoder_row_independent_present rate row row' t s

private theorem actualRecord_input_time (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r) :
    r.input.time = t := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  · obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hr
    have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
      rate rewards C_star C_h _ ⟨z, hk⟩
    dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
      ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
      List.get_eq_getElem] at hf
    rw [hrecord] at hf
    have ht := ReferenceCompletePhysicalHistory.completeSuffixRecords_time_values
      rate z rewards C_star C_h
    have hk' : t.val - ReferenceCompletePhysicalHistory.physicalStart
        rate z rewards C_star C_h < p.T - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h := by
      simpa only [ReferenceCompletePhysicalHistory.completeSuffixRecords_length] using hk
    have hget := congrArg (fun l : List ℕ => l[t.val -
      ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h]?) ht
    simp only [ReferenceActivePhysicalHorizon.calendar, List.getElem?_map,
      List.getElem?_range' hk', Nat.one_mul] at hget
    rw [List.getElem?_eq_getElem hk, hrecord] at hget
    apply Fin.ext
    have hv := Option.some.inj hget
    simpa only [Nat.add_sub_of_le hs] using hv

/-- The actual lookup and its existing encoded input give exactly the
administrative decoder at date `t`, for every replacement row. -/
theorem calendarParameters_eq_parameterDecoder
    (row : CompletePublicTable.CompleteRow p) (t : Fin p.T) (z : SourceInput p) :
    calendarParameters rate rewards C_star C_h t z =
      parameterDecoder rate row t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) := by
  classical
  unfold calendarParameters
  cases hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none => simp [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord, parameterDecoder]
  | some r =>
      have htime := actualRecord_input_time rate rewards C_star C_h t z r hrecord
      let code := ReferenceActivePhysicalStepMeasurability.encodeState r.input.state
      have hphysical :=
        ReferenceLaterSamplerParameterMeasurability.parameters?_eq_canonicalDiagnostics r.input
      have hcode : parameterDecoder rate r.input.row t (some code) =
          ReferenceLaterSamplerParameterMeasurability.parameters? r.input := by
        rw [ReferenceLaterSamplerParameterMeasurability.parameters?_eq_canonicalDiagnostics]
        simp [parameterDecoder, code,
          ReferenceActivePhysicalStepMeasurability.encodeState,
          ReferenceCollectionDispatchMeasurability.canonicalDiagnostics, htime]
      rw [ReferenceSourcePrefixHistoryFiltration.incoming, hrecord]
      simp only [Option.map_some, Option.bind_some]
      calc
        ReferenceLaterSamplerParameterMeasurability.parameters? r.input =
            parameterDecoder rate r.input.row t (some code) := hcode.symm
        _ = parameterDecoder rate row t (some code) :=
          parameterDecoder_row_independent rate r.input.row row t (some code)

/-- The selector factors through the strict prefix, including absent and
terminal launch cases. -/
theorem calendarParameters_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    calendarParameters rate rewards C_star C_h t z =
      calendarParameters rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
  let row : CompletePublicTable.CompleteRow p :=
    (ReferenceSourceOwnHistoryContainment.selectedForwardRow z, fun _ => control0)
  calc
    calendarParameters rate rewards C_star C_h t z =
        parameterDecoder rate row t
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) :=
      calendarParameters_eq_parameterDecoder rate rewards C_star C_h row t z
    _ = parameterDecoder rate row t
          (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) := by
      rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor]
    _ = calendarParameters rate rewards C_star C_h t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) :=
      (calendarParameters_eq_parameterDecoder rate rewards C_star C_h row t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)).symm

/-- Measurability in the exact inspected-history enlargement. -/
theorem calendarParameters_measurable_in_inspected
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[
      ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h
        t.val (Nat.le_of_lt t.isLt)]
      (calendarParameters rate rewards C_star C_h t) := by
  let I := ReferenceSourceOwnHistoryContainment.inspectedHistorySpace rate rewards C_star C_h
    t.val (Nat.le_of_lt t.isLt)
  let row : SourceInput p → CompletePublicTable.CompleteRow p :=
    fun z => (ReferenceSourceOwnHistoryContainment.selectedForwardRow z, fun _ => control0)
  have hforward : Measurable[I]
      ReferenceSourceOwnHistoryContainment.selectedForwardRow :=
    ReferenceInspectedPastRoundObservations.selectedForwardRow_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt)
  have hrow : Measurable[I] row := by
    exact hforward.prodMk measurable_const
  have hincoming : Measurable[I]
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t) :=
    ReferenceSourceOwnHistoryContainment.incoming_measurable_in_inspectedHistorySpace
      rate rewards C_star C_h t.val (Nat.le_of_lt t.isLt) t le_rfl
  have harg : Measurable[I] (fun z =>
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z,
        (row z, t))) := hincoming.prodMk (hrow.prodMk measurable_const)
  have hdec : Measurable (fun x : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) ×
      (CompletePublicTable.CompleteRow p × Fin p.T) =>
        parameterDecoder rate x.2.1 x.2.2 x.1) := parameterDecoder_measurable rate
  have heq : calendarParameters rate rewards C_star C_h t = fun z =>
      parameterDecoder rate (row z) t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) := by
    funext z
    exact calendarParameters_eq_parameterDecoder rate rewards C_star C_h (row z) t z
  rw [heq]
  exact hdec.comp harg

/-- Measurability in the pre-choice original-source successor filtration. -/
theorem calendarParameters_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (calendarParameters rate rewards C_star C_h t) := by
  apply (calendarParameters_measurable_in_inspected rate rewards C_star C_h control0 t).mono
  exact ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_sourcePrefixFiltration
    rate rewards C_star C_h control0 t.val (Nat.le_of_lt t.isLt)
  exact le_rfl

end Bandits.Support.ReferenceCalendarLaterSamplerPredictability

end
