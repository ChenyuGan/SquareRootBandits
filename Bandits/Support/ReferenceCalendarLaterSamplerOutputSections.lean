/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCalendarLaterSamplerPredictability

/-!
# Full later-sampler output sections on the original source

The observations below retain the actual diagnostics, every failure tag and
the whole continuous assignment vector. The section is taken in the original
source prefix field. These are internal laws, not a physical/logical coupling
or a claim of manuscript closure.

Sources: `06_interruptions.tex:41-69,246-299,376-426`,
`05_binary_transport.tex:354-431`, `07_public_setup.tex:127-164`, and
`appendix_b_communication.tex:25-58` in the pinned ZIP4 manuscript.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceCalendarLaterSamplerOutputSections

variable {p : ConstructorDimensions.Parameters}

local instance clockObservationMeasurableSpace :
    MeasurableSpace (ReferenceCollectionDispatchMeasurability.ClockObservation p) := ⊤

local instance optionNatMeasurableSpace : MeasurableSpace (Option ℕ) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

/-- The existing full later output, with noncollection and invalid boundaries
remaining absent. -/
def outputOnInput {rate : ReferenceActivePhysicalStep.RateInput p}
    (x : ReferenceActivePhysicalStep.RoundInput p rate) :
    Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) :=
  (ReferenceCollectionDispatchMeasurability.canonicalDiagnostics x).bind fun bd =>
    match bd with
    | .inl _ => none
    | .inr d => d.2.2.2.2

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- Read the later operation on the actual calendar record. -/
def outputAt (t : Fin p.T) (z : SourceInput p) :
    Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).bind
    fun r => outputOnInput r.input

/-- Preserve absence of the actual record separately from every original
canonical diagnostic tag. -/
def diagnosticsAt (t : Fin p.T) (z : SourceInput p) :
    Option (Option (Unit ⊕ ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p)) :=
  (ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z).map
    fun r => ReferenceCollectionDispatchMeasurability.canonicalDiagnostics r.input

/-- The original full-vector integral with the accepted insertion into the
actual input. No sampler parameter or successful branch is assumed. -/
def vectorSection (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p)) (z : SourceInput p) : ℝ :=
  match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => ∫ v, B.indicator (fun _ => (1 : ℝ)) (none, v)
      ∂ContinuousControlSlice.assignmentLaw p.K
  | some r => ∫ v, B.indicator (fun _ => (1 : ℝ))
      (outputOnInput (ReferenceLaterAssignmentFibreStep.withAssignment r.input v), v)
      ∂ContinuousControlSlice.assignmentLaw p.K

/-- All literal source fields of a present actual record, at its calendar time. -/
theorem actualRecord_fields (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z =
      some r) :
    r.input.rows = z.1.2 ∧
      r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p z ∧
      r.input.time = t ∧ r.input.rewards = rewards := by
  unfold ReferenceSourcePrefixHistoryFiltration.actualRecord at hr
  split_ifs at hr with hs
  obtain ⟨hk, hrecord⟩ := List.getElem?_eq_some_iff.mp hr
  have hf := ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt_fields
    rate rewards C_star C_h _ ⟨z, hk⟩
  dsimp only [ReferenceCompleteSuffixInputMeasurability.actualRoundInputAt,
    ReferenceCompleteSuffixInputMeasurability.actualRecordCodeAt,
    List.get_eq_getElem] at hf
  rw [hrecord] at hf
  refine ⟨hf.1, hf.2.1, ?_, hf.2.2.1⟩
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
  simpa only [Nat.add_sub_of_le hs] using Option.some.inj hget

private theorem measurable_optionBind {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (input : X → Option Y) (hinput : Measurable input)
    (f : Y → Option Z) (hf : Measurable f) :
    Measurable (fun x => (input x).bind f) := by
  let e : Option Y ≃ᵐ Y ⊕ PUnit := {
    toEquiv := Equiv.optionEquivSumPUnit Y
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      exact measurable_id }
  have heq : (fun x => (input x).bind f) =
      fun x => Sum.elim f (fun _ : PUnit => none) (e (input x)) := by
    funext x
    cases input x <;> rfl
  rw [heq]
  have hlift : Measurable (Sum.elim f (fun _ : PUnit => (none : Option Z))) :=
    measurable_fun_sum hf measurable_const
  exact hlift.comp (e.measurable.comp hinput)

private theorem measurable_outputProjection : Measurable
    (fun bd : Unit ⊕ ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p =>
      match bd with
      | .inl _ => (none : Option
          (LaterAssignmentFullOutputMeasurability.FullOutputObservation p))
      | .inr d => d.2.2.2.2) :=
  measurable_fun_sum measurable_const
    (measurable_snd.comp (measurable_snd.comp
      (measurable_snd.comp (measurable_snd.comp measurable_id))))

theorem measurable_outputOnInput :
    Measurable (outputOnInput (p := p) (rate := rate)) :=
  measurable_optionBind _
    ReferenceCollectionDispatchMeasurability.measurable_canonicalDiagnostics _
    measurable_outputProjection

/-- Exact equality with the already accepted actual parameter selector. -/
theorem outputAt_parameters (t : Fin p.T) (z : SourceInput p) :
    (outputAt rate rewards C_star C_h t z).bind (fun o => o.2.1) =
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z := by
  unfold outputAt ReferenceCalendarLaterSamplerPredictability.calendarParameters
  cases ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none => rfl
  | some r =>
      simp only [Option.bind_some]
      rw [ReferenceLaterSamplerParameterMeasurability.parameters?_eq_canonicalDiagnostics]
      unfold outputOnInput
      cases ReferenceCollectionDispatchMeasurability.canonicalDiagnostics r.input with
      | none => rfl
      | some d => cases d <;> rfl

private theorem fullOutput_eq_of_vector
    (input : LaterAssignmentFullOutputMeasurability.JointLocalStartInput p rate.eta)
    (row row' : CompletePublicTable.CompleteRow p)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector row input.2.2.1.time =
      LaterAssignmentStartOperation.ownAssignmentVector row' input.2.2.1.time) :
    LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation (input, row) =
      LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
        (input, row') := by
  have hcode :=
    LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_of_ownAssignmentVector_eq
      input.1 input.2 row row' hv
  have hscore :=
    LaterAssignmentStartMeasurability.laterAssignmentStart_payloadAndBaseScore?_eq_of_ownAssignmentVector_eq
      input.1 input.2 row row' hv
  unfold LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
    LaterAssignmentAnchorMeasurability.laterAssignmentStartCodeMap
    LaterAssignmentAnchorMeasurability.operationCodeForInput
    LaterAssignmentFullOutputMeasurability.actualPayloadScoreObservation?
    LaterAssignmentFullOutputMeasurability.actualDerivedFields?
    LaterAssignmentFullOutputMeasurability.actualPayloadScore?
    LaterAssignmentFullOutputMeasurability.actualResult
    LaterAssignmentFullOutputMeasurability.originalAssignmentVector
  dsimp only
  rw [hcode, hscore, hv]

private theorem requestedInstruction_time
    (z : ReferenceCollectionDispatchMeasurability.LocalInput p rate)
    (core : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceCollectionDispatchMeasurability.assemble z))
    (instruction : CoordinatorPhaseClock.AssignmentStartInstruction p)
    (hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction z =
      some instruction) : instruction.time = z.2.2.2.2.1 := by
  by_cases hpending : z.2.1.pending.Nonempty
  · simp [ReferenceCollectionDispatchMeasurability.requestedInstruction,
      ReferenceCollectionDispatchMeasurability.requestedInstructionAt, hpending] at hrequest
  · cases hstart : CoordinatorPhaseClock.startRound p rate.eta.val
        (ReferenceCollectionDispatchMeasurability.assemble z).time
        (ReferenceCollectionDispatchMeasurability.assemble z).clock
        (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending with
    | error reason =>
        simp [ReferenceCollectionDispatchMeasurability.requestedInstruction,
          ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
          ReferenceCollectionDispatchMeasurability.clockObservation, hpending, hstart] at hrequest
    | ok started =>
        have hi : started.assignmentStart = some instruction := by
          simpa only [ReferenceCollectionDispatchMeasurability.requestedInstruction,
            ReferenceCollectionDispatchMeasurability.requestedInstructionAt,
            ite_eq_right hpending, ReferenceCollectionDispatchMeasurability.clockObservation,
            hstart] using hrequest
        exact (CoordinatorPhaseClock.startRound_assignment_effect p rate.eta.val
          (ReferenceCollectionDispatchMeasurability.assemble z).time
          (ReferenceCollectionDispatchMeasurability.assemble z).clock
          (ReferenceCollectionDispatchMeasurability.assemble z).ledger.pending
          started instruction core.clock_parameter_valid core.clock_registers_valid
          core.clock_start_time_valid hstart hi).1

private theorem prechoiceDiagnostics_row
    (z : ReferenceCollectionDispatchMeasurability.LocalInput p rate)
    (row : CompletePublicTable.CompleteRow p)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector z.1.2 z.2.2.2.2.1 =
      LaterAssignmentStartOperation.ownAssignmentVector row z.2.2.2.2.1) :
    ReferenceCollectionDispatchMeasurability.prechoiceDiagnostics z =
      ReferenceCollectionDispatchMeasurability.prechoiceDiagnostics ((z.1.1, row), z.2) := by
  let z' : ReferenceCollectionDispatchMeasurability.LocalInput p rate := ((z.1.1, row), z.2)
  have hcore : CoordinatorRoundDispatch.CollectionCoreValid
      (ReferenceCollectionDispatchMeasurability.assemble z) ↔
      CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceCollectionDispatchMeasurability.assemble z') :=
    (ReferenceCollectionDispatchMeasurability.coreChecks_iff z).symm.trans
      (ReferenceCollectionDispatchMeasurability.coreChecks_iff z')
  have houtput : ReferenceCollectionDispatchMeasurability.laterObservation? z =
      ReferenceCollectionDispatchMeasurability.laterObservation? z' := by
    unfold ReferenceCollectionDispatchMeasurability.laterObservation?
      ReferenceCollectionDispatchMeasurability.laterObservationAtClock
    by_cases hc : CoordinatorRoundDispatch.CollectionCoreValid
        (ReferenceCollectionDispatchMeasurability.assemble z)
    · rw [dite_eq_left hc, dite_eq_left (hcore.mp hc)]
      change ReferenceCollectionDispatchMeasurability.laterObservationForInstruction
          ⟨z, hc⟩ (ReferenceCollectionDispatchMeasurability.requestedInstruction z) =
        ReferenceCollectionDispatchMeasurability.laterObservationForInstruction
          ⟨z', hcore.mp hc⟩ (ReferenceCollectionDispatchMeasurability.requestedInstruction z)
      cases hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction z with
      | none => rfl
      | some instruction =>
          have ht := requestedInstruction_time rate z hc instruction hrequest
          apply congrArg some
          change LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
              (ReferenceCollectionDispatchMeasurability.laterInput ⟨z, hc⟩ instruction, z.1.2) =
            LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
              (ReferenceCollectionDispatchMeasurability.laterInput ⟨z, hc⟩ instruction, row)
          exact fullOutput_eq_of_vector rate _ _ _ (ht ▸ hv)
    · rw [dite_eq_right hc, dite_eq_right (fun h => hc (hcore.mpr h))]
  have hcheck : ReferenceCollectionDispatchMeasurability.coreCheck z =
      ReferenceCollectionDispatchMeasurability.coreCheck z' := by
    simp only [ReferenceCollectionDispatchMeasurability.coreCheck, hcore]
  change (_, _, _, _, ReferenceCollectionDispatchMeasurability.laterObservation? z) =
    (_, _, _, _, ReferenceCollectionDispatchMeasurability.laterObservation? z')
  rw [houtput, hcheck]
  rfl

/-- The full canonical diagnostic reads state, time, and the full current
assignment vector only. The actual clock supplies the instruction time. -/
theorem canonicalDiagnostics_eq_of_reads
    {rate : ReferenceActivePhysicalStep.RateInput p}
    (x y : ReferenceActivePhysicalStep.RoundInput p rate)
    (hs : x.state = y.state) (ht : x.time = y.time)
    (hv : LaterAssignmentStartOperation.ownAssignmentVector x.row x.time =
      LaterAssignmentStartOperation.ownAssignmentVector y.row y.time) :
    ReferenceCollectionDispatchMeasurability.canonicalDiagnostics x =
      ReferenceCollectionDispatchMeasurability.canonicalDiagnostics y := by
  unfold ReferenceCollectionDispatchMeasurability.canonicalDiagnostics
  rw [← hs, ← ht]
  rw [← ht] at hv
  cases hc : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator) with
  | none => rfl
  | some c =>
      change some (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics
          (ReferenceCollectionDispatchMeasurability.attachBoundary c
            (x.row, x.state.upDecoderBank, x.time))) =
        some (ReferenceCollectionDispatchMeasurability.boundaryDiagnostics
          (ReferenceCollectionDispatchMeasurability.attachBoundary c
            (y.row, x.state.upDecoderBank, x.time)))
      apply congrArg some
      unfold ReferenceCollectionDispatchMeasurability.boundaryDiagnostics
      by_cases hcutoff : ReferenceCollectionDispatchMeasurability.cutoffValid
          (ReferenceCollectionDispatchMeasurability.attachBoundary c
            (x.row, x.state.upDecoderBank, x.time))
      · have hcutoff' : ReferenceCollectionDispatchMeasurability.cutoffValid
            (ReferenceCollectionDispatchMeasurability.attachBoundary c
              (y.row, x.state.upDecoderBank, x.time)) := hcutoff
        rw [dite_eq_left hcutoff, dite_eq_left hcutoff']
        apply congrArg Sum.inr
        exact prechoiceDiagnostics_row rate _ y.row hv
      · have hcutoff' : ¬ ReferenceCollectionDispatchMeasurability.cutoffValid
            (ReferenceCollectionDispatchMeasurability.attachBoundary c
              (y.row, x.state.upDecoderBank, x.time)) := hcutoff
        rw [dite_eq_right hcutoff, dite_eq_right hcutoff']

private def diagnosticsDecoder (row : CompletePublicTable.CompleteRow p) (t : Fin p.T)
    (c : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate)) :
    Option (Option (Unit ⊕ ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p)) :=
  c.map fun s => ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
    (ReferenceCollectionDispatchMeasurability.collectionCoordinates? s.1, row, s.2.1, t)

private theorem measurable_diagnosticsDecoder : Measurable
    (fun x : Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate) ×
      (CompletePublicTable.CompleteRow p × Fin p.T) =>
      diagnosticsDecoder rate x.2.1 x.2.2 x.1) := by
  let Rest := CompletePublicTable.CompleteRow p × Fin p.T
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv
    (ReferenceActivePhysicalStepMeasurability.StateCode p rate) Rest
  let decode : (ReferenceActivePhysicalStepMeasurability.StateCode p rate × Rest) ⊕
      (PUnit × Rest) → Option
        (Option (Unit ⊕ ReferenceCollectionDispatchMeasurability.PrechoiceDiagnostics p)) :=
    Sum.elim (fun x => some
      (ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics
        (ReferenceCollectionDispatchMeasurability.collectionCoordinates? x.1.1,
          x.2.1, x.1.2.1, x.2.2))) (fun _ => none)
  have hcoords : Measurable (fun x :
      ReferenceActivePhysicalStepMeasurability.StateCode p rate × Rest =>
      (ReferenceCollectionDispatchMeasurability.collectionCoordinates? x.1.1,
        x.2.1, x.1.2.1, x.2.2)) :=
    (ReferenceCollectionDispatchMeasurability.measurable_collectionCoordinates?.comp
      (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_fst.comp measurable_snd).prodMk
        ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_snd)))
  have hdecode : Measurable decode := measurable_fun_sum
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (ReferenceCollectionDispatchMeasurability.measurable_optionalBoundaryDiagnostics.comp
        hcoords)) measurable_const
  have heq : (fun x : Option
      (ReferenceActivePhysicalStepMeasurability.StateCode p rate) × Rest =>
      diagnosticsDecoder rate x.2.1 x.2.2 x.1) = fun x => decode (e x) := by
    funext x
    rcases x with ⟨c, row, t⟩
    cases c <;> rfl
  rw [heq]
  exact hdecode.comp e.measurable

private theorem diagnosticsAt_eq_decoder (t : Fin p.T) (z : SourceInput p) :
    diagnosticsAt rate rewards C_star C_h t z =
      diagnosticsDecoder rate (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z) := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp only [diagnosticsAt, ReferenceSourcePrefixHistoryFiltration.incoming,
        hr, Option.map_none, diagnosticsDecoder]
  | some r =>
      have hf := actualRecord_fields rate rewards C_star C_h t z r hr
      have hrow : r.input.row =
          z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z) := by
        change r.input.rows r.input.selected = _
        rw [hf.1, hf.2.1]
      simp only [diagnosticsAt, ReferenceSourcePrefixHistoryFiltration.incoming,
        hr, Option.map_some, diagnosticsDecoder,
        ReferenceActivePhysicalStepMeasurability.encodeState,
        ReferenceCollectionDispatchMeasurability.canonicalDiagnostics, hf.2.2.1, hrow]

private theorem measurable_sourceRow : Measurable (fun z : SourceInput p =>
    z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) := by
  have hselected : Measurable (ActualInitializationPhysicalStep.selectedRowIndex p) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have heval : Measurable (fun x :
      (Fin (M p) → CompletePublicTable.CompleteRow p) × Fin (M p) => x.1 x.2) :=
    measurable_from_prod_countable_left fun q => measurable_pi_apply q
  exact heval.comp ((measurable_snd.comp measurable_fst).prodMk hselected)

private theorem measurable_diagnosticsDecoder_comp {X : Type*} [MeasurableSpace X]
    (input : X → Option (ReferenceActivePhysicalStepMeasurability.StateCode p rate))
    (row : X → CompletePublicTable.CompleteRow p) (time : X → Fin p.T)
    (hi : Measurable input) (hr : Measurable row) (ht : Measurable time) :
    Measurable (fun x => diagnosticsDecoder rate (row x) (time x) (input x)) := by
  have hpair : Measurable (fun x : X => (input x, (row x, time x))) :=
    hi.prodMk (hr.prodMk ht)
  intro s hs
  exact hpair ((measurable_diagnosticsDecoder rate) hs)

/-- Borelness of the complete nested diagnostic on the original source space. -/
theorem measurable_diagnosticsAt (t : Fin p.T) :
    Measurable (diagnosticsAt rate rewards C_star C_h t) := by
  have hdec : Measurable (fun z : SourceInput p =>
      diagnosticsDecoder rate (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)) :=
    measurable_diagnosticsDecoder_comp rate
      (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t)
      (fun z => z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) (fun _ => t)
      (ReferenceSourcePrefixHistoryFiltration.measurable_incoming rate rewards C_star C_h t)
      measurable_sourceRow measurable_const
  have heq : (fun z : SourceInput p =>
      diagnosticsDecoder rate (z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)) t
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z)) =
      diagnosticsAt rate rewards C_star C_h t :=
    funext fun z => (diagnosticsAt_eq_decoder rate rewards C_star C_h t z).symm
  exact heq ▸ hdec

private theorem outputAt_eq_diagnostics (t : Fin p.T) (z : SourceInput p) :
    outputAt rate rewards C_star C_h t z =
      (diagnosticsAt rate rewards C_star C_h t z).bind (fun d => d.bind fun bd =>
        match bd with
        | .inl _ => none
        | .inr d => d.2.2.2.2) := by
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z <;>
    simp only [outputAt, diagnosticsAt, hr, Option.map_none, Option.map_some,
      Option.bind_none, Option.bind_some, outputOnInput]

/-- Borelness of the actual full optional output, including failed operations. -/
theorem measurable_outputAt (t : Fin p.T) :
    Measurable (outputAt rate rewards C_star C_h t) := by
  rw [show outputAt rate rewards C_star C_h t = fun z =>
    (diagnosticsAt rate rewards C_star C_h t z).bind (fun d => d.bind fun bd =>
      match bd with
      | .inl _ => none
      | .inr d => d.2.2.2.2) from
    funext (outputAt_eq_diagnostics rate rewards C_star C_h t)]
  exact measurable_optionBind _ (measurable_diagnosticsAt rate rewards C_star C_h t) _
    (measurable_optionBind id measurable_id _ measurable_outputProjection)

private theorem actualRecord_vector (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    LaterAssignmentStartOperation.ownAssignmentVector r.input.row r.input.time =
      ContinuousControlSlice.assignmentVector
        (ReferenceSourceCurrentControlFreshness.u_t p t z).1 := by
  have hf := actualRecord_fields rate rewards C_star C_h t z r hr
  change ContinuousControlSlice.assignmentVector
      ((r.input.rows r.input.selected).2 r.input.time).1 = _
  rw [hf.1, hf.2.1, hf.2.2.1]
  rfl

private theorem diagnosticsAt_eq_of_reads (t : Fin p.T) (z z' : SourceInput p)
    (hi : ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z')
    (hv : ContinuousControlSlice.assignmentVector
        (ReferenceSourceCurrentControlFreshness.u_t p t z).1 =
      ContinuousControlSlice.assignmentVector
        (ReferenceSourceCurrentControlFreshness.u_t p t z').1) :
    diagnosticsAt rate rewards C_star C_h t z =
      diagnosticsAt rate rewards C_star C_h t z' := by
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hi
  unfold diagnosticsAt
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z <;>
    cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z' <;>
    simp only [hr, hr', Option.map_none, Option.map_some] at hi ⊢
  · cases hi
  · cases hi
  · rename_i r r'
    apply congrArg some
    exact canonicalDiagnostics_eq_of_reads r.input r'.input
      (ReferenceActivePhysicalStepMeasurability.encodeState_injective (Option.some.inj hi))
      ((actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1.trans
        (actualRecord_fields rate rewards C_star C_h t z' r' hr').2.2.1.symm)
      ((actualRecord_vector rate rewards C_star C_h t z r hr).trans
        (hv.trans (actualRecord_vector rate rewards C_star C_h t z' r' hr').symm))

/-- Successor prefix factorization retains the whole current assignment vector. -/
theorem diagnosticsAt_successor_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    diagnosticsAt rate rewards C_star C_h t z =
      diagnosticsAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  apply diagnosticsAt_eq_of_reads rate rewards C_star C_h t
  · rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t z,
      ReferenceSourcePrefixHistoryFiltration.incoming_factor
        rate rewards C_star C_h control0 t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z),
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
        control0 t.val (t.val + 1) (Nat.le_succ _) z]
  · unfold ReferenceSourceCurrentControlFreshness.u_t
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefix_selected,
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix_control,
      ite_eq_left (Nat.lt_succ_self t.val)]

/-- The full later output factors through the same successor prefix. -/
theorem outputAt_successor_factor (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    outputAt rate rewards C_star C_h t z =
      outputAt rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) z) := by
  rw [outputAt_eq_diagnostics, outputAt_eq_diagnostics,
    diagnosticsAt_successor_factor rate rewards C_star C_h control0 t z]

private theorem fullOutput_code_of_parameters
    (input : LaterAssignmentFullOutputMeasurability.JointLocalStartInput p rate.eta)
    (row : CompletePublicTable.CompleteRow p) (theta : AssignmentParameterFibreKernel.Theta p)
    (hp : (LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
      (input, row)).2.1 = some theta) :
    (LaterAssignmentFullOutputMeasurability.laterAssignmentFullOutputObservation
      (input, row)).1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
        (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
          (LaterAssignmentStartOperation.ownAssignmentVector row input.2.2.1.time)) := by
  rcases input with ⟨old, ledger, instruction, consistent⟩
  rw [LaterAssignmentFullOutputMeasurability.fullOutput_code]
  change LaterAssignmentStartMeasurability.laterAssignmentStartCode
    old ledger instruction row consistent = _
  rw [LaterAssignmentStartMeasurability.laterAssignmentStartCode_eq_reconstructedFirstCode
    old ⟨ledger, instruction, consistent⟩ row]
  rw [LaterAssignmentFullOutputMeasurability.fullOutput_selectedParameters] at hp
  change LaterAssignmentStartMeasurability.selectedSamplerParameters?
    old ⟨ledger, instruction, consistent⟩ = some theta at hp
  rw [LaterAssignmentJointCodeMeasurability.selectedSamplerParameters?_eq_match] at hp
  cases hd : LaterAssignmentStartOperation.decideReconstruction old ledger instruction with
  | failure reason =>
      simp only [hd, reduceCtorEq] at hp
  | success out hcall =>
      have htheta : LaterAssignmentStartMeasurability.selectedSamplerParameters
          old ledger instruction out hcall = theta := by
        exact Option.some.inj (by
          simpa only [hd] using hp)
      simp only [LaterAssignmentStartMeasurability.reconstructedFirstCode, hd, htheta]

private theorem outputOnInput_code_vector
    (x : ReferenceActivePhysicalStep.RoundInput p rate)
    (o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (ho : outputOnInput x = some o) (hp : o.2.1 = some theta) :
    o.2.2.2.1 = LaterAssignmentStartOperation.ownAssignmentVector x.row x.time ∧
      o.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
        (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
          (LaterAssignmentStartOperation.ownAssignmentVector x.row x.time)) := by
  unfold outputOnInput ReferenceCollectionDispatchMeasurability.canonicalDiagnostics at ho
  cases hc : ReferenceCollectionDispatchMeasurability.collectionCoordinates?
      (ReferenceActivePhysicalStepMeasurability.encodeCoordinator x.state.coordinator) with
  | none =>
      simp only [hc, ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics,
        Option.bind_none] at ho
      cases ho
  | some c =>
      simp only [hc, ReferenceCollectionDispatchMeasurability.optionalBoundaryDiagnostics,
        Option.bind_some] at ho
      let bd : ReferenceCollectionDispatchMeasurability.BoundaryInput p rate :=
        ReferenceCollectionDispatchMeasurability.attachBoundary c
          (x.row, x.state.upDecoderBank, x.time)
      change (match ReferenceCollectionDispatchMeasurability.boundaryDiagnostics bd with
        | .inl _ => none
        | .inr d => d.2.2.2.2) = some o at ho
      unfold ReferenceCollectionDispatchMeasurability.boundaryDiagnostics at ho
      split_ifs at ho with hcutoff
      let localInput := ReferenceCollectionDispatchMeasurability.boundaryLocal ⟨bd, hcutoff⟩
      change ReferenceCollectionDispatchMeasurability.laterObservation? localInput = some o at ho
      unfold ReferenceCollectionDispatchMeasurability.laterObservation?
        ReferenceCollectionDispatchMeasurability.laterObservationAtClock at ho
      split_ifs at ho with hcore
      change ReferenceCollectionDispatchMeasurability.laterObservationForInstruction
        ⟨localInput, hcore⟩
        (ReferenceCollectionDispatchMeasurability.requestedInstruction localInput) = some o at ho
      cases hrequest : ReferenceCollectionDispatchMeasurability.requestedInstruction localInput with
      | none =>
          simp only [hrequest,
            ReferenceCollectionDispatchMeasurability.laterObservationForInstruction] at ho
          cases ho
      | some instruction =>
          have hout : ReferenceCollectionDispatchMeasurability.laterObservation
              ⟨localInput, hcore⟩ instruction = o := by
            exact Option.some.inj (by
              simpa only [hrequest,
                ReferenceCollectionDispatchMeasurability.laterObservationForInstruction] using ho)
          have ht : instruction.time = x.time :=
            requestedInstruction_time rate localInput hcore instruction hrequest
          subst o
          constructor
          · rw [ReferenceCollectionDispatchMeasurability.laterObservation,
              LaterAssignmentFullOutputMeasurability.fullOutput_originalAssignmentVector]
            change LaterAssignmentStartOperation.ownAssignmentVector x.row instruction.time = _
            rw [ht]
          · have hcode := fullOutput_code_of_parameters rate
              (ReferenceCollectionDispatchMeasurability.laterInput ⟨localInput, hcore⟩ instruction)
              localInput.1.2 theta hp
            change _ = LaterAssignmentStartMeasurability.codeOfCheckedSample p
              (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
                (LaterAssignmentStartOperation.ownAssignmentVector x.row instruction.time)) at hcode
            rw [ht] at hcode
            exact hcode

/-- A present selected parameter determines the exact checked operation code
and the original full current assignment vector, even on sampling failure. -/
theorem outputAt_code_vector (t : Fin p.T) (z : SourceInput p)
    (o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (ho : outputAt rate rewards C_star C_h t z = some o) (hp : o.2.1 = some theta) :
    o.2.2.2.1 = ContinuousControlSlice.assignmentVector
        (ReferenceSourceCurrentControlFreshness.u_t p t z).1 ∧
      o.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
        (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
          (ContinuousControlSlice.assignmentVector
            (ReferenceSourceCurrentControlFreshness.u_t p t z).1)) := by
  unfold outputAt at ho
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      simp only [hr, Option.bind_none] at ho
      cases ho
  | some r =>
      have houtput : outputOnInput r.input = some o := by
        simpa only [hr, Option.bind_some] using ho
      obtain ⟨hv, hcode⟩ := outputOnInput_code_vector rate r.input o theta houtput hp
      rw [actualRecord_vector rate rewards C_star C_h t z r hr] at hv hcode
      exact ⟨hv, hcode⟩

private theorem sourcePrefix_replace (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hvt : v ≠ t := by intro h; subst v; exact (Nat.lt_irrefl _) hv
        simp only [hv, ite_true, Function.update_of_ne hvt]
      · simp only [hv, ite_false]
    · have hq' : q ≠ ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p z := hq
      simp only [ReferenceSourcePrefixHistoryFiltration.sourcePrefix,
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
        ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex] at hq hq' ⊢
      rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
  · rfl

private theorem incoming_replace (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c) =
      ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z := by
  rw [ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c),
    sourcePrefix_replace,
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0 t.val t.val le_rfl,
    ← ReferenceSourcePrefixHistoryFiltration.incoming_factor
      rate rewards C_star C_h control0 t z]

private theorem replaced_control (t : Fin p.T) (z : SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceSourceCurrentControlFreshness.u_t p t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) = c := by
  simp only [ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]

private theorem outputAt_replace (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    outputAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c) =
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
      | none => none
      | some r => outputOnInput (ReferenceLaterAssignmentFibreStep.withAssignment r.input
          (ContinuousControlSlice.assignmentVector c.1)) := by
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
    (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c
  have hi := incoming_replace rate rewards C_star C_h control0 t z c
  change ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' =
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z at hi
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hi
  change outputAt rate rewards C_star C_h t z' = _
  unfold outputAt
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z' with
      | none => rfl
      | some r' =>
          simp only [hr, hr', Option.map_none, Option.map_some] at hi
          cases hi
  | some r =>
      cases hr' : ReferenceSourcePrefixHistoryFiltration.actualRecord
          rate rewards C_star C_h t z' with
      | none =>
          simp only [hr, hr', Option.map_none, Option.map_some] at hi
          cases hi
      | some r' =>
          simp only [hr, hr', Option.map_some] at hi
          simp only [Option.bind_some]
          have hs : r'.input.state = r.input.state :=
            ReferenceActivePhysicalStepMeasurability.encodeState_injective (Option.some.inj hi)
          have ht : r'.input.time = r.input.time :=
            (actualRecord_fields rate rewards C_star C_h t z' r' hr').2.2.1.trans
              (actualRecord_fields rate rewards C_star C_h t z r hr).2.2.1.symm
          have hv := actualRecord_vector rate rewards C_star C_h t z' r' hr'
          change _ = ContinuousControlSlice.assignmentVector
            (ReferenceSourceCurrentControlFreshness.u_t p t
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c)).1 at hv
          rw [replaced_control] at hv
          have hinsert : LaterAssignmentStartOperation.ownAssignmentVector
              (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                (ContinuousControlSlice.assignmentVector c.1)).row
              (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                (ContinuousControlSlice.assignmentVector c.1)).time =
              ContinuousControlSlice.assignmentVector c.1 := by
            rw [ReferenceLaterAssignmentFibreStep.withAssignment_row]
            exact ReferenceLaterAssignmentFibreStep.ownAssignmentVector_rowWithAssignment _ _
          unfold outputOnInput
          rw [canonicalDiagnostics_eq_of_reads r'.input
            (ReferenceLaterAssignmentFibreStep.withAssignment r.input
              (ContinuousControlSlice.assignmentVector c.1)) hs ht (hv.trans hinsert.symm)]

private theorem assignment_integral (f : CheckedAssignmentSample.AssignmentVector p → ℝ) :
    (∫ c, f (ContinuousControlSlice.assignmentVector c.1)
      ∂ContinuousLearningRows.timeControlLaw p) =
      ∫ v, f v ∂ContinuousControlSlice.assignmentLaw p.K := by
  have hs := (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).integral_comp'
    (fun x => f x.1)
  change (∫ c, f (ContinuousControlSlice.assignmentVector c.1)
    ∂ContinuousLearningRows.timeControlLaw p) = _ at hs
  rw [hs, integral_fun_fst]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

private theorem controlSection_eq_vectorSection
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p)) (z : SourceInput p) :
    (∫ c, B.indicator (fun _ => (1 : ℝ))
      (outputAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c),
        ContinuousControlSlice.assignmentVector c.1)
      ∂ContinuousLearningRows.timeControlLaw p) = vectorSection rate rewards C_star C_h t B z := by
  simp_rw [outputAt_replace rate rewards C_star C_h control0 t z]
  unfold vectorSection
  cases ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
  | none =>
      exact assignment_integral (p := p)
        (fun v => B.indicator (fun _ => (1 : ℝ)) (none, v))
  | some r =>
      exact assignment_integral (p := p)
        (fun v => B.indicator (fun _ => (1 : ℝ))
          (outputOnInput (ReferenceLaterAssignmentFibreStep.withAssignment r.input v), v))

private def sectionMap (t : Fin p.T)
    (x : SourceInput p × ContinuousLearningRows.TimeControl p) :
    Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p :=
  (outputAt rate rewards C_star C_h t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2),
    ContinuousControlSlice.assignmentVector x.2.1)

private theorem measurable_sectionMap (t : Fin p.T) :
    Measurable (sectionMap rate rewards C_star C_h t) := by
  have ho : Measurable (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      outputAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) := by
    intro s hs
    exact (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t)
      ((measurable_outputAt rate rewards C_star C_h t) hs)
  exact ho.prodMk ((ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
    (measurable_fst.comp measurable_snd))

private theorem sectionMap_restore (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    sectionMap rate rewards C_star C_h t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z) =
      (outputAt rate rewards C_star C_h t z,
        ContinuousControlSlice.assignmentVector
          (ReferenceSourceCurrentControlFreshness.u_t p t z).1) := by
  apply Prod.ext
  · change outputAt rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z)
        (ReferenceSourceCurrentControlFreshness.u_t p t z)) = _
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    change outputAt rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
        ((z.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p z)).2 t)) = _
    rw [← ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore]
    exact (outputAt_successor_factor rate rewards C_star C_h control0 t z).symm
  · rfl

private theorem indicator_sectionMap
    (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p))
    (x : SourceInput p × ContinuousLearningRows.TimeControl p) :
    ((sectionMap rate rewards C_star C_h t) ⁻¹' B).indicator (fun _ => (1 : ℝ)) x =
      B.indicator (fun _ => (1 : ℝ)) (sectionMap rate rewards C_star C_h t x) := by
  by_cases h : sectionMap rate rewards C_star C_h t x ∈ B <;>
    simp only [Set.indicator, Set.mem_preimage, h, ite_true, ite_false]

/-- The literal Borel full-output/vector test has the actual vector section
as its conditional expectation in the original-source pre-choice field. -/
theorem outputAt_vectorSection_condExp
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p)) (hB : MeasurableSet B) :
    (sourceInputLaw p)[(fun z => B.indicator (fun _ => (1 : ℝ))
      (outputAt rate rewards C_star C_h t z,
        ContinuousControlSlice.assignmentVector
          (ReferenceSourceCurrentControlFreshness.u_t p t z).1)) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      =ᵐ[sourceInputLaw p] vectorSection rate rewards C_star C_h t B := by
  let E := (sectionMap rate rewards C_star C_h t) ⁻¹' B
  have hE : MeasurableSet E := hB.preimage (measurable_sectionMap rate rewards C_star C_h t)
  have htest : ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t E =
      fun z => B.indicator (fun _ => (1 : ℝ))
        (outputAt rate rewards C_star C_h t z,
          ContinuousControlSlice.assignmentVector
            (ReferenceSourceCurrentControlFreshness.u_t p t z).1) := by
    funext z
    change E.indicator (fun _ => (1 : ℝ))
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z,
        ReferenceSourceCurrentControlFreshness.u_t p t z) = _
    rw [indicator_sectionMap, sectionMap_restore]
  have hsection (z : SourceInput p) :
      (∫ c, E.indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, c)
        ∂ContinuousLearningRows.timeControlLaw p) = vectorSection rate rewards C_star C_h t B z := by
    dsimp only [E]
    simp_rw [indicator_sectionMap]
    exact controlSection_eq_vectorSection rate rewards C_star C_h control0 t B z
  have hce := ReferenceSourceCurrentControlFreshness.source_control_test_condExp control0 t E hE
  rw [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t]
  rw [htest] at hce
  filter_upwards [hce] with z hz
  exact hz.trans (hsection z)

/-- Strong adaptation follows by integrating the visible whole-control test
and composing with the original source prefix. -/
theorem vectorSection_stronglyMeasurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p)) (hB : MeasurableSet B) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (vectorSection rate rewards C_star C_h t B) := by
  have hf : Measurable (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      B.indicator (fun _ => (1 : ℝ)) (sectionMap rate rewards C_star C_h t x)) :=
    (measurable_const.indicator hB).comp (measurable_sectionMap rate rewards C_star C_h t)
  have hbase : StronglyMeasurable (fun s : SourceInput p =>
      ∫ c, B.indicator (fun _ => (1 : ℝ)) (sectionMap rate rewards C_star C_h t (s, c))
        ∂ContinuousLearningRows.timeControlLaw p) :=
    hf.stronglyMeasurable.integral_prod_right'
  rw [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t]
  have hcomp := hbase.comp_measurable
    (comap_measurable (ReferenceSourceCurrentControlFreshness.c_t p control0 t))
  have heq : (fun z : SourceInput p =>
      ∫ c, B.indicator (fun _ => (1 : ℝ))
        (sectionMap rate rewards C_star C_h t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, c))
        ∂ContinuousLearningRows.timeControlLaw p) =
      vectorSection rate rewards C_star C_h t B :=
    funext (controlSection_eq_vectorSection rate rewards C_star C_h control0 t B)
  exact heq ▸ hcomp

/-- Pointwise bounds include all absent and failed branches. -/
theorem vectorSection_bounds
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p)) (hB : MeasurableSet B) (z : SourceInput p) :
    0 ≤ vectorSection rate rewards C_star C_h t B z ∧
      vectorSection rate rewards C_star C_h t B z ≤ 1 := by
  let f : ContinuousLearningRows.TimeControl p → ℝ := fun c =>
    B.indicator (fun _ => (1 : ℝ)) (sectionMap rate rewards C_star C_h t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, c))
  have hf : Measurable f := (measurable_const.indicator hB).comp
    ((measurable_sectionMap rate rewards C_star C_h t).comp
      (measurable_const.prodMk measurable_id))
  have hzero (c) : 0 ≤ f c := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hone (c) : f c ≤ 1 := by
    by_cases h : sectionMap rate rewards C_star C_h t
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, c) ∈ B <;>
      simp only [f, Set.indicator, h, ite_true, ite_false, le_refl, zero_le_one]
  have hnorm (c) : ‖f c‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hzero c)]
    exact hone c
  have hint : Integrable f (ContinuousLearningRows.timeControlLaw p) :=
    (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall hnorm)
  rw [← controlSection_eq_vectorSection rate rewards C_star C_h control0 t B z]
  change 0 ≤ ∫ c, f c ∂ContinuousLearningRows.timeControlLaw p ∧
    (∫ c, f c ∂ContinuousLearningRows.timeControlLaw p) ≤ 1
  constructor
  · exact integral_nonneg hzero
  · calc
      _ ≤ ∫ _, (1 : ℝ) ∂ContinuousLearningRows.timeControlLaw p :=
        integral_mono_ae hint (integrable_const 1) (Filter.Eventually.of_forall hone)
      _ = 1 := by simp only [integral_const, probReal_univ, one_smul]

/-- Integrability is unconditional, with the original source probability law. -/
theorem vectorSection_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B : Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      CheckedAssignmentSample.AssignmentVector p)) (hB : MeasurableSet B) :
    Integrable (vectorSection rate rewards C_star C_h t B) (sourceInputLaw p) := by
  have hmeas := (vectorSection_stronglyMeasurable
    rate rewards C_star C_h control0 t B hB).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1))
  apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with z
  obtain ⟨hzero, hone⟩ := vectorSection_bounds rate rewards C_star C_h control0 t B hB z
  rw [Real.norm_of_nonneg hzero]
  exact hone

end Bandits.Support.ReferenceCalendarLaterSamplerOutputSections

end
