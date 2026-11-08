/-
Copyright (c) 2026 The Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCalendarLaterSamplerOutputSections

/-!
# Actual calendar checked-sampler finite-fibre law

This module projects the existing later-sampler output to its complete
optional checked slow-set result and identifies its full-vector sections with
the finite fibres of the original continuous assignment law. Sampler absence
and checked-sample failure remain distinct. No normalized sampler law or
physical/logical coupling is asserted.

Sources: `sources/zip4/manuscript/06_interruptions.tex:246-299,376-426`,
`sources/zip4/manuscript/05_binary_transport.tex:354-431`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceCalendarLaterSamplerFibreMass

variable {p : ConstructorDimensions.Parameters}

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⊤

local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (AssignmentParameterFibreKernel.Outcome p) := ⟨fun _ => trivial⟩

local instance activeOutcomeOptionMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (AssignmentParameterFibreKernel.Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

private theorem measurableSet_option_singleton {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet[LaterAssignmentStartMeasurability.optionMeasurableSpace] {a} := by
  let e := Equiv.optionEquivSumPUnit α
  have he : @Measurable (Option α) (α ⊕ PUnit)
      LaterAssignmentStartMeasurability.optionMeasurableSpace inferInstance e :=
    comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    exact ⟨fun h => congrArg e h, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

local instance outcomeOptionMeasurableSingletonClass (p : ConstructorDimensions.Parameters) :
    @MeasurableSingletonClass (Option (AssignmentParameterFibreKernel.Outcome p))
      LaterAssignmentStartMeasurability.optionMeasurableSpace :=
  ⟨measurableSet_option_singleton⟩

private def codeSlow (p : ConstructorDimensions.Parameters)
    (code : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p) :
    AssignmentParameterFibreKernel.Outcome p :=
  match code with
  | .sampled outcome => CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
  | _ => none

variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p) (C_star C_h : ℝ)

/-- The actual optional operation output, projected to its selected checked
slow-set outcome. The outer `none` means no selected sampler; `some none`
retains a checked-sample failure.
-/
def activeOutcomeAt (t : Fin p.T) (z : SourceInput p) :
    Option (AssignmentParameterFibreKernel.Outcome p) :=
  (ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t z).bind
    fun o => o.2.1.map fun _ =>
      match o.1 with
      | .sampled outcome => CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
      | _ => none

private def projectOutput (p : ConstructorDimensions.Parameters)
    (o : Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p)) :
    Option (AssignmentParameterFibreKernel.Outcome p) :=
  o.bind fun value => value.2.1.map fun _ => codeSlow p value.1

private theorem codeSlow_codeOfCheckedSample (p : ConstructorDimensions.Parameters)
    (sample : CheckedAssignmentSample.Result p) :
    codeSlow p (LaterAssignmentStartMeasurability.codeOfCheckedSample p sample) =
      CheckedAssignmentSample.successfulSlowSet p sample := by
  cases sample <;> rfl

/-- On every actual output carrying a selected parameter, the operation code
is the checked sampler applied to the entire original assignment vector.
-/
theorem activeOutcomeAt_eq_selectedSampler (t : Fin p.T) (z : SourceInput p)
    (o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (ho : ReferenceCalendarLaterSamplerOutputSections.outputAt
      rate rewards C_star C_h t z = some o) (hp : o.2.1 = some theta) :
    activeOutcomeAt rate rewards C_star C_h t z = some
      (AssignmentParameterFibreKernel.successfulSlowSet p theta
        (ContinuousControlSlice.assignmentVector
          (ReferenceSourceCurrentControlFreshness.u_t p t z).1)) := by
  obtain ⟨_, hcode⟩ := ReferenceCalendarLaterSamplerOutputSections.outputAt_code_vector
    rate rewards C_star C_h t z o theta ho hp
  simp only [activeOutcomeAt, ho, Option.bind_some, hp, Option.map_some]
  rw [hcode]
  change some (codeSlow p _) = _
  rw [codeSlow_codeOfCheckedSample]
  rfl

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
      · have hvt : v ≠ t := by
          intro h
          subst v
          exact (Nat.lt_irrefl _) hv
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
    ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
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

private theorem actualRecord_vector (t : Fin p.T) (z : SourceInput p)
    (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
    (hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z = some r) :
    LaterAssignmentStartOperation.ownAssignmentVector r.input.row r.input.time =
      ContinuousControlSlice.assignmentVector
        (ReferenceSourceCurrentControlFreshness.u_t p t z).1 := by
  have hf := ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
    rate rewards C_star C_h t z r hr
  change ContinuousControlSlice.assignmentVector
      ((r.input.rows r.input.selected).2 r.input.time).1 = _
  rw [hf.1, hf.2.1, hf.2.2.1]
  rfl

private theorem outputAt_replace (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c) =
      match ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z with
      | none => none
      | some r => ReferenceCalendarLaterSamplerOutputSections.outputOnInput
          (ReferenceLaterAssignmentFibreStep.withAssignment r.input
            (ContinuousControlSlice.assignmentVector c.1)) := by
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
    (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c
  have hi := incoming_replace rate rewards C_star C_h control0 t z c
  change ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z' =
    ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t z at hi
  unfold ReferenceSourcePrefixHistoryFiltration.incoming at hi
  change ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t z' = _
  unfold ReferenceCalendarLaterSamplerOutputSections.outputAt
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
            (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
              rate rewards C_star C_h t z' r' hr').2.2.1.trans
              (ReferenceCalendarLaterSamplerOutputSections.actualRecord_fields
                rate rewards C_star C_h t z r hr).2.2.1.symm
          have hv := actualRecord_vector rate rewards C_star C_h t z' r' hr'
          change _ = ContinuousControlSlice.assignmentVector
            (ReferenceSourceCurrentControlFreshness.u_t p t z').1 at hv
          rw [replaced_control] at hv
          have hinsert : LaterAssignmentStartOperation.ownAssignmentVector
              (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                (ContinuousControlSlice.assignmentVector c.1)).row
              (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                (ContinuousControlSlice.assignmentVector c.1)).time =
              ContinuousControlSlice.assignmentVector c.1 := by
            rw [ReferenceLaterAssignmentFibreStep.withAssignment_row]
            exact ReferenceLaterAssignmentFibreStep.ownAssignmentVector_rowWithAssignment _ _
          unfold ReferenceCalendarLaterSamplerOutputSections.outputOnInput
          rw [ReferenceCalendarLaterSamplerOutputSections.canonicalDiagnostics_eq_of_reads
            r'.input
            (ReferenceLaterAssignmentFibreStep.withAssignment r.input
              (ContinuousControlSlice.assignmentVector c.1)) hs ht (hv.trans hinsert.symm)]

private theorem calendarParameters_replace (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c) =
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z := by
  calc
    _ = ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c)) :=
      ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
        rate rewards C_star C_h control0 t _
    _ = ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) := by
      rw [sourcePrefix_replace,
        ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix control0 t z,
        ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
          control0 t.val t.val le_rfl]
    _ = ReferenceCalendarLaterSamplerPredictability.calendarParameters rate rewards C_star C_h t z :=
      (ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
        rate rewards C_star C_h control0 t z).symm

private theorem activeOutcomeAt_replace_control
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) (z : SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) (theta : AssignmentParameterFibreKernel.Theta p)
    (hparam : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z = some theta) :
    activeOutcomeAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c) =
      some (AssignmentParameterFibreKernel.successfulSlowSet p theta
        (ContinuousControlSlice.assignmentVector c.1)) := by
  let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
    (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c
  change activeOutcomeAt rate rewards C_star C_h t z' = _
  have hselected :
      (ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t z').bind
        (fun o => o.2.1) = some theta := by
    rw [ReferenceCalendarLaterSamplerOutputSections.outputAt_parameters,
      calendarParameters_replace rate rewards C_star C_h control0 t z c, hparam]
  cases hout : ReferenceCalendarLaterSamplerOutputSections.outputAt
      rate rewards C_star C_h t z' with
  | none =>
      simp only [hout, Option.bind_none] at hselected
      cases hselected
  | some o =>
      have hp : o.2.1 = some theta := by
        simpa only [hout, Option.bind_some] using hselected
      have hcode := ReferenceCalendarLaterSamplerOutputSections.outputAt_code_vector
        rate rewards C_star C_h t z' o theta hout hp
      have hcontrol : ReferenceSourceCurrentControlFreshness.u_t p t z' = c := by
        dsimp [z']
        exact replaced_control t (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c
      rw [hcontrol] at hcode
      have hv : o.2.2.2.1 = ContinuousControlSlice.assignmentVector c.1 := by
        exact hcode.1
      have hcode' : o.1 = LaterAssignmentStartMeasurability.codeOfCheckedSample p
          (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
            (ContinuousControlSlice.assignmentVector c.1)) := by
        exact hcode.2
      simp only [activeOutcomeAt, hout, Option.bind_some, hp, Option.map_some, hcode']
      change some (codeSlow p
         (LaterAssignmentStartMeasurability.codeOfCheckedSample p
           (CheckedAssignmentSample.checkedAssignmentSample p theta.1 theta.2
             (ContinuousControlSlice.assignmentVector c.1)))) = _
      rw [codeSlow_codeOfCheckedSample]
      rfl

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
  have hlift : Measurable (Sum.elim f (fun _ : PUnit => (none : Option Z))) := by
    apply measurable_fun_sum
    · exact hf
    · exact measurable_const
  rw [heq]
  exact hlift.comp (e.measurable.comp hinput)

private theorem measurable_codeSlow (p : ConstructorDimensions.Parameters) :
    Measurable (codeSlow p) := Measurable.of_discrete

private theorem measurable_selectedProjection (p : ConstructorDimensions.Parameters) :
    Measurable (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      o.2.1.map fun _ => codeSlow p o.1) := by
  let Code := LaterAssignmentStartMeasurability.LaterAssignmentStartCode p
  let Theta := AssignmentParameterFibreKernel.Theta p
  let Out := AssignmentParameterFibreKernel.Outcome p
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv Theta Code
  let decode : (Theta × Code) ⊕ (PUnit × Code) → Option Out :=
    Sum.elim (fun q => some (codeSlow p q.2)) (fun _ => none)
  have hdecode : Measurable decode := by
    apply measurable_fun_sum
    · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
        (fun q : Theta × Code => codeSlow p q.2)
        ((measurable_codeSlow p).comp measurable_snd)
    · exact measurable_const
  have harg : Measurable (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      (o.2.1, o.1)) :=
    (measurable_fst.comp measurable_snd).prodMk measurable_fst
  have heq : (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      o.2.1.map fun _ => codeSlow p o.1) = fun o => decode (e (o.2.1, o.1)) := by
    funext o
    cases h : o.2.1 <;> rfl
  rw [heq]
  exact hdecode.comp (e.measurable.comp harg)

private theorem measurable_projectOutput (p : ConstructorDimensions.Parameters) :
    Measurable (projectOutput p) := by
  exact measurable_optionBind _ measurable_id _ (measurable_selectedProjection p)

private def fibreVectorEvent (p : ConstructorDimensions.Parameters)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) :
    Set (Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      AssignmentParameterFibreKernel.AssignmentVector p) :=
  {x : Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
      AssignmentParameterFibreKernel.AssignmentVector p |
    projectOutput p x.1 = some a ∧ x.2 ∈ C}

private theorem measurableSet_fibreVectorEvent (p : ConstructorDimensions.Parameters)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p))
    (hC : MeasurableSet C) : MeasurableSet (fibreVectorEvent p a C) := by
  change MeasurableSet
    ({x : Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
        AssignmentParameterFibreKernel.AssignmentVector p |
      projectOutput p x.1 = some a} ∩
      {x : Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p) ×
        AssignmentParameterFibreKernel.AssignmentVector p | x.2 ∈ C})
  apply MeasurableSet.inter
  · exact (measurable_projectOutput p).comp measurable_fst (measurableSet_singleton (some a))
  · exact hC.preimage measurable_snd

private theorem projectOutput_eq_none_of_selected_none (p : ConstructorDimensions.Parameters)
    (o : Option (LaterAssignmentFullOutputMeasurability.FullOutputObservation p))
    (h : o.bind (fun value => value.2.1) = none) : projectOutput p o = none := by
  cases o with
  | none => rfl
  | some value =>
      simp only [Option.bind_some] at h
      simp [projectOutput, h]

private theorem assignment_integral (f : AssignmentParameterFibreKernel.AssignmentVector p → ℝ) :
    (∫ c, f (ContinuousControlSlice.assignmentVector c.1)
      ∂ContinuousLearningRows.timeControlLaw p) =
      ∫ v, f v ∂ContinuousControlSlice.assignmentLaw p.K := by
  have hs := (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).integral_comp'
    (fun x => f x.1)
  change (∫ c, f (ContinuousControlSlice.assignmentVector c.1)
    ∂ContinuousLearningRows.timeControlLaw p) = _ at hs
  rw [hs, integral_fun_fst]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]

private theorem vectorSection_fibreVectorEvent_eq (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (hC : MeasurableSet C)
    (z : SourceInput p) :
    ReferenceCalendarLaterSamplerOutputSections.vectorSection rate rewards C_star C_h t
      (fibreVectorEvent p a C) z =
      match ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z with
      | none => 0
      | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
          (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal := by
  classical
  cases hr : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h t z with
  | none =>
      have htheta : ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z = none := by
        rw [← ReferenceCalendarLaterSamplerOutputSections.outputAt_parameters
          rate rewards C_star C_h t z]
        simp [ReferenceCalendarLaterSamplerOutputSections.outputAt, hr]
      simp [ReferenceCalendarLaterSamplerOutputSections.vectorSection,
        fibreVectorEvent, projectOutput, hr, htheta]
  | some r =>
      simp only [ReferenceCalendarLaterSamplerOutputSections.vectorSection, hr]
      cases htheta : ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z with
      | none =>
          let f : AssignmentParameterFibreKernel.AssignmentVector p → ℝ := fun v =>
            (fibreVectorEvent p a C).indicator (fun _ => (1 : ℝ))
              (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                (ReferenceLaterAssignmentFibreStep.withAssignment r.input v), v)
          have hzero (c : ContinuousLearningRows.TimeControl p) :
              projectOutput p (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                  (ContinuousControlSlice.assignmentVector c.1))) = none := by
            let z' := ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
              (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c
            have hrep := outputAt_replace rate rewards C_star C_h control0 t z c
            rw [hr] at hrep
            have hparam' : ReferenceCalendarLaterSamplerPredictability.calendarParameters
                rate rewards C_star C_h t z' = none := by
              rw [calendarParameters_replace rate rewards C_star C_h control0 t z c, htheta]
            have hselected := ReferenceCalendarLaterSamplerOutputSections.outputAt_parameters
              rate rewards C_star C_h t z'
            rw [hrep] at hselected
            rw [hparam'] at hselected
            exact projectOutput_eq_none_of_selected_none p _ hselected
          rw [← assignment_integral (p := p) f]
          have hfun : (fun c : ContinuousLearningRows.TimeControl p =>
              f (ContinuousControlSlice.assignmentVector c.1)) = fun _ => (0 : ℝ) := by
            funext c
            have hmem :
                (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                  (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                    (ContinuousControlSlice.assignmentVector c.1)),
                  ContinuousControlSlice.assignmentVector c.1) ∉ fibreVectorEvent p a C := by
              simp [fibreVectorEvent, hzero c]
            change (fibreVectorEvent p a C).indicator (fun _ => (1 : ℝ))
              (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                  (ContinuousControlSlice.assignmentVector c.1)),
                ContinuousControlSlice.assignmentVector c.1) = 0
            exact Set.indicator_of_notMem hmem _
          rw [hfun, integral_zero]
      | some theta =>
          let E : Set (AssignmentParameterFibreKernel.AssignmentVector p) :=
            {v | AssignmentParameterFibreKernel.successfulSlowSet p theta v = a ∧ v ∈ C}
          let f : AssignmentParameterFibreKernel.AssignmentVector p → ℝ := fun v =>
            (fibreVectorEvent p a C).indicator (fun _ => (1 : ℝ))
              (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                (ReferenceLaterAssignmentFibreStep.withAssignment r.input v), v)
          have hrep (c : ContinuousLearningRows.TimeControl p) :
              ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
                (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                  (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c) =
              ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                  (ContinuousControlSlice.assignmentVector c.1)) := by
            have h := outputAt_replace rate rewards C_star C_h control0 t z c
            rw [hr] at h
            exact h
          have hparam : ReferenceCalendarLaterSamplerPredictability.calendarParameters
              rate rewards C_star C_h t z = some theta := htheta
          have hfun : (fun c : ContinuousLearningRows.TimeControl p =>
              f (ContinuousControlSlice.assignmentVector c.1)) =
              fun c => E.indicator (fun _ => (1 : ℝ))
                (ContinuousControlSlice.assignmentVector c.1) := by
            funext c
            have hproject := activeOutcomeAt_replace_control rate rewards C_star C_h control0
              t z c theta hparam
            have hproject' : projectOutput p
                (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                  (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                    (ContinuousControlSlice.assignmentVector c.1))) =
                some (AssignmentParameterFibreKernel.successfulSlowSet p theta
                  (ContinuousControlSlice.assignmentVector c.1)) := by
              change projectOutput p
                (ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t
                  (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                    (ReferenceSourceCurrentControlFreshness.c_t p control0 t z) c)) = _ at hproject
              rw [hrep c] at hproject
              simpa only [codeSlow] using hproject
            by_cases hv : AssignmentParameterFibreKernel.successfulSlowSet p theta
                (ContinuousControlSlice.assignmentVector c.1) = a ∧
                  ContinuousControlSlice.assignmentVector c.1 ∈ C
            · have hmem :
                (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                  (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                    (ContinuousControlSlice.assignmentVector c.1)),
                  ContinuousControlSlice.assignmentVector c.1) ∈ fibreVectorEvent p a C :=
                ⟨hproject'.trans (congrArg some hv.1), hv.2⟩
              change (fibreVectorEvent p a C).indicator (fun _ => (1 : ℝ))
                  (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                    (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                      (ContinuousControlSlice.assignmentVector c.1)),
                    ContinuousControlSlice.assignmentVector c.1) =
                E.indicator (fun _ => (1 : ℝ)) (ContinuousControlSlice.assignmentVector c.1)
              simp [Set.indicator, E, hmem, hv]
            · have hmem :
                (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                  (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                    (ContinuousControlSlice.assignmentVector c.1)),
                  ContinuousControlSlice.assignmentVector c.1) ∉ fibreVectorEvent p a C := by
                intro hm
                exact hv ⟨Option.some.inj (hproject'.symm.trans hm.1), hm.2⟩
              change (fibreVectorEvent p a C).indicator (fun _ => (1 : ℝ))
                  (ReferenceCalendarLaterSamplerOutputSections.outputOnInput
                    (ReferenceLaterAssignmentFibreStep.withAssignment r.input
                      (ContinuousControlSlice.assignmentVector c.1)),
                    ContinuousControlSlice.assignmentVector c.1) =
                E.indicator (fun _ => (1 : ℝ)) (ContinuousControlSlice.assignmentVector c.1)
              simp [Set.indicator, E, hmem, hv]
          rw [← assignment_integral (p := p) f, hfun,
            assignment_integral (p := p) (fun v => E.indicator (fun _ => (1 : ℝ)) v)]
          let F : AssignmentParameterFibreKernel.AssignmentVector p →
              AssignmentParameterFibreKernel.Outcome p :=
            AssignmentParameterFibreKernel.successfulSlowSet p theta
          have hF : Measurable F := by
            exact (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
              measurable_prodMk_left
          have hFibre : MeasurableSet (FiniteFibreLift.fibre F a) :=
            hF (measurableSet_singleton a)
          have hset : E = C ∩ FiniteFibreLift.fibre F a := by
            ext v
            simp [E, F, FiniteFibreLift.fibre, and_comm]
          have hE : MeasurableSet E := by
            rw [hset]
            exact hC.inter hFibre
          have hmix := congrArg
            (fun μ : Measure (AssignmentParameterFibreKernel.AssignmentVector p) => μ.real C)
            (AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure p theta a)
          rw [measureReal_ennreal_smul_apply,
            measureReal_restrict_apply hC] at hmix
          have hproduct : (ContinuousControlSlice.assignmentLaw p.K).real E =
              (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
                (AssignmentParameterFibreKernel.fibreMeasure p theta a).real C := by
            calc
              _ = (ContinuousControlSlice.assignmentLaw p.K).real
                  (C ∩ FiniteFibreLift.fibre F a) := by rw [hset]
              _ = _ := hmix.symm
          calc
            _ = (ContinuousControlSlice.assignmentLaw p.K).real E :=
              integral_indicator_one hE
            _ = _ := hproduct

private theorem measurable_optionElim {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (input : X → Option Y) (hinput : Measurable input)
    (f : Y → Z) (hf : Measurable f) (z0 : Z) :
    Measurable (fun x => match input x with | none => z0 | some y => f y) := by
  let e : Option Y ≃ᵐ Y ⊕ PUnit := {
    toEquiv := Equiv.optionEquivSumPUnit Y
    measurable_toFun := comap_measurable _
    measurable_invFun := by
      rw [measurable_comap_iff]
      exact measurable_id }
  have heq : (fun x => match input x with | none => z0 | some y => f y) =
      fun x => Sum.elim f (fun _ : PUnit => z0) (e (input x)) := by
    funext x
    cases input x <;> rfl
  rw [heq]
  exact (Measurable.sumElim hf measurable_const).comp (e.measurable.comp hinput)

theorem fibreProbability_parameterMeasurable (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (hC : MeasurableSet C) :
    Measurable (fun theta : AssignmentParameterFibreKernel.Theta p =>
      (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
        (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) := by
  have harg : Measurable (fun theta : AssignmentParameterFibreKernel.Theta p => (theta, a)) :=
    measurable_id.prodMk measurable_const
  have hm := (AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp harg
  have hq := (AssignmentParameterFibreKernel.measurable_fibreMeasure_apply_joint p C hC).comp harg
  exact hm.ennreal_toReal.mul hq.ennreal_toReal

/-- The finite-fibre probability section is strongly measurable in the exact
original-source pre-choice filtration.
-/
theorem fibreProbability_stronglyMeasurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (hC : MeasurableSet C) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
            (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) := by
  let B := fibreVectorEvent p a C
  have hB : MeasurableSet B := measurableSet_fibreVectorEvent p a C hC
  have hsection : (fun z : SourceInput p =>
      ReferenceCalendarLaterSamplerOutputSections.vectorSection rate rewards C_star C_h t B z) =
      (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
            (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) := by
    funext z
    exact vectorSection_fibreVectorEvent_eq rate rewards C_star C_h control0 t a C hC z
  exact hsection ▸
    ReferenceCalendarLaterSamplerOutputSections.vectorSection_stronglyMeasurable
      rate rewards C_star C_h control0 t B hB

/-- The finite-fibre section is Borel measurable in the exact pre-choice
source-prefix filtration.
-/
theorem fibreProbability_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (hC : MeasurableSet C) :
    Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
            (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) := by
  exact (fibreProbability_stronglyMeasurable rate rewards C_star C_h
    control0 t a C hC).measurable

/-- The displayed finite-fibre section is pointwise in `[0,1]`, including
absent samplers and zero-mass outcome fibres.
-/
theorem fibreProbability_bounds
    (t : Fin p.T) (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (z : SourceInput p) :
    0 ≤ (match ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
      | none => 0
      | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
          (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) ∧
    (match ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
      | none => 0
      | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
          (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) ≤ 1 := by
  cases htheta : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
  | none => simp
  | some theta =>
      have hmass : AssignmentParameterFibreKernel.fibreMass p theta a ≤ 1 := by
        change ContinuousControlSlice.assignmentLaw p.K
          (FiniteFibreLift.fibre
            (AssignmentParameterFibreKernel.successfulSlowSet p theta) a) ≤ 1
        calc
          _ ≤ ContinuousControlSlice.assignmentLaw p.K Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hvec : AssignmentParameterFibreKernel.fibreMeasure p theta a C ≤ 1 := by
        have hprobability : IsProbabilityMeasure
            (AssignmentParameterFibreKernel.fibreMeasure p theta a) := by
          change IsProbabilityMeasure (FiniteFibreLift.fibreMeasure
            (ContinuousControlSlice.assignmentLaw p.K)
            (AssignmentParameterFibreKernel.successfulSlowSet p theta) a)
          exact FiniteFibreLift.instIsProbabilityMeasureFibreMeasure
            (μ := ContinuousControlSlice.assignmentLaw p.K)
            (F := AssignmentParameterFibreKernel.successfulSlowSet p theta) (a := a)
        calc
          _ ≤ AssignmentParameterFibreKernel.fibreMeasure p theta a Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := measure_univ
      have hx0 : 0 ≤ (AssignmentParameterFibreKernel.fibreMass p theta a).toReal :=
        ENNReal.toReal_nonneg
      have hx1 : (AssignmentParameterFibreKernel.fibreMass p theta a).toReal ≤ 1 := by
        calc
          _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hmass
          _ = 1 := ENNReal.toReal_one
      have hy0 : 0 ≤ (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal :=
        ENNReal.toReal_nonneg
      have hy1 : (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal ≤ 1 := by
        calc
          _ ≤ (1 : ℝ≥0∞).toReal := ENNReal.toReal_mono ENNReal.one_ne_top hvec
          _ = 1 := ENNReal.toReal_one
      constructor
      · exact mul_nonneg hx0 hy0
      · calc
          _ ≤ (AssignmentParameterFibreKernel.fibreMass p theta a).toReal := by
            nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hy1)]
          _ ≤ 1 := hx1

/-- The conditional section is integrable under the original private source
law, with no integrability premise.
-/
theorem fibreProbability_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (hC : MeasurableSet C) :
    Integrable
      (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
            (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal)
      (sourceInputLaw p) := by
  have hmeas := (fibreProbability_stronglyMeasurable rate rewards C_star C_h
    control0 t a C hC).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le (t.val + 1))
  apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with z
  obtain ⟨hzero, hone⟩ := fibreProbability_bounds rate rewards C_star C_h t a C z
  rw [Real.norm_of_nonneg hzero]
  exact hone

/-- On selected-parameter support the complete optional outcome masses sum to
one. With no selected sampler, this analytical section has total mass zero;
the `none` checked-sample failure row remains part of the sum.
-/
theorem fibreProbability_sum_outcomes
    (t : Fin p.T) (z : SourceInput p) :
    (∑ a : AssignmentParameterFibreKernel.Outcome p,
      (match ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal)) =
      (match ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z with
        | none => 0
        | some _ => (1 : ℝ)) := by
  classical
  cases htheta : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
  | none => simp
  | some theta =>
      have hsum := AssignmentParameterFibreKernel.sum_fibreMass_eq_one p theta
      have hfinite (a : AssignmentParameterFibreKernel.Outcome p) :
          AssignmentParameterFibreKernel.fibreMass p theta a ≠ ∞ := by
        change ContinuousControlSlice.assignmentLaw p.K
          (FiniteFibreLift.fibre
            (AssignmentParameterFibreKernel.successfulSlowSet p theta) a) ≠ ∞
        exact measure_ne_top _ _
      rw [← ENNReal.toReal_sum
        (s := Finset.univ)
        (f := fun a : AssignmentParameterFibreKernel.Outcome p =>
          AssignmentParameterFibreKernel.fibreMass p theta a)
        (fun a _ => hfinite a), hsum]
      simp

/-- Joint testing by an outcome and a Borel set of the full original
assignment vector has the actual finite-fibre conditional law on the same
source-prefix field as the output-section theorem.
-/
theorem activeOutcomeAt_vector_condExp
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : AssignmentParameterFibreKernel.Outcome p)
    (C : Set (AssignmentParameterFibreKernel.AssignmentVector p)) (hC : MeasurableSet C) :
    (sourceInputLaw p)[(fun z : SourceInput p =>
      Set.indicator {z | activeOutcomeAt rate rewards C_star C_h t z = some a ∧
        ContinuousControlSlice.assignmentVector
          (ReferenceSourceCurrentControlFreshness.u_t p t z).1 ∈ C}
        (fun _ => (1 : ℝ)) z) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      =ᵐ[sourceInputLaw p] (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta =>
            (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
              (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) := by
  let B := fibreVectorEvent p a C
  have hB : MeasurableSet B := measurableSet_fibreVectorEvent p a C hC
  have htest : (fun z : SourceInput p =>
      B.indicator (fun _ => (1 : ℝ))
        (ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t z,
          ContinuousControlSlice.assignmentVector
            (ReferenceSourceCurrentControlFreshness.u_t p t z).1)) =
      (fun z : SourceInput p =>
        Set.indicator {z | activeOutcomeAt rate rewards C_star C_h t z = some a ∧
          ContinuousControlSlice.assignmentVector
            (ReferenceSourceCurrentControlFreshness.u_t p t z).1 ∈ C}
          (fun _ => (1 : ℝ)) z) := by
    funext z
    have hproj : projectOutput p
        (ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t z) =
        activeOutcomeAt rate rewards C_star C_h t z := by
      rfl
    simp [Set.indicator, B, fibreVectorEvent, hproj]
  have hce := ReferenceCalendarLaterSamplerOutputSections.outputAt_vectorSection_condExp
    rate rewards C_star C_h control0 t B hB
  rw [htest] at hce
  have hsection :
      (fun z : SourceInput p =>
        ReferenceCalendarLaterSamplerOutputSections.vectorSection rate rewards C_star C_h t B z) =
      (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta =>
            (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
              (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) := by
    funext z
    exact vectorSection_fibreVectorEvent_eq rate rewards C_star C_h control0 t a C hC z
  have hsection' :
      ReferenceCalendarLaterSamplerOutputSections.vectorSection rate rewards C_star C_h t B =
        (fun z : SourceInput p =>
          match ReferenceCalendarLaterSamplerPredictability.calendarParameters
              rate rewards C_star C_h t z with
          | none => 0
          | some theta =>
              (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
                (AssignmentParameterFibreKernel.fibreMeasure p theta a C).toReal) :=
    by
      funext z
      exact congrFun hsection z
  rw [hsection'] at hce
  exact hce

/-- The constant-vector-test specialization is the actual finite-fibre law
for each complete optional checked outcome, including `none` failures.
-/
theorem activeOutcomeAt_condExp
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : AssignmentParameterFibreKernel.Outcome p) :
    (sourceInputLaw p)[(fun z : SourceInput p =>
      Set.indicator {z | activeOutcomeAt rate rewards C_star C_h t z = some a}
        (fun _ => (1 : ℝ)) z) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      =ᵐ[sourceInputLaw p] (fun z : SourceInput p =>
        match ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => 0
        | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal) := by
  have htest : (fun z : SourceInput p =>
      Set.indicator {z | activeOutcomeAt rate rewards C_star C_h t z = some a ∧
        ContinuousControlSlice.assignmentVector
          (ReferenceSourceCurrentControlFreshness.u_t p t z).1 ∈ (Set.univ : Set _)}
        (fun _ => (1 : ℝ)) z) =
      (fun z : SourceInput p => Set.indicator
        {z | activeOutcomeAt rate rewards C_star C_h t z = some a}
        (fun _ => (1 : ℝ)) z) := by
    funext z
    simp
  have h := activeOutcomeAt_vector_condExp rate rewards C_star C_h control0 t a Set.univ
    MeasurableSet.univ
  rw [htest] at h
  filter_upwards [h] with z hz
  cases htheta : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
  | none =>
      simpa [htheta, Set.indicator, Set.mem_ofPred_eq, Set.mem_univ] using hz
  | some theta =>
      have hprobability : IsProbabilityMeasure
          (AssignmentParameterFibreKernel.fibreMeasure p theta a) := by
        change IsProbabilityMeasure (FiniteFibreLift.fibreMeasure
          (ContinuousControlSlice.assignmentLaw p.K)
          (AssignmentParameterFibreKernel.successfulSlowSet p theta) a)
        exact FiniteFibreLift.instIsProbabilityMeasureFibreMeasure
          (μ := ContinuousControlSlice.assignmentLaw p.K)
          (F := AssignmentParameterFibreKernel.successfulSlowSet p theta) (a := a)
      have hprob :
          (AssignmentParameterFibreKernel.fibreMeasure p theta a Set.univ).toReal = 1 := by
        simp
      simpa [htheta, Set.indicator, Set.mem_ofPred_eq, Set.mem_univ, hprob] using hz
