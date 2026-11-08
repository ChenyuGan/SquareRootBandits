/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionOriginalSourceFibreTransport

/-!
# Marked current-control law on an original first-call cell

The tested mark retains the strict source prefix, the actual optional sampler
outcome, the whole assignment vector, and every remaining current-control
coordinate. The conditional field is the exact successor source-prefix field.

Sources: `06_interruptions.tex:391-426` and
`appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionMarkedCurrentConditionalLaw

open BootstrapPrivateRoundStreams (sourceInputLaw)
open ContinuousLearningRows (TimeControl)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open ReferenceCalendarLaterSamplerFibreMass (activeOutcomeAt)
open ReferenceFirstCollectionSamplerOutputLaw (currentAssignmentVector)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix sourcePrefixFiltration)
open ReferenceSourceCurrentControlFreshness (u_t)
open ReferenceFixedTimeSourceControlCoupling (replaceSourceControl)
open AssignmentParameterFibreKernel (Outcome AssignmentVector fibreMass fibreMeasure)
open ReferenceLaterOptionalControlResampling (ControlRemainder controlRemainderLaw)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

abbrev MarkedCurrentPair (p : ConstructorDimensions.Parameters) :=
  SourceInput p × (Option (Outcome p) ×
    (AssignmentVector p × ControlRemainder p))

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance outcomeMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Outcome p) := ⊤
local instance outcomeDiscreteMeasurableSpace (p : ConstructorDimensions.Parameters) :
    DiscreteMeasurableSpace (Outcome p) := ⟨fun _ => trivial⟩
local instance outcomeOptionMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (Option (Outcome p)) :=
  LaterAssignmentStartMeasurability.optionMeasurableSpace

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual current mark, with the full split of the current control. -/
def markedCurrentPair (control0 : TimeControl p) (t : Fin p.T)
    (z : SourceInput p) : MarkedCurrentPair p :=
  (sourcePrefix control0 t.val z,
    (activeOutcomeAt rate rewards C_star C_h t z,
      (currentAssignmentVector t z,
        (controlAssignmentSplitEquiv p (u_t p t z)).2)))

/-- A Borel test of the entire marked current pair. -/
def markedCurrentTest (control0 : TimeControl p) (t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (z : SourceInput p) : ℝ :=
  B0.indicator (fun _ => (1 : ℝ)) (markedCurrentPair rate rewards C_star C_h control0 t z)

/-- The unnormalized finite-fibre section, including the analytical absent-
parameter zero branch. -/
def markedCurrentSection (control0 : TimeControl p) (t : Fin p.T)
    (a : Outcome p) (B0 : Set (MarkedCurrentPair p)) (z : SourceInput p) : ℝ :=
  match calendarParameters rate rewards C_star C_h t z with
  | none => 0
  | some theta => (fibreMass p theta a).toReal *
      ∫ vw : AssignmentVector p × ControlRemainder p,
        B0.indicator (fun _ => (1 : ℝ))
          (sourcePrefix control0 t.val z, (some a, vw))
        ∂(fibreMeasure p theta a).prod (controlRemainderLaw p)

abbrev JointY (p : ConstructorDimensions.Parameters) :=
  ReferenceFirstCollectionOriginalSourceFibreTransport.JointY p

/-- Project the original joint observation to the optional marked current
payload. The outer absence remains absence; it receives no fabricated state. -/
def projectOriginalCurrent (_control0 : TimeControl p) (t : Fin p.T)
    (q : JointY p) : Option (MarkedCurrentPair p) :=
  q.2.map fun y =>
    let payload := y.2.2
    (payload.1, (payload.2.1,
      (payload.2.2, (controlAssignmentSplitEquiv p (u_t p t q.1)).2)))

/-- Pull a Borel target test back along the optional joint projection. -/
def originalCurrentTestSet (control0 : TimeControl p) (t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) : Set (JointY p) :=
  {q | projectOriginalCurrent control0 t q ∈ some '' B0}

private theorem measurableSet_someImage {Y : Type*} [MeasurableSpace Y]
    (B : Set Y) (hB : MeasurableSet B) :
    MeasurableSet (some '' B : Set (Option Y)) := by
  change MeasurableSet[
    (inferInstance : MeasurableSpace (Y ⊕ PUnit)).comap
      (Equiv.optionEquivSumPUnit Y)] (some '' B)
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨Sum.inl '' B, measurableSet_inl_image.mpr hB, ?_⟩
  ext y
  cases y <;> simp

/-- The optional projection is jointly Borel on the original source and its
actual first-call observation. -/
theorem projectOriginalCurrent_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (fun q : JointY p =>
      projectOriginalCurrent control0 t q) := by
  let Body := Fin p.T × (Fin p.T ×
    ReferenceFirstCollectionPastSamplerFibreLaw.MarkedPayload p)
  have hbody : Measurable (fun b : Body =>
      (b.2.2.1, (b.2.2.2.1, b.2.2.2.2))) := by
    fun_prop
  have hrem : Measurable (fun q : SourceInput p × Body =>
      (controlAssignmentSplitEquiv p (u_t p t q.1)).2) :=
    measurable_snd.comp ((controlAssignmentSplitEquiv p).measurable.comp
      ((ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t).comp
        measurable_fst))
  have hproject : Measurable (fun r : Body × JointY p =>
      (r.1.2.2.1, (r.1.2.2.2.1,
        (r.1.2.2.2.2,
          (controlAssignmentSplitEquiv p (u_t p t r.2.1)).2)))) := by
    exact (measurable_fst.comp (hbody.comp measurable_fst)).prodMk
      ((measurable_fst.comp
          (measurable_snd.comp (hbody.comp measurable_fst))).prodMk
        ((measurable_snd.comp
            (measurable_snd.comp (hbody.comp measurable_fst))).prodMk
          (measurable_snd.comp ((controlAssignmentSplitEquiv p).measurable.comp
            ((ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t).comp
              (measurable_fst.comp measurable_snd))))))
  let projectionOnBody : Body × JointY p → MarkedCurrentPair p := fun r =>
    (r.1.2.2.1, (r.1.2.2.2.1,
      (r.1.2.2.2.2, (controlAssignmentSplitEquiv p (u_t p t r.2.1)).2)))
  simpa only [projectOriginalCurrent, projectionOnBody] using
      ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      projectionOnBody hproject (fun q : JointY p => q.2) measurable_snd

/-- Every Borel current-pair test has a Borel preimage in the original joint
observation, including its analytic outer-absence branch. -/
theorem originalCurrentTestSet_measurable (control0 : TimeControl p) (t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0) :
    MeasurableSet (originalCurrentTestSet control0 t B0) := by
  exact (projectOriginalCurrent_measurable control0 t)
    (measurableSet_someImage B0 hB0)

private theorem currentControl_replace (t : Fin p.T) (z : SourceInput p)
    (c : TimeControl p) :
    u_t p t (replaceSourceControl p t z c) = c := by
  simp [ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex]

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
      fun x => Sum.elim f (fun _ : PUnit => (none : Option Z)) (e (input x)) := by
    funext x
    cases input x <;> rfl
  have hlift : Measurable (Sum.elim f (fun _ : PUnit => (none : Option Z))) := by
    apply measurable_fun_sum
    · exact hf
    · exact measurable_const
  rw [heq]
  exact hlift.comp (e.measurable.comp hinput)

private theorem projectedReplacement (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (a : Outcome p)
    (vw : AssignmentVector p × ControlRemainder p) :
    projectOriginalCurrent control0 t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z
          ((controlAssignmentSplitEquiv p).symm vw),
        some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1))))) =
      some (sourcePrefix control0 t.val z, (some a, vw)) := by
  simp [projectOriginalCurrent, currentControl_replace,
    (controlAssignmentSplitEquiv p).apply_symm_apply]

/-- On the original first-call cell, the joint projection is exactly the
actual marked current pair. The call tags and the sampler trace are produced
from the original source at this point. -/
theorem projectOriginalCurrent_actual_on_cell (control0 : TimeControl p)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    projectOriginalCurrent control0 t
      (z, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput
        rate rewards C_star C_h control0 z) =
      some (markedCurrentPair rate rewards C_star C_h control0 t z) := by
  obtain ⟨theta, o, _htheta, _hout, _hparam, _hvec, _hcode, hactive⟩ :=
    ReferenceFirstCollectionSamplerFibreLaw.firstCell_actualSamplerTrace
      rate rewards C_star C_h u t z hz
  have htags :=
    (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
      rate rewards C_star C_h u t z).mp hz
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at htags
  | some c =>
      simp only [hcall, Option.map_some, Option.some.injEq] at htags
      have hu : c.1 = u := congrArg Prod.fst htags
      have ht : c.2.1 = t := congrArg Prod.snd htags
      simp [projectOriginalCurrent,
        ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput,
        hcall, hu, ht, markedCurrentPair, hactive]

/-- Each per-outcome section is the corresponding section of the admitted
original-source joint transport. -/
theorem markedCurrentSection_eq_originalSourceSection (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B0 : Set (MarkedCurrentPair p))
    (_hB0 : MeasurableSet B0) (z : SourceInput p) :
    markedCurrentSection rate rewards C_star C_h control0 t a B0 z =
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
        rate rewards C_star C_h control0 u t a
        (originalCurrentTestSet control0 t B0) z := by
  cases htheta : calendarParameters rate rewards C_star C_h t z with
  | none =>
      simp [markedCurrentSection,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection, htheta]
  | some theta =>
    simp only [markedCurrentSection,
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection, htheta]
    apply congrArg (fun x : ℝ => (fibreMass p theta a).toReal * x)
    apply integral_congr_ae
    filter_upwards [] with vw
    change (if (sourcePrefix control0 t.val z, (some a, vw)) ∈ B0 then 1 else 0) =
      (if projectOriginalCurrent control0 t
        (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
          some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1))))) ∈
        some '' B0 then 1 else 0)
    rw [projectedReplacement control0 u t z a vw]
    simp [Set.mem_image]

/-- Ambient Borel measurability of each section, obtained from the admitted
joint transport. -/
theorem markedCurrentSection_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B0 : Set (MarkedCurrentPair p))
    (hB0 : MeasurableSet B0) :
    Measurable (markedCurrentSection rate rewards C_star C_h control0 t a B0) := by
  have hB := originalCurrentTestSet_measurable control0 t B0 hB0
  have hsection : Measurable
      (ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
        rate rewards C_star C_h control0 u t a
        (originalCurrentTestSet control0 t B0)) :=
    ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_measurable
    rate rewards C_star C_h control0 u t a
    (originalCurrentTestSet control0 t B0) hB
  have heq : markedCurrentSection rate rewards C_star C_h control0 t a B0 =
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
        rate rewards C_star C_h control0 u t a
        (originalCurrentTestSet control0 t B0) :=
    funext (markedCurrentSection_eq_originalSourceSection rate rewards C_star C_h
      control0 u t a B0 hB0)
  rw [heq]
  exact hsection

/-- Every section remains in `[0,1]`, including zero-mass fibres. -/
theorem markedCurrentSection_bounds (control0 : TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0)
    (z : SourceInput p) :
    0 ≤ markedCurrentSection rate rewards C_star C_h control0 t a B0 z ∧
      markedCurrentSection rate rewards C_star C_h control0 t a B0 z ≤ 1 := by
  rw [markedCurrentSection_eq_originalSourceSection rate rewards C_star C_h
    control0 u t a B0 hB0 z]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_bounds
    rate rewards C_star C_h control0 u t a
    (originalCurrentTestSet control0 t B0)
    (originalCurrentTestSet_measurable control0 t B0 hB0) z

/-- Each section is integrable under the complete original source law. -/
theorem markedCurrentSection_integrable (control0 : TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0) :
    Integrable (markedCurrentSection rate rewards C_star C_h control0 t a B0)
      (sourceInputLaw p) := by
  rw [show markedCurrentSection rate rewards C_star C_h control0 t a B0 =
      ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
        rate rewards C_star C_h control0 u t a
        (originalCurrentTestSet control0 t B0) from
    funext (markedCurrentSection_eq_originalSourceSection rate rewards C_star C_h
      control0 u t a B0 hB0)]
  exact ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection_integrable
    rate rewards C_star C_h control0 u t a
    (originalCurrentTestSet control0 t B0)
    (originalCurrentTestSet_measurable control0 t B0 hB0)

/-- The tested actual current mark is Borel. -/
theorem markedCurrentPair_measurable (control0 : TimeControl p) (t : Fin p.T) :
    Measurable (markedCurrentPair rate rewards C_star C_h control0 t) := by
  have hprefix := ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
    control0 t.val
  have houtput := ReferenceCalendarLaterSamplerOutputSections.measurable_outputAt
    rate rewards C_star C_h t
  have hcode : Measurable (fun o :
      LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
      o.2.1.map fun _ =>
        match o.1 with
        | LaterAssignmentStartMeasurability.LaterAssignmentStartCode.sampled outcome =>
            CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
        | _ => none) := by
    let codeSlow : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p →
        Outcome p := fun code => match code with
      | .sampled outcome => CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
      | _ => none
    have hcodeSlow : Measurable codeSlow := Measurable.of_discrete
    let Code := LaterAssignmentStartMeasurability.LaterAssignmentStartCode p
    let Theta := AssignmentParameterFibreKernel.Theta p
    let Out := AssignmentParameterFibreKernel.Outcome p
    let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv Theta Code
    let decode : (Theta × Code) ⊕ (PUnit × Code) → Option Out :=
      Sum.elim (fun q => some (codeSlow q.2)) (fun _ => none)
    have hdecode : Measurable decode := by
      apply measurable_fun_sum
      · exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
          (fun q : Theta × Code => codeSlow q.2)
          (hcodeSlow.comp measurable_snd)
      · exact measurable_const
    have harg : Measurable (fun o :
        LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
        (o.2.1, o.1)) :=
      (measurable_fst.comp measurable_snd).prodMk measurable_fst
    have heq : (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
        o.2.1.map fun _ => codeSlow o.1) = fun o => decode (e (o.2.1, o.1)) := by
      funext o
      cases h : o.2.1 <;> rfl
    rw [heq]
    exact hdecode.comp (e.measurable.comp harg)
  have hactive : Measurable (activeOutcomeAt rate rewards C_star C_h t) := by
    change Measurable (fun z =>
      (ReferenceCalendarLaterSamplerOutputSections.outputAt rate rewards C_star C_h t z).bind
        (fun o => o.2.1.map fun _ =>
          match o.1 with
          | LaterAssignmentStartMeasurability.LaterAssignmentStartCode.sampled outcome =>
              CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
          | _ => none))
    exact measurable_optionBind _ houtput _ hcode
  have hvector : Measurable (currentAssignmentVector t) :=
    (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
      (measurable_fst.comp
        (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t))
  have hsplit : Measurable (fun z : SourceInput p =>
      (controlAssignmentSplitEquiv p (u_t p t z)).2) := by
    exact (measurable_snd.comp
      ((controlAssignmentSplitEquiv p).measurable.comp
        (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t)))
  exact hprefix.prodMk (hactive.prodMk (hvector.prodMk hsplit))

/-- The actual tested variable is bounded and integrable. -/
theorem markedCurrentTest_bounds (control0 : TimeControl p) (t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (z : SourceInput p) :
    0 ≤ markedCurrentTest rate rewards C_star C_h control0 t B0 z ∧
      markedCurrentTest rate rewards C_star C_h control0 t B0 z ≤ 1 := by
  by_cases hz : markedCurrentPair rate rewards C_star C_h control0 t z ∈ B0 <;>
    simp [markedCurrentTest, Set.indicator, hz]

theorem markedCurrentTest_integrable (control0 : TimeControl p) (t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0) :
    Integrable (markedCurrentTest rate rewards C_star C_h control0 t B0)
      (sourceInputLaw p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_const.indicator hB0).comp
      (markedCurrentPair_measurable rate rewards C_star C_h control0 t)).aestronglyMeasurable)
  filter_upwards [] with z
  obtain ⟨h0, h1⟩ := markedCurrentTest_bounds rate rewards C_star C_h control0 t B0 z
  change ‖markedCurrentTest rate rewards C_star C_h control0 t B0 z‖ ≤ 1
  rw [Real.norm_of_nonneg h0]
  exact h1

private theorem section_eq_prefix (control0 : TimeControl p) (t : Fin p.T)
    (a : Outcome p) (B0 : Set (MarkedCurrentPair p)) (z : SourceInput p) :
    markedCurrentSection rate rewards C_star C_h control0 t a B0 z =
      markedCurrentSection rate rewards C_star C_h control0 t a B0
        (sourcePrefix control0 t.val z) := by
  have htheta := ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
    rate rewards C_star C_h control0 t z
  have hpref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix
    control0 t.val t.val le_rfl z
  simp [markedCurrentSection, htheta, hpref]

/-- Strong measurability of an individual section in exactly the successor
source-prefix field, using its strict-prefix factorization. -/
theorem markedCurrentSection_stronglyMeasurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B0 : Set (MarkedCurrentPair p))
    (hB0 : MeasurableSet B0) :
    StronglyMeasurable[
      sourcePrefixFiltration control0 (t.val + 1)]
      (markedCurrentSection rate rewards C_star C_h control0 t a B0) := by
  have hmeas := markedCurrentSection_measurable rate rewards C_star C_h
    control0 u t a B0 hB0
  have hfactor :
      markedCurrentSection rate rewards C_star C_h control0 t a B0 =
        markedCurrentSection rate rewards C_star C_h control0 t a B0 ∘
          sourcePrefix control0 t.val := by
    funext z
    exact section_eq_prefix rate rewards C_star C_h control0 t a B0 z
  rw [hfactor]
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
  have hcomp : Measurable[sourcePrefixFiltration control0 (t.val + 1)]
      (markedCurrentSection rate rewards C_star C_h control0 t a B0 ∘
        sourcePrefix control0 t.val) :=
    hmeas.comp (comap_measurable (sourcePrefix control0 t.val))
  exact hcomp.stronglyMeasurable

/-- The finite section sum is strongly measurable at the exact field
`sourcePrefixFiltration control0 (t.val + 1)`. -/
theorem markedCurrentSection_sum_stronglyMeasurable (control0 : TimeControl p)
    (u t : Fin p.T) (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0) :
    StronglyMeasurable[
      sourcePrefixFiltration control0 (t.val + 1)]
      (fun z => ∑ a : Outcome p,
        markedCurrentSection rate rewards C_star C_h control0 t a B0 z) := by
  classical
  apply Finset.stronglyMeasurable_fun_sum
  intro a ha
  exact markedCurrentSection_stronglyMeasurable rate rewards C_star C_h
    control0 u t a B0 hB0

private theorem test_set_measurable (control0 : TimeControl p) (t : Fin p.T)
    (A : Set (SourceInput p)) (B0 : Set (MarkedCurrentPair p))
    (hA : MeasurableSet A) (hB0 : MeasurableSet B0) :
    MeasurableSet {q : JointY p |
      q.1 ∈ A ∧
        projectOriginalCurrent control0 t q ∈
          some '' (B0 : Set (MarkedCurrentPair p))} := by
  exact hA.preimage measurable_fst |>.inter
    ((projectOriginalCurrent_measurable control0 t)
      (measurableSet_someImage B0 hB0))

private theorem actualTest_on_cell (control0 : TimeControl p) (u t : Fin p.T)
    (A : Set (SourceInput p)) (B0 : Set (MarkedCurrentPair p)) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    (({q : JointY p | q.1 ∈ A ∧
        projectOriginalCurrent control0 t q ∈ some '' B0} :
        Set (JointY p)).indicator (fun _ => (1 : ℝ))
      (ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceOutput
        rate rewards C_star C_h control0 z)) =
      A.indicator (fun y => markedCurrentTest rate rewards C_star C_h control0 t B0 y) z := by
  rw [ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceOutput]
  simp only [Set.indicator, Set.mem_ofPred_eq]
  rw [projectOriginalCurrent_actual_on_cell rate rewards C_star C_h control0 u t z hz]
  by_cases hzA : z ∈ A
  · simp [markedCurrentTest, Set.indicator, Set.mem_image, hzA]
  · simp [hzA]

private theorem sectionTest_eq_indicator (control0 : TimeControl p) (u t : Fin p.T)
    (A : Set (SourceInput p)) (B0 : Set (MarkedCurrentPair p))
    (hA : ∀ z c, replaceSourceControl p t z c ∈ A ↔ z ∈ A)
    (z : SourceInput p) (a : Outcome p) :
    ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
      rate rewards C_star C_h control0 u t a
        {q : JointY p | q.1 ∈ A ∧
          projectOriginalCurrent control0 t q ∈ some '' B0} z =
      A.indicator (fun y => markedCurrentSection rate rewards C_star C_h
        control0 t a B0 y) z := by
  cases htheta : calendarParameters rate rewards C_star C_h t z with
  | none =>
    simp only [ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection,
      markedCurrentSection, htheta, Set.indicator]
    by_cases hz : z ∈ A <;> simp [hz]
  | some theta =>
    simp only [ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection,
      markedCurrentSection, htheta, Set.indicator, Set.mem_ofPred_eq]
    by_cases hz : z ∈ A
    · simp only [hz, ite_true]
      apply congrArg (fun x : ℝ => (fibreMass p theta a).toReal * x)
      apply integral_congr_ae
      filter_upwards [] with vw
      have hrep : replaceSourceControl p t z
          ((controlAssignmentSplitEquiv p).symm vw) ∈ A := (hA z _).2 hz
      have hproj := projectedReplacement control0 u t z a vw
      rw [hproj]
      simp [hrep, Set.mem_image]
    · simp only [hz, ite_false]
      have hrep (vw : AssignmentVector p × ControlRemainder p) :
          replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw) ∉ A :=
        fun h => hz ((hA z _).mp h)
      simp [hrep]

/-- Every measurable event of the exact successor field satisfies the same
unnormalized cell integral identity. The event is pulled back through the
strict prefix, so whole-current-control replacement fixes it. -/
theorem markedCurrent_cell_setIntegral (control0 : TimeControl p) (u t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0)
    (A : Set (SourceInput p))
    (hA : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] A) :
    ∫ z in A,
        (firstCell rate rewards C_star C_h u t).indicator
          (markedCurrentTest rate rewards C_star C_h control0 t B0) z
      ∂sourceInputLaw p =
    ∫ z in A,
        (firstCell rate rewards C_star C_h u t).indicator
          (fun y => ∑ a : Outcome p,
            markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z
      ∂sourceInputLaw p := by
  classical
  let cell := firstCell rate rewards C_star C_h u t
  let pref := sourcePrefix control0 t.val
  let μ := sourceInputLaw p
  have hcellField : MeasurableSet[sourcePrefixFiltration control0 (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : sourcePrefixFiltration control0 (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
    (sourcePrefixFiltration control0).le (t.val + 1)
  have hcell : MeasurableSet cell := hfieldLe _ hcellField
  have hAglobal : MeasurableSet A := hfieldLe _ hA
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ control0 t.val] at hA
  obtain ⟨V, hV, hVA⟩ :=
    (MeasurableSpace.measurableSet_comap (f := pref)).mp hA
  have hArep : pref ⁻¹' V = A := hVA
  have hreplace (z : SourceInput p) (c : TimeControl p) :
      replaceSourceControl p t z c ∈ A ↔ z ∈ A := by
    rw [← hArep]
    change sourcePrefix control0 t.val (replaceSourceControl p t z c) ∈ V ↔
      sourcePrefix control0 t.val z ∈ V
    rw [ReferenceFirstCollectionOriginalSourceFibreTransport.sourcePrefix_replaceSourceControl]
  let B : Set (JointY p) := {q | q.1 ∈ A ∧
    projectOriginalCurrent control0 t q ∈ some '' B0}
  have hB : MeasurableSet B := by
    exact test_set_measurable control0 t A B0 hAglobal hB0
  have htransport :=
    ReferenceFirstCollectionOriginalSourceFibreTransport.originalSource_cell_integral
      rate rewards C_star C_h control0 u t B hB
  have hleft :
      ∫ z in cell, A.indicator
          (markedCurrentTest rate rewards C_star C_h control0 t B0) z ∂μ =
        ∫ z in cell,
          ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceTest
            rate rewards C_star C_h control0 B z ∂μ := by
    apply setIntegral_congr_ae hcell
    filter_upwards [] with z hz
    exact (actualTest_on_cell rate rewards C_star C_h control0 u t A B0 z hz).symm
  have hright :
      (∑ a : Outcome p, ∫ z in cell,
        A.indicator (fun y => markedCurrentSection rate rewards C_star C_h
          control0 t a B0 y) z ∂μ) =
      ∑ a : Outcome p, ∫ z in cell,
        ReferenceFirstCollectionOriginalSourceFibreTransport.originalSourceSection
          rate rewards C_star C_h control0 u t a B z ∂μ := by
    apply Finset.sum_congr rfl
    intro a _
    apply setIntegral_congr_ae hcell
    filter_upwards [] with z _
    exact (sectionTest_eq_indicator rate rewards C_star C_h control0 u t A B0
      hreplace z a).symm
  have hsum := hleft.trans (htransport.trans hright.symm)
  have hleftGlobal :
      ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
        (markedCurrentTest rate rewards C_star C_h control0 t B0)) z ∂μ =
      ∫ z in cell, A.indicator
        (markedCurrentTest rate rewards C_star C_h control0 t B0) z ∂μ := by
    rw [← integral_indicator hcell]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ cell <;> simp [Set.indicator, cell, hz]
  have hrightGlobal :
      ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
        (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y)) z ∂μ =
      ∫ z in cell, A.indicator (fun y => ∑ a : Outcome p,
        markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z ∂μ := by
    rw [← integral_indicator hcell]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ cell <;> simp [Set.indicator, cell, hz]
  have hsum_integral :
      ∫ z in cell, A.indicator (fun y => ∑ a : Outcome p,
        markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z ∂μ =
      ∑ a : Outcome p, ∫ z in cell,
        A.indicator (fun y => markedCurrentSection rate rewards C_star C_h
          control0 t a B0 y) z ∂μ := by
    calc
      _ = ∫ z in cell, (fun z => ∑ a : Outcome p,
          A.indicator (fun y => markedCurrentSection rate rewards C_star C_h
            control0 t a B0 y) z) z ∂μ := by
          apply setIntegral_congr_ae hcell
          filter_upwards [] with z _
          by_cases hzA : z ∈ A <;> simp [Set.indicator, hzA]
      _ = ∑ a : Outcome p, ∫ z in cell,
          A.indicator (fun y => markedCurrentSection rate rewards C_star C_h
            control0 t a B0 y) z ∂μ := by
          rw [integral_finsetSum Finset.univ (fun a _ =>
            (markedCurrentSection_integrable rate rewards C_star C_h
              control0 u t a B0 hB0).indicator hAglobal |>.integrableOn)]
  have hglobal :
      ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
        (markedCurrentTest rate rewards C_star C_h control0 t B0)) z ∂μ =
      ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
        (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y)) z ∂μ := by
    calc
      _ = ∫ z in cell, A.indicator
          (markedCurrentTest rate rewards C_star C_h control0 t B0) z ∂μ := hleftGlobal
      _ = ∑ a : Outcome p, ∫ z in cell,
          A.indicator (fun y => markedCurrentSection rate rewards C_star C_h
            control0 t a B0 y) z ∂μ := hsum
      _ = ∫ z in cell, A.indicator (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z ∂μ :=
            hsum_integral.symm
      _ = ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
          (fun y => ∑ a : Outcome p,
            markedCurrentSection rate rewards C_star C_h control0 t a B0 y)) z ∂μ :=
            hrightGlobal.symm
  calc
    _ = ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
        (markedCurrentTest rate rewards C_star C_h control0 t B0)) z ∂μ :=
          (integral_indicator hAglobal).symm
    _ = ∫ z, A.indicator ((firstCell rate rewards C_star C_h u t).indicator
        (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y)) z ∂μ := hglobal
    _ = ∫ z in A, (firstCell rate rewards C_star C_h u t).indicator
        (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z ∂μ :=
          integral_indicator hAglobal

/-- The same unnormalized first-cell integral, with every outcome included. -/
theorem markedCurrent_cell_integral (control0 : TimeControl p) (u t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0) :
    ∫ z in firstCell rate rewards C_star C_h u t,
        markedCurrentTest rate rewards C_star C_h control0 t B0 z
      ∂sourceInputLaw p =
    ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
      markedCurrentSection rate rewards C_star C_h control0 t a B0 z
      ∂sourceInputLaw p := by
  have h := markedCurrent_cell_setIntegral rate rewards C_star C_h
    control0 u t B0 hB0 Set.univ MeasurableSet.univ
  have hcell : MeasurableSet (firstCell rate rewards C_star C_h u t) := by
    have hf := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
    exact ((sourcePrefixFiltration control0).le (t.val + 1)) _ hf
  have h0 :
      ∫ z, (firstCell rate rewards C_star C_h u t).indicator
        (markedCurrentTest rate rewards C_star C_h control0 t B0) z ∂sourceInputLaw p =
      ∫ z, (firstCell rate rewards C_star C_h u t).indicator
        (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z
        ∂sourceInputLaw p := by
    simpa using h
  have hsum :
      ∫ z in firstCell rate rewards C_star C_h u t,
        (fun y => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 y) z
        ∂sourceInputLaw p =
      ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
        markedCurrentSection rate rewards C_star C_h control0 t a B0 z
        ∂sourceInputLaw p := by
    rw [integral_finsetSum Finset.univ (fun a _ =>
      (markedCurrentSection_integrable rate rewards C_star C_h
        control0 u t a B0 hB0).integrableOn)]
  rw [integral_indicator hcell, integral_indicator hcell] at h0
  exact h0.trans hsum

/-- The requested conditional whole-vector/remainder law on the exact
successor strict-past field. -/
theorem markedCurrent_cell_condExp (control0 : TimeControl p) (u t : Fin p.T)
    (B0 : Set (MarkedCurrentPair p)) (hB0 : MeasurableSet B0) :
    (sourceInputLaw p)[
      (firstCell rate rewards C_star C_h u t).indicator
        (markedCurrentTest rate rewards C_star C_h control0 t B0) |
      sourcePrefixFiltration control0 (t.val + 1)] =ᵐ[sourceInputLaw p]
      (firstCell rate rewards C_star C_h u t).indicator
        (fun z => ∑ a : Outcome p,
          markedCurrentSection rate rewards C_star C_h control0 t a B0 z) := by
  let μ := sourceInputLaw p
  let H := sourcePrefixFiltration control0
  let cell := firstCell rate rewards C_star C_h u t
  let test := markedCurrentTest rate rewards C_star C_h control0 t B0
  let sectionSum := fun z => ∑ a : Outcome p,
    markedCurrentSection rate rewards C_star C_h control0 t a B0 z
  let candidate := cell.indicator sectionSum
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt : Integrable test μ := by
    exact markedCurrentTest_integrable rate rewards C_star C_h control0 t B0 hB0
  have hleftInt : Integrable (cell.indicator test) μ := htestInt.indicator hcellGlobal
  have hsectionSumInt : Integrable sectionSum μ := by
    exact integrable_finsetSum Finset.univ fun a _ =>
      markedCurrentSection_integrable rate rewards C_star C_h control0 u t a B0 hB0
  have hcandidateInt : Integrable candidate μ := hsectionSumInt.indicator hcellGlobal
  have hcandidateMeas :
      StronglyMeasurable[H (t.val + 1)] candidate := by
    exact (markedCurrentSection_sum_stronglyMeasurable rate rewards C_star C_h
      control0 u t B0 hB0).indicator hcellField
  have hsetint : ∀ A : Set (SourceInput p), MeasurableSet[H (t.val + 1)] A →
      μ A < ⊤ →
      ∫ z in A, candidate z ∂μ =
        ∫ z in A, cell.indicator test z ∂μ := by
    intro A hA _
    simpa only [μ, H, cell, test, sectionSum, candidate] using
      (markedCurrent_cell_setIntegral rate rewards C_star C_h
        control0 u t B0 hB0 A hA).symm
  have hce := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (m := H (t.val + 1))
    (m₀ := (inferInstance : MeasurableSpace (SourceInput p))) (μ := μ)
    (f := cell.indicator test) (g := candidate)
    hfieldLe hleftInt (fun _ _ _ => hcandidateInt.integrableOn) hsetint
    hcandidateMeas.aestronglyMeasurable
  exact hce.symm

end Bandits.Support.ReferenceFirstCollectionMarkedCurrentConditionalLaw

end
