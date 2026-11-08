/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPastSamplerFibreLaw

import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Original-source joint transport at the first collection invocation

The source coordinate in this observation retains all future controls. The
strict prefix is only the existing analytical mark. All restrictions below
are unnormalized restrictions of the original source law.

Sources: `06_interruptions.tex:391-426` and
`appendix_b_communication.tex:25-58`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionOriginalSourceFibreTransport

open ReferenceFixedTimeSourceControlCoupling
  (replaceSourceControl fixedControlSplit fixedControlSourceStratum
    fixedControlRemainderLaw fixedControlRemainderStratum sourceCoordinatorIndex)
open ReferenceSourcePrefixHistoryFiltration (sourcePrefix)
open ReferenceCalendarCollectionCallControlLaw (firstCell)
open ReferenceCalendarLaterSamplerPredictability (calendarParameters)
open AssignmentParameterFibreKernel (fibreMass fibreMeasure successfulSlowSet)
open ReferenceLaterOptionalControlResampling (controlRemainderLaw)
open LaunchAssignmentCoordinateSplit (controlAssignmentSplitEquiv)
open ContinuousLearningRows (TimeControl timeControlLaw)
open BootstrapPrivateRoundStreams (sourceInputLaw)

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev Outcome (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.Outcome p
abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.AssignmentVector p
abbrev JointY (p : ConstructorDimensions.Parameters) :=
  SourceInput p × ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
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

/-- The original source jointly with the existing first-call marked output. -/
def originalSourceOutput (control0 : TimeControl p) (z : SourceInput p) : JointY p :=
  (z, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput
    rate rewards C_star C_h control0 z)

/-- A Borel indicator tested on the literal joint observation. -/
def originalSourceTest (control0 : TimeControl p) (B : Set (JointY p))
    (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (originalSourceOutput rate rewards C_star C_h control0 z)

/-- The fibre section retains the original source outside the replaced current
control. The absent-parameter zero is only an analytical off-cell value. -/
def originalSourceSection (control0 : TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B : Set (JointY p)) (z : SourceInput p) : ℝ :=
  match calendarParameters rate rewards C_star C_h t z with
  | none => 0
  | some theta => (fibreMass p theta a).toReal *
      ∫ vw, B.indicator (fun _ => (1 : ℝ))
        (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
          some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1)))))
        ∂(fibreMeasure p theta a).prod (controlRemainderLaw p)

private theorem indicator_bounds {Y : Type*} (B : Set Y) (y : Y) :
    0 ≤ B.indicator (fun _ => (1 : ℝ)) y ∧
      B.indicator (fun _ => (1 : ℝ)) y ≤ 1 := by
  by_cases hy : y ∈ B <;> simp [Set.indicator, hy]

private theorem bounded_integrable {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsFiniteMeasure μ] (f : Y → ℝ) (hf : Measurable f)
    (hb : ∀ y, ‖f y‖ ≤ 1) : Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall hb

private theorem integrable_test {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) μ := by
  apply bounded_integrable μ _ ((measurable_const.indicator hB).comp hf)
  intro x
  obtain ⟨h0, h1⟩ := indicator_bounds B (f x)
  simpa only [Function.comp_apply, Real.norm_of_nonneg h0] using h1

/-- Joint Borelness uses the original source identity map. -/
theorem originalSourceOutput_measurable (control0 : TimeControl p) :
    Measurable (originalSourceOutput rate rewards C_star C_h control0) :=
  measurable_id.prodMk
    (ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput_measurable
      rate rewards C_star C_h control0)

/-- Every Borel test of the joint observation is Borel. -/
theorem originalSourceTest_measurable (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Measurable (originalSourceTest rate rewards C_star C_h control0 B) :=
  (measurable_const.indicator hB).comp
    (originalSourceOutput_measurable rate rewards C_star C_h control0)

/-- Every joint indicator is integrable under the entire original source law. -/
theorem originalSourceTest_integrable (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (originalSourceTest rate rewards C_star C_h control0 B)
      (sourceInputLaw p) :=
  integrable_test _ _ (originalSourceOutput_measurable
    rate rewards C_star C_h control0) B hB

/-- Replacing the current control preserves the exact strict-past mark. -/
theorem sourcePrefix_replaceSourceControl (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : TimeControl p) :
    sourcePrefix control0 t.val (replaceSourceControl p t z c) =
      sourcePrefix control0 t.val z := by
  apply Prod.ext
  · refine Prod.ext rfl ?_
    funext q
    by_cases hq : q = ActualInitializationPhysicalStep.selectedRowIndex p z
    · subst q
      simp only [sourcePrefix, replaceSourceControl, sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex, Function.update_self]
      refine Prod.ext rfl ?_
      funext v
      by_cases hv : v.val < t.val
      · have hvt : v ≠ t := by intro h; subst v; exact (Nat.lt_irrefl _) hv
        simp only [hv, ite_true, Function.update_of_ne hvt]
      · simp only [hv, ite_false]
    · have hq' : q ≠ sourceCoordinatorIndex p z := hq
      simp only [sourcePrefix, replaceSourceControl, sourceCoordinatorIndex,
        ActualInitializationPhysicalStep.selectedRowIndex] at hq hq' ⊢
      rw [Function.update_of_ne hq, Function.update_of_ne hq, Function.update_of_ne hq]
  · rfl

private theorem cell_measurable (control0 : TimeControl p) (u t : Fin p.T) :
    MeasurableSet (firstCell rate rewards C_star C_h u t) :=
  ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
    (t.val + 1)) _
    (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t)

/-- Original cell membership is unchanged by an arbitrary current control. -/
theorem firstCell_replaceSourceControl_iff (control0 : TimeControl p)
    (u t : Fin p.T) (z : SourceInput p) (c : TimeControl p) :
    replaceSourceControl p t z c ∈ firstCell rate rewards C_star C_h u t ↔
      z ∈ firstCell rate rewards C_star C_h u t := by
  have hm := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
    MeasurableSpace.measurableSet_comap] at hm
  obtain ⟨D, _hD, hD⟩ := hm
  rw [← hD]
  change sourcePrefix control0 t.val (replaceSourceControl p t z c) ∈ D ↔ _
  rw [sourcePrefix_replaceSourceControl]
  rfl

/-- The actual moving parameter is unchanged, without replacing future data. -/
theorem calendarParameters_replaceSourceControl (control0 : TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : TimeControl p) :
    calendarParameters rate rewards C_star C_h t (replaceSourceControl p t z c) =
      calendarParameters rate rewards C_star C_h t z := by
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
    rate rewards C_star C_h control0 t (replaceSourceControl p t z c),
    sourcePrefix_replaceSourceControl,
    ← ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
      rate rewards C_star C_h control0 t z]

private theorem vector_replacement (t : Fin p.T) (z : SourceInput p)
    (c : TimeControl p) :
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
      (replaceSourceControl p t z c) = ContinuousControlSlice.assignmentVector c.1 := by
  simp [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
    ReferenceSourceCurrentControlFreshness.u_t, replaceSourceControl,
    sourceCoordinatorIndex, ActualInitializationPhysicalStep.selectedRowIndex]

private theorem fibre_probability (theta : AssignmentParameterFibreKernel.Theta p)
    (a : Outcome p) : IsProbabilityMeasure (fibreMeasure p theta a) := by
  change IsProbabilityMeasure (FiniteFibreLift.fibreMeasure
    (ContinuousControlSlice.assignmentLaw p.K) (successfulSlowSet p theta) a)
  infer_instance

private theorem fibre_observation_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) :
    Measurable (fun x : SourceInput p ×
        (AssignmentVector p × ReferenceLaterOptionalControlResampling.ControlRemainder p) =>
      (replaceSourceControl p t x.1 ((controlAssignmentSplitEquiv p).symm x.2),
        (some (u, (t, (sourcePrefix control0 t.val x.1, (some a, x.2.1)))) :
          ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p))) := by
  have hsource := (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
    p t).comp (measurable_fst.prodMk
      ((controlAssignmentSplitEquiv p).symm.measurable.comp measurable_snd))
  have hmark : Measurable (fun x : SourceInput p ×
      (AssignmentVector p × ReferenceLaterOptionalControlResampling.ControlRemainder p) =>
      sourcePrefix control0 t.val x.1) :=
    (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
      control0 t.val).comp measurable_fst
  exact hsource.prodMk
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_const.prodMk (measurable_const.prodMk
        (hmark.prodMk (measurable_const.prodMk measurable_snd.fst)))))

private theorem section_parameter_measurable (control0 : TimeControl p)
    (u t : Fin p.T) (a : Outcome p) (B : Set (JointY p)) (hB : MeasurableSet B) :
    Measurable (fun x : SourceInput p × AssignmentParameterFibreKernel.Theta p =>
      (fibreMass p x.2 a).toReal *
        ∫ vw, B.indicator (fun _ => (1 : ℝ))
          (replaceSourceControl p t x.1 ((controlAssignmentSplitEquiv p).symm vw),
            some (u, (t, (sourcePrefix control0 t.val x.1, (some a, vw.1)))))
          ∂(fibreMeasure p x.2 a).prod (controlRemainderLaw p)) := by
  let κ := ((AssignmentParameterFibreKernel.assignmentParameterFibreKernel p).comap
    (fun x : SourceInput p × AssignmentParameterFibreKernel.Theta p => (x.2, a))
    (measurable_snd.prodMk measurable_const)).prod
      (ProbabilityTheory.Kernel.const
        (SourceInput p × AssignmentParameterFibreKernel.Theta p) (controlRemainderLaw p))
  have hf : Measurable (fun x :
      (SourceInput p × AssignmentParameterFibreKernel.Theta p) ×
        (AssignmentVector p × ReferenceLaterOptionalControlResampling.ControlRemainder p) =>
      B.indicator (fun _ => (1 : ℝ))
        (replaceSourceControl p t x.1.1 ((controlAssignmentSplitEquiv p).symm x.2),
          some (u, (t, (sourcePrefix control0 t.val x.1.1, (some a, x.2.1)))))) :=
    (measurable_const.indicator hB).comp
      ((fibre_observation_measurable control0 u t a).comp
        (measurable_fst.fst.prodMk measurable_snd))
  have hi := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  have hmass : Measurable (fun x : SourceInput p × AssignmentParameterFibreKernel.Theta p =>
      (fibreMass p x.2 a).toReal) :=
    ((AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp
      (measurable_snd.prodMk measurable_const)).ennreal_toReal
  apply hmass.mul
  simpa only [κ, ProbabilityTheory.Kernel.prod_apply,
    ProbabilityTheory.Kernel.comap_apply, ProbabilityTheory.Kernel.const_apply,
    AssignmentParameterFibreKernel.assignmentParameterFibreKernel_apply] using hi.measurable

private theorem measurable_option_section {X Θ : Type*}
    [MeasurableSpace X] [MeasurableSpace Θ]
    (f : X × Θ → ℝ) (hf : Measurable f) :
    Measurable (fun y : Option Θ × X =>
      match y.1 with | none => 0 | some theta => f (y.2, theta)) := by
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv Θ X
  let decode : (Θ × X) ⊕ (PUnit × X) → ℝ :=
    Sum.elim (fun x => f (x.2, x.1)) (fun _ => 0)
  have hd : Measurable decode := measurable_fun_sum (hf.comp measurable_swap) measurable_const
  have heq : (fun y : Option Θ × X =>
      match y.1 with | none => 0 | some theta => f (y.2, theta)) =
      fun y => decode (e y) := by
    funext y
    rcases y with ⟨o, x⟩
    cases o <;> rfl
  rw [heq]
  exact hd.comp e.measurable

/-- Sections are Borel for the original source Borel structure. -/
theorem originalSourceSection_measurable (control0 : TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B : Set (JointY p)) (hB : MeasurableSet B) :
    Measurable (originalSourceSection rate rewards C_star C_h control0 u t a B) := by
  have htheta := (ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable
    rate rewards C_star C_h control0 t).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
        (t.val + 1)) le_rfl
  convert (measurable_option_section _
    (section_parameter_measurable control0 u t a B hB)).comp
      (htheta.prodMk measurable_id) using 1
  · rfl
  · funext z
    cases ht : calendarParameters rate rewards C_star C_h t z <;>
      simp only [originalSourceSection, Function.comp_apply, id_eq, ht]

/-- The section is nonnegative and at most one, including every zero fibre. -/
theorem originalSourceSection_bounds (control0 : TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B : Set (JointY p)) (hB : MeasurableSet B) (z : SourceInput p) :
    0 ≤ originalSourceSection rate rewards C_star C_h control0 u t a B z ∧
      originalSourceSection rate rewards C_star C_h control0 u t a B z ≤ 1 := by
  cases ht : calendarParameters rate rewards C_star C_h t z with
  | none => simp [originalSourceSection, ht]
  | some theta =>
      have := fibre_probability theta a
      let f := fun vw : AssignmentVector p ×
          ReferenceLaterOptionalControlResampling.ControlRemainder p =>
        B.indicator (fun _ => (1 : ℝ))
          (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
            some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1)))))
      have hi : Integrable f ((fibreMeasure p theta a).prod (controlRemainderLaw p)) :=
        integrable_test _ _
          ((fibre_observation_measurable control0 u t a).comp measurable_prodMk_left) B hB
      have h0 : 0 ≤ ∫ vw, f vw ∂(fibreMeasure p theta a).prod (controlRemainderLaw p) :=
        integral_nonneg fun vw => (indicator_bounds B _).1
      have h1 : (∫ vw, f vw ∂(fibreMeasure p theta a).prod (controlRemainderLaw p)) ≤ 1 := by
        calc
          _ ≤ ∫ _ : AssignmentVector p ×
              ReferenceLaterOptionalControlResampling.ControlRemainder p,
              (1 : ℝ) ∂(fibreMeasure p theta a).prod (controlRemainderLaw p) :=
            integral_mono hi (integrable_const 1) fun vw => (indicator_bounds B _).2
          _ = 1 := by simp
      have hmass : (fibreMass p theta a).toReal ≤ 1 := by
        have hle : fibreMass p theta a ≤ 1 := by
          rw [← AssignmentParameterFibreKernel.sum_fibreMass_eq_one p theta]
          exact Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ a)
        exact (ENNReal.toReal_le_toReal (ne_of_lt (hle.trans_lt ENNReal.one_lt_top))
          ENNReal.one_ne_top).mpr hle
      simp only [originalSourceSection, ht]
      change 0 ≤ (fibreMass p theta a).toReal * _ ∧
        (fibreMass p theta a).toReal * _ ≤ 1
      exact ⟨mul_nonneg ENNReal.toReal_nonneg h0,
        (mul_le_of_le_one_right ENNReal.toReal_nonneg h1).trans hmass⟩

/-- Every moving section is integrable, hence also on each original cell. -/
theorem originalSourceSection_integrable (control0 : TimeControl p) (u t : Fin p.T)
    (a : Outcome p) (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (originalSourceSection rate rewards C_star C_h control0 u t a B)
      (sourceInputLaw p) := by
  apply bounded_integrable _ _
    (originalSourceSection_measurable rate rewards C_star C_h control0 u t a B hB)
  intro z
  obtain ⟨h0, h1⟩ := originalSourceSection_bounds
    rate rewards C_star C_h control0 u t a B hB z
  simpa only [Real.norm_of_nonneg h0] using h1

private theorem source_partition_integral (f : SourceInput p → ℝ)
    (hf : Integrable f (sourceInputLaw p)) :
    (∫ z, f z ∂sourceInputLaw p) =
      ∑ q : Fin (ConstructorDimensions.M p),
        ∫ z in fixedControlSourceStratum p q, f z ∂sourceInputLaw p := by
  have hindex : Measurable (sourceCoordinatorIndex p) :=
    (PrivateSourceStreams.measurable_coordinatorIndex p).comp
      (measurable_snd.comp (measurable_fst.comp measurable_snd))
  have hp : (∑ q : Fin (ConstructorDimensions.M p),
      (sourceInputLaw p).restrict (fixedControlSourceStratum p q)) = sourceInputLaw p :=
    FiniteFibreLift.sum_restrict_fibre (sourceInputLaw p) (sourceCoordinatorIndex p) hindex
  conv_lhs => rw [← hp]
  exact integral_finsetSum_measure (fun _ _ => hf.integrableOn)

private theorem resampling_integral (t : Fin p.T) (f : SourceInput p → ℝ)
    (hf : Measurable f) (hb : ∀ z, ‖f z‖ ≤ 1) :
    (∫ z, f z ∂sourceInputLaw p) =
      ∫ z, ∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p
        ∂sourceInputLaw p := by
  let g : SourceInput p → ℝ := fun z =>
    ∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p
  have hg : Measurable g :=
    (hf.comp (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl
      p t)).stronglyMeasurable.integral_prod_right'.measurable
  have hgb : ∀ z, ‖g z‖ ≤ 1 := by
    intro z
    simpa only [probReal_univ, mul_one] using
      (norm_integral_le_of_norm_le_const
        (μ := timeControlLaw p) (Filter.Eventually.of_forall fun c => hb
          (replaceSourceControl p t z c)))
  have hfi := bounded_integrable (sourceInputLaw p) f hf hb
  have hgi := bounded_integrable (sourceInputLaw p) g hg hgb
  rw [source_partition_integral f hfi, source_partition_integral g hgi]
  apply Finset.sum_congr rfl
  intro q _
  let e := fixedControlSplit p q t
  let η := (fixedControlRemainderLaw p q t).restrict (fixedControlRemainderStratum p q t)
  have hmap : ((timeControlLaw p).prod η).map e.symm =
      (sourceInputLaw p).restrict (fixedControlSourceStratum p q) :=
    ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_privateStratum_map_symm p q t
  have hint (h : SourceInput p → ℝ) (hh : Measurable h) :
      (∫ z in fixedControlSourceStratum p q, h z ∂sourceInputLaw p) =
        ∫ x, h (e.symm x) ∂(timeControlLaw p).prod η := by
    rw [← hmap]
    exact integral_map_of_stronglyMeasurable e.symm.measurable hh.stronglyMeasurable
  have hfe : Integrable (fun x => f (e.symm x)) ((timeControlLaw p).prod η) :=
    bounded_integrable _ _ (hf.comp e.symm.measurable) (fun x => hb (e.symm x))
  have hge : Integrable (fun x => g (e.symm x)) ((timeControlLaw p).prod η) :=
    bounded_integrable _ _ (hg.comp e.symm.measurable) (fun x => hgb (e.symm x))
  have hrepl (r : ReferenceFixedTimeSourceControlCoupling.FixedControlRemainder p q t)
      (hr : r ∈ fixedControlRemainderStratum p q t) (c d : TimeControl p) :
      replaceSourceControl p t (e.symm (c, r)) d = e.symm (d, r) := by
    have hq : sourceCoordinatorIndex p (e.symm (c, r)) = q := by
      change PrivateSourceStreams.coordinatorIndex p (e.symm (c, r)).2.1.2 = q
      rw [ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_symm_private]
      exact hr
    have he := ReferenceFixedTimeSourceControlCoupling.fixedControlSplit_replaceSourceControl
      p q t (e.symm (c, r)) d hq
    change e.symm (d, (e (e.symm (c, r))).2) = _ at he
    rw [e.apply_symm_apply] at he
    exact he.symm
  rw [hint f hf, hint g hg, integral_prod_symm _ hfe, integral_prod_symm _ hge]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    (ReferenceFixedTimeSourceControlCoupling.measurableSet_fixedControlRemainderStratum
      p q t)] with r hr
  have heq : (fun c : TimeControl p => g (e.symm (c, r))) =
      fun _ => ∫ d, f (e.symm (d, r)) ∂timeControlLaw p := by
    funext c
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun d => congrArg f (hrepl r hr c d)
  rw [heq]
  simp only [integral_const, probReal_univ, one_smul]

private theorem split_assignmentVector (vw : AssignmentVector p ×
    ReferenceLaterOptionalControlResampling.ControlRemainder p) :
    ContinuousControlSlice.assignmentVector ((controlAssignmentSplitEquiv p).symm vw).1 =
      vw.1 := by
  have hfirst (c : TimeControl p) :
      (controlAssignmentSplitEquiv p c).1 =
        ContinuousControlSlice.assignmentVector c.1 := by
    funext r
    rfl
  rw [← hfirst, (controlAssignmentSplitEquiv p).apply_symm_apply]

private theorem joint_fibre_graph_integral (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (theta : AssignmentParameterFibreKernel.Theta p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ vw, B.indicator (fun _ => (1 : ℝ))
      (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
        some (u, (t, (sourcePrefix control0 t.val z,
          (some (successfulSlowSet p theta vw.1), vw.1)))))
      ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)) =
      ∑ a : Outcome p, (fibreMass p theta a).toReal *
        ∫ vw, B.indicator (fun _ => (1 : ℝ))
          (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
            some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1)))))
          ∂(fibreMeasure p theta a).prod (controlRemainderLaw p) := by
  let F := successfulSlowSet p theta
  let ν := (ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)
  let g := fun vw : AssignmentVector p ×
      ReferenceLaterOptionalControlResampling.ControlRemainder p =>
    B.indicator (fun _ => (1 : ℝ))
      (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
        some (u, (t, (sourcePrefix control0 t.val z, (some (F vw.1), vw.1)))))
  have hF : Measurable F :=
    (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
      measurable_prodMk_left
  have hobs : Measurable (fun vw : AssignmentVector p ×
      ReferenceLaterOptionalControlResampling.ControlRemainder p =>
      (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
        (some (u, (t, (sourcePrefix control0 t.val z, (some (F vw.1), vw.1)))) :
          ReferenceFirstCollectionPastSamplerFibreLaw.PastFibreY p))) := by
    have hs : Measurable (fun vw : AssignmentVector p ×
        ReferenceLaterOptionalControlResampling.ControlRemainder p =>
        replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw)) :=
      (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
        (measurable_const.prodMk (controlAssignmentSplitEquiv p).symm.measurable)
    exact hs.prodMk
      (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
        (measurable_const.prodMk (measurable_const.prodMk
          (measurable_const.prodMk
            ((LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
              (hF.comp measurable_fst)).prodMk measurable_fst)))))
  have hg : Integrable g ν := integrable_test ν _ hobs B hB
  have hrect (a : Outcome p) :
      FiniteFibreLift.fibre (fun vw : AssignmentVector p ×
          ReferenceLaterOptionalControlResampling.ControlRemainder p => F vw.1) a =
        FiniteFibreLift.fibre F a ×ˢ Set.univ := by
    ext vw
    simp only [FiniteFibreLift.fibre, Set.mem_prod, Set.mem_univ, and_true]
    rfl
  have hrestrict (a : Outcome p) :
      ν.restrict (FiniteFibreLift.fibre (fun vw => F vw.1) a) =
        (fibreMass p theta a • fibreMeasure p theta a).prod (controlRemainderLaw p) := by
    rw [AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure, hrect]
    exact (Measure.prod_restrict _ Set.univ).symm.trans (by rw [Measure.restrict_univ])
  have hp : (∑ a : Outcome p,
      ν.restrict (FiniteFibreLift.fibre (fun vw => F vw.1) a)) = ν := by
    simp_rw [hrestrict]
    rw [← Measure.sum_fintype, ← Measure.prod_sum_left, Measure.sum_fintype,
      AssignmentParameterFibreKernel.sum_fibreMass_smul_fibreMeasure]
  calc
    _ = ∫ vw, g vw ∂∑ a : Outcome p,
        ν.restrict (FiniteFibreLift.fibre (fun vw => F vw.1) a) := by rw [hp]
    _ = ∑ a : Outcome p, ∫ vw in FiniteFibreLift.fibre (fun vw => F vw.1) a,
        g vw ∂ν := integral_finsetSum_measure (fun _ _ => hg.integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have heq : (∫ vw in FiniteFibreLift.fibre (fun vw => F vw.1) a, g vw ∂ν) =
          ∫ vw in FiniteFibreLift.fibre (fun vw => F vw.1) a,
            B.indicator (fun _ => (1 : ℝ))
              (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
                some (u, (t, (sourcePrefix control0 t.val z, (some a, vw.1))))) ∂ν := by
        apply setIntegral_congr_fun
          (FiniteFibreLift.measurableSet_fibre _ a (hF.comp measurable_fst))
        intro vw hv
        change F vw.1 = a at hv
        simp only [g, hv]
      rw [heq, hrestrict, Measure.prod_smul_left, integral_smul_measure, smul_eq_mul]

private theorem pastFibreOutput_on_cell (control0 : TimeControl p) (u t : Fin p.T)
    (z : SourceInput p) (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput
        rate rewards C_star C_h control0 z =
      some (u, (t, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair
        rate rewards C_star C_h control0 t z)) := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have htag := (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
        rate rewards C_star C_h u t z).mp hz
      simp only [hcall, Option.map_none, reduceCtorEq] at htag
  | some c =>
      have htag := (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
        rate rewards C_star C_h u t z).mp hz
      simp only [hcall, Option.map_some, Option.some.injEq, Prod.mk.injEq] at htag
      simp only [ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput, hcall,
        Option.map_some, ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair,
        htag.1, htag.2]

/-- On an actual first-call cell, whole-control resampling produces the joint
source/vector/remainder fibre section. The sampler witnesses are local. -/
theorem resampledTest_eq_fibreSum_on_cell (control0 : TimeControl p)
    (u t : Fin p.T) (B : Set (JointY p)) (hB : MeasurableSet B) (z : SourceInput p)
    (hz : z ∈ firstCell rate rewards C_star C_h u t) :
    (∫ c, originalSourceTest rate rewards C_star C_h control0 B
      (replaceSourceControl p t z c) ∂timeControlLaw p) =
      ∑ a : Outcome p, originalSourceSection rate rewards C_star C_h control0 u t a B z := by
  obtain ⟨theta, _o, htheta, _ho, _hs, _hv, _hc, _ha⟩ :=
    ReferenceFirstCollectionSamplerFibreLaw.firstCell_actualSamplerTrace
      rate rewards C_star C_h u t z hz
  have hcell (c : TimeControl p) :
      replaceSourceControl p t z c ∈ firstCell rate rewards C_star C_h u t :=
    (firstCell_replaceSourceControl_iff rate rewards C_star C_h control0 u t z c).mpr hz
  have hactive (c : TimeControl p) :
      ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h t
        (replaceSourceControl p t z c) =
      some (successfulSlowSet p theta (ContinuousControlSlice.assignmentVector c.1)) := by
    obtain ⟨theta', _o', htheta', _ho', _hs', _hv', _hc', ha'⟩ :=
      ReferenceFirstCollectionSamplerFibreLaw.firstCell_actualSamplerTrace
        rate rewards C_star C_h u t (replaceSourceControl p t z c) (hcell c)
    have heq : theta' = theta := Option.some.inj
      (htheta'.symm.trans
        ((calendarParameters_replaceSourceControl rate rewards C_star C_h
          control0 t z c).trans htheta))
    rw [heq, vector_replacement] at ha'
    exact ha'
  have htest (c : TimeControl p) :
      originalSourceTest rate rewards C_star C_h control0 B (replaceSourceControl p t z c) =
        B.indicator (fun _ => (1 : ℝ))
          (replaceSourceControl p t z c,
            some (u, (t, (sourcePrefix control0 t.val z,
              (some (successfulSlowSet p theta
                (ContinuousControlSlice.assignmentVector c.1)),
                ContinuousControlSlice.assignmentVector c.1))))) := by
    unfold originalSourceTest originalSourceOutput
    rw [pastFibreOutput_on_cell rate rewards C_star C_h control0 u t _ (hcell c)]
    simp only [ReferenceFirstCollectionPastSamplerFibreLaw.pastFibrePair,
      sourcePrefix_replaceSourceControl, hactive, vector_replacement]
  have hsplit : ((ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p)).map
      (controlAssignmentSplitEquiv p).symm = timeControlLaw p :=
    (LaunchAssignmentCoordinateSplit.measurePreserving_controlAssignmentSplitEquiv p).symm.map_eq
  have hg : StronglyMeasurable (fun c : TimeControl p =>
      originalSourceTest rate rewards C_star C_h control0 B
        (replaceSourceControl p t z c)) :=
    ((originalSourceTest_measurable rate rewards C_star C_h control0 B hB).comp
      ((ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
        measurable_prodMk_left)).stronglyMeasurable
  calc
    _ = ∫ vw, originalSourceTest rate rewards C_star C_h control0 B
        (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw))
        ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p) := by
      conv_lhs => rw [← hsplit]
      exact integral_map_of_stronglyMeasurable (controlAssignmentSplitEquiv p).symm.measurable hg
    _ = ∫ vw, B.indicator (fun _ => (1 : ℝ))
        (replaceSourceControl p t z ((controlAssignmentSplitEquiv p).symm vw),
          some (u, (t, (sourcePrefix control0 t.val z,
            (some (successfulSlowSet p theta vw.1), vw.1)))))
        ∂(ContinuousControlSlice.assignmentLaw p.K).prod (controlRemainderLaw p) := by
      apply integral_congr_ae
      filter_upwards [] with vw
      rw [htest, split_assignmentVector]
    _ = _ := by
      rw [joint_fibre_graph_integral control0 u t z theta B hB]
      apply Finset.sum_congr rfl
      intro a _
      simp only [originalSourceSection, htheta]

/-- The same single-cell identity, testing the original source jointly with
its actual marked first-call output. Every optional outcome is summed. -/
theorem originalSource_cell_integral (control0 : TimeControl p) (u t : Fin p.T)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z in firstCell rate rewards C_star C_h u t,
      originalSourceTest rate rewards C_star C_h control0 B z ∂sourceInputLaw p) =
      ∑ a : Outcome p, ∫ z in firstCell rate rewards C_star C_h u t,
        originalSourceSection rate rewards C_star C_h control0 u t a B z
          ∂sourceInputLaw p := by
  let E := firstCell rate rewards C_star C_h u t
  let f := E.indicator (originalSourceTest rate rewards C_star C_h control0 B)
  have hE : MeasurableSet E := cell_measurable rate rewards C_star C_h control0 u t
  have hf : Measurable f :=
    (originalSourceTest_measurable rate rewards C_star C_h control0 B hB).indicator hE
  have hb : ∀ z, ‖f z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ E
    · simp only [f, Set.indicator_of_mem hz]
      obtain ⟨h0, h1⟩ := indicator_bounds B
        (originalSourceOutput rate rewards C_star C_h control0 z)
      exact (Real.norm_of_nonneg h0).le.trans h1
    · simp only [f, Set.indicator_of_notMem hz, norm_zero, zero_le_one]
  have hpoint (z : SourceInput p) :
      (∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p) =
        E.indicator (fun y => ∑ a : Outcome p,
          originalSourceSection rate rewards C_star C_h control0 u t a B y) z := by
    by_cases hz : z ∈ E
    · have hc (c : TimeControl p) : replaceSourceControl p t z c ∈ E :=
        (firstCell_replaceSourceControl_iff rate rewards C_star C_h control0 u t z c).mpr hz
      simp only [f, Set.indicator_of_mem (hc _), Set.indicator_of_mem hz]
      exact resampledTest_eq_fibreSum_on_cell
        rate rewards C_star C_h control0 u t B hB z hz
    · have hc (c : TimeControl p) : replaceSourceControl p t z c ∉ E :=
        fun h => hz ((firstCell_replaceSourceControl_iff
          rate rewards C_star C_h control0 u t z c).mp h)
      simp only [f, Set.indicator_of_notMem (hc _), Set.indicator_of_notMem hz, integral_zero]
  calc
    _ = ∫ z, f z ∂sourceInputLaw p := (integral_indicator hE).symm
    _ = ∫ z, ∫ c, f (replaceSourceControl p t z c) ∂timeControlLaw p
        ∂sourceInputLaw p := resampling_integral t f hf hb
    _ = ∫ z, E.indicator (fun y => ∑ a : Outcome p,
        originalSourceSection rate rewards C_star C_h control0 u t a B y) z
        ∂sourceInputLaw p := integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∫ z in E, (∑ a : Outcome p,
        originalSourceSection rate rewards C_star C_h control0 u t a B z)
        ∂sourceInputLaw p := integral_indicator hE
    _ = _ := integral_finsetSum Finset.univ fun a _ =>
      (originalSourceSection_integrable rate rewards C_star C_h control0 u t a B hB).integrableOn

private theorem originalSource_indicator_partition (control0 : TimeControl p)
    (B : Set (JointY p)) (z : SourceInput p) :
    originalSourceTest rate rewards C_star C_h control0 B z =
      (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
        rate rewards C_star C_h).indicator
          (fun y => B.indicator (fun _ => (1 : ℝ)) (y, none)) z +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        (firstCell rate rewards C_star C_h u t).indicator
          (originalSourceTest rate rewards C_star C_h control0 B) z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hnone : z ∈ ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h := hcall
      have hcell (u t : Fin p.T) : z ∉ firstCell rate rewards C_star C_h u t := by
        intro hz
        have htag := (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
          rate rewards C_star C_h u t z).mp hz
        simp only [hcall, Option.map_none, reduceCtorEq] at htag
      simp only [Set.indicator_of_mem hnone, Set.indicator_of_notMem (hcell _ _),
        Finset.sum_const_zero, add_zero, originalSourceTest, originalSourceOutput,
        ReferenceFirstCollectionPastSamplerFibreLaw.pastFibreOutput, hcall, Option.map_none]
  | some c =>
      have hnone : z ∉ ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h := by
        intro hz
        change ReferenceFirstCollectionSamplerCall.firstCollectionCall
          rate rewards C_star C_h z = none at hz
        rw [hcall] at hz
        cases hz
      have hcell (u t : Fin p.T) : z ∈ firstCell rate rewards C_star C_h u t ↔
          c.1 = u ∧ c.2.1 = t := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags, hcall]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      simp only [Set.indicator_of_notMem hnone, zero_add]
      simp only [Set.indicator, hcell, ite_and]
      simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Finset.sum_const_zero]

/-- The source-dependent no-call test is integrable before restriction. -/
theorem originalSource_noCallTest_integrable (B : Set (JointY p)) (hB : MeasurableSet B) :
    Integrable (fun z : SourceInput p => B.indicator (fun _ => (1 : ℝ)) (z, none))
      (sourceInputLaw p) :=
  integrable_test _ _ (measurable_id.prodMk measurable_const) B hB

/-- Arbitrary Borel tests of the original source and existing marked first-call
observation. Absence is the actual restricted integral, and all fibres remain. -/
theorem originalSourceOutput_borel_test_law (control0 : TimeControl p)
    (B : Set (JointY p)) (hB : MeasurableSet B) :
    (∫ z, B.indicator (fun _ => (1 : ℝ))
      (originalSourceOutput rate rewards C_star C_h control0 z) ∂sourceInputLaw p) =
      (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h,
        B.indicator (fun _ => (1 : ℝ)) (z, none) ∂sourceInputLaw p) +
      ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
        ∫ z in firstCell rate rewards C_star C_h u t,
          originalSourceSection rate rewards C_star C_h control0 u t a B z
            ∂sourceInputLaw p := by
  let noneTerm : SourceInput p → ℝ :=
    (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
      rate rewards C_star C_h).indicator
        (fun z => B.indicator (fun _ => (1 : ℝ)) (z, none))
  let cellTerm (u t : Fin p.T) : SourceInput p → ℝ :=
    (firstCell rate rewards C_star C_h u t).indicator
      (originalSourceTest rate rewards C_star C_h control0 B)
  have hnoneMeas := ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent_measurable
    rate rewards C_star C_h
  have hnoneInt : Integrable noneTerm (sourceInputLaw p) :=
    (originalSource_noCallTest_integrable B hB).indicator hnoneMeas
  have hcellInt (u t : Fin p.T) : Integrable (cellTerm u t) (sourceInputLaw p) :=
    (originalSourceTest_integrable rate rewards C_star C_h control0 B hB).indicator
      (cell_measurable rate rewards C_star C_h control0 u t)
  have hsumInt : Integrable (fun z =>
      ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) (sourceInputLaw p) := by
    apply integrable_finsetSum
    intro u _
    apply integrable_finsetSum
    intro t _
    exact hcellInt u t
  calc
    _ = ∫ z, noneTerm z + (∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z)
        ∂sourceInputLaw p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (originalSource_indicator_partition rate rewards C_star C_h control0 B)
    _ = (∫ z, noneTerm z ∂sourceInputLaw p) +
        ∫ z, (∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) ∂sourceInputLaw p :=
      integral_add' hnoneInt hsumInt
    _ = (∫ z in ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h,
        B.indicator (fun _ => (1 : ℝ)) (z, none) ∂sourceInputLaw p) +
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z, cellTerm u t z ∂sourceInputLaw p := by
      rw [show (∫ z, noneTerm z ∂sourceInputLaw p) = _ from integral_indicator hnoneMeas]
      congr 1
      rw [integral_finsetSum Finset.univ (fun u _ =>
        integrable_finsetSum Finset.univ (fun t _ => hcellInt u t))]
      apply Finset.sum_congr rfl
      intro u _
      exact integral_finsetSum Finset.univ (fun t _ => hcellInt u t)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro t _
      change (∫ z, (firstCell rate rewards C_star C_h u t).indicator
        (originalSourceTest rate rewards C_star C_h control0 B) z ∂sourceInputLaw p) = _
      rw [integral_indicator (cell_measurable rate rewards C_star C_h control0 u t)]
      exact originalSource_cell_integral rate rewards C_star C_h control0 u t B hB

end Bandits.Support.ReferenceFirstCollectionOriginalSourceFibreTransport

end
