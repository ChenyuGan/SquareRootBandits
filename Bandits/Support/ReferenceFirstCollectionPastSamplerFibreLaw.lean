/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPastPhysicalLaw
public import Bandits.Support.ReferenceFirstCollectionSamplerFibreLaw

import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Strict-past marked finite-fibre law of the original first invocation

The retained source prefix is an analysis mark. All dates, optional checked
outcomes, complete assignment vectors, and unnormalized original cells are
those of the existing physical execution. This is an internal physical law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical ENNReal BigOperators

namespace Bandits.Support.ReferenceFirstCollectionPastSamplerFibreLaw

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p
abbrev Outcome (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.Outcome p
abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  AssignmentParameterFibreKernel.AssignmentVector p
abbrev MarkedPayload (p : ConstructorDimensions.Parameters) :=
  SourceInput p × (Option (Outcome p) × AssignmentVector p)
abbrev PastFibreY (p : ConstructorDimensions.Parameters) :=
  Option (Fin p.T × (Fin p.T × MarkedPayload p))

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

/-- Map the same original first call, adding only its strict-past source mark. -/
def pastFibreOutput (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) : PastFibreY p :=
  (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z).map
    (fun c => (c.1, (c.2.1,
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 c.2.1.val z,
        (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
          rate rewards C_star C_h c.2.1 z,
          ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector c.2.1 z)))))

/-- The literal marked outcome and entire current assignment vector. -/
def pastFibrePair (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) : MarkedPayload p :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
    (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
      rate rewards C_star C_h t z,
      ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z))

/-- A Borel observation tested at the actual marked pair. -/
def pastFibreTest (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (B0 : Set (MarkedPayload p)) (z : SourceInput p) : ℝ :=
  B0.indicator (fun _ => (1 : ℝ))
    (pastFibrePair rate rewards C_star C_h control0 t z)

/-- The slice at the unchanged original cutoff and invocation dates. -/
def stratumSet (B : Set (PastFibreY p)) (u t : Fin p.T) : Set (MarkedPayload p) :=
  {y | some (u, (t, y)) ∈ B}

/-- The moving Borel fibre section, including the genuine absent-parameter
branch. Its conditional-law use is restricted to the original first cell. -/
def pastFibreSection (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : Outcome p) (B0 : Set (MarkedPayload p))
    (z : SourceInput p) : ℝ :=
  match ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
  | none => 0
  | some theta => (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
      ∫ v, B0.indicator (fun _ => (1 : ℝ))
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
          (some a, v)) ∂AssignmentParameterFibreKernel.fibreMeasure p theta a

private theorem integrable_test {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_const.indicator hB).comp hf).aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : f x ∈ B <;> simp [Set.indicator, hx]

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
  rw [heq]
  have hlift : Measurable (Sum.elim f (fun _ : PUnit => (none : Option Z))) := by
    apply measurable_fun_sum
    · exact hf
    · exact measurable_const
  exact hlift.comp (e.measurable.comp hinput)

private theorem activeOutcomeAt_measurable (t : Fin p.T) :
    Measurable (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
      rate rewards C_star C_h t) := by
  let codeSlow : LaterAssignmentStartMeasurability.LaterAssignmentStartCode p → Outcome p :=
    fun code => match code with
    | .sampled outcome => CheckedAssignmentSample.successfulSlowSet p (.sampled outcome)
    | _ => none
  have hcode : Measurable codeSlow := Measurable.of_discrete
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv
    (AssignmentParameterFibreKernel.Theta p)
    (LaterAssignmentStartMeasurability.LaterAssignmentStartCode p)
  let decode := Sum.elim
    (fun q : AssignmentParameterFibreKernel.Theta p ×
      LaterAssignmentStartMeasurability.LaterAssignmentStartCode p => some (codeSlow q.2))
    (fun _ : PUnit × LaterAssignmentStartMeasurability.LaterAssignmentStartCode p =>
      (none : Option (Outcome p)))
  have hdecode : Measurable decode := measurable_fun_sum
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (hcode.comp measurable_snd)) measurable_const
  have hselected : Measurable
      (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
        o.2.1.map fun _ => codeSlow o.1) := by
    have heq : (fun o : LaterAssignmentFullOutputMeasurability.FullOutputObservation p =>
        o.2.1.map fun _ => codeSlow o.1) = fun o => decode (e (o.2.1, o.1)) := by
      funext o
      cases o.2.1 <;> rfl
    rw [heq]
    exact hdecode.comp (e.measurable.comp
      ((measurable_fst.comp measurable_snd).prodMk measurable_fst))
  exact measurable_optionBind _
    (ReferenceCalendarLaterSamplerOutputSections.measurable_outputAt
      rate rewards C_star C_h t) _ hselected

/-- Borelness of the literal pair, without discarding the absent sampler. -/
theorem pastFibrePair_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) :
    Measurable (pastFibrePair rate rewards C_star C_h control0 t) := by
  exact (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val).prodMk
    ((activeOutcomeAt_measurable rate rewards C_star C_h t).prodMk
      (measurable_snd.comp
        (ReferenceFirstCollectionSamplerOutputLaw.firstOutputPair_measurable
          rate rewards C_star C_h t)))

/-- All original tag slices of a Borel test are Borel. -/
theorem stratumSet_measurable (B : Set (PastFibreY p)) (hB : MeasurableSet B)
    (u t : Fin p.T) : MeasurableSet (stratumSet B u t) := by
  exact hB.preimage
    (LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _
      (measurable_const.prodMk (measurable_const.prodMk measurable_id)))

/-- The outer absence is precisely absence of the original invocation. -/
theorem pastFibreOutput_eq_none_iff_original_call_eq_none
    (control0 : ContinuousLearningRows.TimeControl p) (z : SourceInput p) :
    pastFibreOutput rate rewards C_star C_h control0 z = none ↔
      ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z = none := by
  cases h : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;> simp [pastFibreOutput, h]

/-- Erase only the source mark, retaining all original optional outcomes. -/
theorem pastFibreOutput_erasePast_eq
    (control0 : ContinuousLearningRows.TimeControl p) (z : SourceInput p) :
    (pastFibreOutput rate rewards C_star C_h control0 z).map
      (fun c => (c.1, (c.2.1, c.2.2.2))) =
      ReferenceFirstCollectionSamplerFibreLaw.firstFibreOutput
        rate rewards C_star C_h z := by
  cases h : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;>
    simp [pastFibreOutput, ReferenceFirstCollectionSamplerFibreLaw.firstFibreOutput, h]

private theorem cell_measurable (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) : MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) :=
  ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
    (t.val + 1)) _
    (ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t)

/-- The actual observation's preimage is the original no-call/cell partition. -/
theorem pastFibreOutput_preimage_eq (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PastFibreY p)) :
    pastFibreOutput rate rewards C_star C_h control0 ⁻¹' B =
      (if none ∈ B then ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
        rate rewards C_star C_h else ∅) ∪
      ⋃ u : Fin p.T, ⋃ t : Fin p.T,
        ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ∩
          (pastFibrePair rate rewards C_star C_h control0 t ⁻¹' stratumSet B u t) := by
  ext z
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hcellnone (u t : Fin p.T) : z ∉
          ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
        intro hz
        have htag := (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
          rate rewards C_star C_h u t z).mp hz
        simp [hcall] at htag
      simp [pastFibreOutput, stratumSet,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent, hcall, hcellnone]
  | some c =>
      have hcelltags (u t : Fin p.T) : z ∈
          ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t ↔
          (c.1, c.2.1) = (u, t) := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags, hcall]
        simp
      simp [pastFibreOutput, stratumSet, pastFibrePair,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent, hcall, hcelltags]

/-- Borelness of the same original first-call observer with its source mark. -/
theorem pastFibreOutput_measurable (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (pastFibreOutput rate rewards C_star C_h control0) := by
  intro B hB
  rw [pastFibreOutput_preimage_eq rate rewards C_star C_h control0 B]
  apply MeasurableSet.union
  · split_ifs
    · exact ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent_measurable
        rate rewards C_star C_h
    · exact MeasurableSet.empty
  · exact MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun t =>
      (cell_measurable rate rewards C_star C_h control0 u t).inter
        ((pastFibrePair_measurable rate rewards C_star C_h control0 t)
          (stratumSet_measurable B hB u t))

private theorem fibre_probability (theta : AssignmentParameterFibreKernel.Theta p)
    (a : Outcome p) : IsProbabilityMeasure
      (AssignmentParameterFibreKernel.fibreMeasure p theta a) := by
  change IsProbabilityMeasure (FiniteFibreLift.fibreMeasure
    (ContinuousControlSlice.assignmentLaw p.K)
    (AssignmentParameterFibreKernel.successfulSlowSet p theta) a)
  infer_instance

private theorem section_parameter_measurable (a : Outcome p)
    (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0) :
    Measurable (fun x : SourceInput p × AssignmentParameterFibreKernel.Theta p =>
      (AssignmentParameterFibreKernel.fibreMass p x.2 a).toReal *
        ∫ v, B0.indicator (fun _ => (1 : ℝ)) (x.1, (some a, v))
          ∂AssignmentParameterFibreKernel.fibreMeasure p x.2 a) := by
  let κ : ProbabilityTheory.Kernel
      (SourceInput p × AssignmentParameterFibreKernel.Theta p) (AssignmentVector p) :=
    (AssignmentParameterFibreKernel.assignmentParameterFibreKernel p).comap
    (fun x : SourceInput p × AssignmentParameterFibreKernel.Theta p => (x.2, a))
    (measurable_snd.prodMk measurable_const)
  have hf : Measurable
      (fun x : (SourceInput p × AssignmentParameterFibreKernel.Theta p) ×
        AssignmentVector p => B0.indicator (fun _ => (1 : ℝ))
          (x.1.1, (some a, x.2))) :=
    (measurable_const.indicator hB0).comp
      (measurable_fst.fst.prodMk (measurable_const.prodMk measurable_snd))
  have hi := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)
  exact ((AssignmentParameterFibreKernel.measurable_fibreMass_joint p).comp
    (measurable_snd.prodMk measurable_const)).ennreal_toReal.mul hi.measurable

private theorem measurable_option_section {X Θ : Type*}
    [MeasurableSpace X] [MeasurableSpace Θ]
    (f : X × Θ → ℝ) (hf : Measurable f) :
    Measurable (fun y : Option Θ × X =>
      match y.1 with | none => 0 | some theta => f (y.2, theta)) := by
  let e := ReferenceCollectionDispatchMeasurability.optionPairEquiv Θ X
  let decode : (Θ × X) ⊕ (PUnit × X) → ℝ :=
    Sum.elim (fun x => f (x.2, x.1)) (fun _ => 0)
  have hd : Measurable decode := by
    apply measurable_fun_sum
    · exact hf.comp measurable_swap
    · exact measurable_const
  have heq : (fun y : Option Θ × X =>
      match y.1 with | none => 0 | some theta => f (y.2, theta)) =
      fun y => decode (e y) := by
    funext y
    rcases y with ⟨o, x⟩
    cases o <;> rfl
  rw [heq]
  exact hd.comp e.measurable

/-- Every moving section is strongly measurable in the exact strict-past field. -/
theorem pastFibreSection_stronglyMeasurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : Outcome p) (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (pastFibreSection rate rewards C_star C_h control0 t a B0) := by
  have hpref : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val) := by
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ]
    exact comap_measurable _
  have harg : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      (fun z : SourceInput p =>
        (ReferenceCalendarLaterSamplerPredictability.calendarParameters
          rate rewards C_star C_h t z,
          ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)) :=
    (ReferenceCalendarLaterSamplerPredictability.calendarParameters_measurable
      rate rewards C_star C_h control0 t).prodMk hpref
  convert ((measurable_option_section _
    (section_parameter_measurable a B0 hB0)).comp harg).stronglyMeasurable using 1
  funext z
  cases ht : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z <;> simp [pastFibreSection, ht]

private theorem test_integral_bounds {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X)
    [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    0 ≤ ∫ x, B.indicator (fun _ => (1 : ℝ)) (f x) ∂μ ∧
      (∫ x, B.indicator (fun _ => (1 : ℝ)) (f x) ∂μ) ≤ 1 := by
  constructor
  · apply integral_nonneg
    intro x
    by_cases hx : f x ∈ B <;> simp [Set.indicator, hx]
  · calc
      _ ≤ ∫ _ : X, (1 : ℝ) ∂μ := by
        apply integral_mono (integrable_test μ f hf B hB) (integrable_const 1)
        intro x
        by_cases hx : f x ∈ B <;> simp [Set.indicator, hx]
      _ = 1 := by simp

private theorem section_le_probability
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (a : Outcome p) (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0)
    (z : SourceInput p) :
    0 ≤ pastFibreSection rate rewards C_star C_h control0 t a B0 z ∧
      pastFibreSection rate rewards C_star C_h control0 t a B0 z ≤
        ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability
          rate rewards C_star C_h t a Set.univ z := by
  cases ht : ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t z with
  | none => simp [pastFibreSection,
      ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability, ht]
  | some theta =>
      have := fibre_probability theta a
      obtain ⟨h0, h1⟩ := test_integral_bounds
        (AssignmentParameterFibreKernel.fibreMeasure p theta a)
        (fun v => (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
          (some a, v))) (measurable_const.prodMk (measurable_const.prodMk measurable_id))
        B0 hB0
      simp only [pastFibreSection,
        ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability, ht, measure_univ,
        ENNReal.toReal_one, mul_one]
      exact ⟨mul_nonneg ENNReal.toReal_nonneg h0,
        mul_le_of_le_one_right ENNReal.toReal_nonneg h1⟩

/-- Every section is nonnegative and at most one, including zero fibres. -/
theorem pastFibreSection_bounds (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : Outcome p) (B0 : Set (MarkedPayload p))
    (hB0 : MeasurableSet B0) (z : SourceInput p) :
    0 ≤ pastFibreSection rate rewards C_star C_h control0 t a B0 z ∧
      pastFibreSection rate rewards C_star C_h control0 t a B0 z ≤ 1 := by
  obtain ⟨h0, hq⟩ := section_le_probability rate rewards C_star C_h control0 t a B0 hB0 z
  exact ⟨h0, hq.trans (ReferenceCalendarLaterSamplerFibreMass.fibreProbability_bounds
    rate rewards C_star C_h t a Set.univ z).2⟩

/-- The finite sum of all outcomes, including checked failure, lies in `[0,1]`. -/
theorem pastFibreSection_sum_bounds (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0)
    (z : SourceInput p) :
    0 ≤ ∑ a : Outcome p, pastFibreSection rate rewards C_star C_h control0 t a B0 z ∧
      (∑ a : Outcome p, pastFibreSection rate rewards C_star C_h control0 t a B0 z) ≤ 1 := by
  constructor
  · exact Finset.sum_nonneg fun a _ =>
      (pastFibreSection_bounds rate rewards C_star C_h control0 t a B0 hB0 z).1
  · calc
      _ ≤ ∑ a : Outcome p,
          ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability
            rate rewards C_star C_h t a Set.univ z :=
        Finset.sum_le_sum fun a _ =>
          (section_le_probability rate rewards C_star C_h control0 t a B0 hB0 z).2
      _ ≤ 1 := by
        cases ht : ReferenceCalendarLaterSamplerPredictability.calendarParameters
            rate rewards C_star C_h t z with
        | none => simp [ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability, ht]
        | some theta =>
            have (a : Outcome p) := fibre_probability theta a
            have hsum := ReferenceCalendarLaterSamplerFibreMass.fibreProbability_sum_outcomes
              rate rewards C_star C_h t z
            simpa [ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability, ht] using
              le_of_eq hsum

/-- The moving section is integrable under the original entire source law. -/
theorem pastFibreSection_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (a : Outcome p) (B0 : Set (MarkedPayload p))
    (hB0 : MeasurableSet B0) :
    Integrable (pastFibreSection rate rewards C_star C_h control0 t a B0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hs := (pastFibreSection_stronglyMeasurable
    rate rewards C_star C_h control0 t a B0 hB0).mono
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le
        (t.val + 1))
  apply (integrable_const (1 : ℝ)).mono' hs.aestronglyMeasurable
  filter_upwards [] with z
  obtain ⟨h0, h1⟩ := pastFibreSection_bounds
    rate rewards C_star C_h control0 t a B0 hB0 z
  simpa only [Real.norm_of_nonneg h0] using h1

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

private theorem prefix_replacement (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z := by
  rw [sourcePrefix_replace,
    ReferenceSourcePrefixHistoryFiltration.sourcePrefix_sourcePrefix control0
      t.val t.val le_rfl]

private theorem cell_replacement (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c ∈
      ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t := by
  have hm := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ,
    MeasurableSpace.measurableSet_comap] at hm
  obtain ⟨D, _hD, hD⟩ := hm
  rw [← hD] at hz ⊢
  change ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val _ ∈ D
  rw [prefix_replacement]
  exact hz

private theorem parameters_replacement (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) (c : ContinuousLearningRows.TimeControl p) :
    ReferenceCalendarLaterSamplerPredictability.calendarParameters
      rate rewards C_star C_h t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c) =
      ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z := by
  rw [ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
    rate rewards C_star C_h control0 t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c),
    prefix_replacement,
    ← ReferenceCalendarLaterSamplerPredictability.calendarParameters_factor
      rate rewards C_star C_h control0 t z]

private theorem vector_replacement (t : Fin p.T) (z : SourceInput p)
    (c : ContinuousLearningRows.TimeControl p) :
    ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c) =
      ContinuousControlSlice.assignmentVector c.1 := by
  simp [ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector,
    ReferenceSourceCurrentControlFreshness.u_t,
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl,
    ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex,
    ActualInitializationPhysicalStep.selectedRowIndex]

/-- Explicit projection of the existing marked physical pair. The physical
code is projected away only here; its upstream observer is unchanged. -/
def physicalProjection (t : Fin p.T)
    (y : SourceInput p ×
      (Option (ReferenceFirstCollectionPastPhysicalLaw.Code p rate) ×
        ContinuousLearningRows.TimeControl p)) : MarkedPayload p :=
  (y.1, (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
    rate rewards C_star C_h t
    (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t y.1 y.2.2),
    ContinuousControlSlice.assignmentVector y.2.2.1))

/-- The projection is jointly Borel in the source mark and entire control. -/
theorem physicalProjection_measurable (t : Fin p.T) :
    Measurable (physicalProjection rate rewards C_star C_h t) := by
  have hr : Measurable (fun y : SourceInput p ×
      (Option (ReferenceFirstCollectionPastPhysicalLaw.Code p rate) ×
        ContinuousLearningRows.TimeControl p) =>
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t y.1 y.2.2) :=
    (ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t).comp
      (measurable_fst.prodMk measurable_snd.snd)
  exact measurable_fst.prodMk
    (((activeOutcomeAt_measurable rate rewards C_star C_h t).comp hr).prodMk
      ((ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
        measurable_snd.snd.fst))

/-- The projection recovers the actual marked pair pointwise on every source. -/
theorem physicalProjection_pair_eq (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    physicalProjection rate rewards C_star C_h t
      (ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalPair
        rate rewards C_star C_h control0 t z) =
      pastFibrePair rate rewards C_star C_h control0 t z := by
  have ho := ReferenceCalendarLaterSamplerOutputSections.outputAt_successor_factor
    rate rewards C_star C_h control0 t z
  rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore] at ho
  have hout : ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
      rate rewards C_star C_h t z =
      ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          (ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
    unfold ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
    rw [ho]
    rfl
  exact congrArg
    (fun o => (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
      (o, ReferenceFirstCollectionSamplerOutputLaw.currentAssignmentVector t z))) hout.symm

private theorem fibre_graph_integral (s : SourceInput p)
    (theta : AssignmentParameterFibreKernel.Theta p)
    (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0) :
    (∫ v, B0.indicator (fun _ => (1 : ℝ))
      (s, (some (AssignmentParameterFibreKernel.successfulSlowSet p theta v), v))
        ∂ContinuousControlSlice.assignmentLaw p.K) =
      ∑ a : Outcome p, (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
        ∫ v, B0.indicator (fun _ => (1 : ℝ)) (s, (some a, v))
          ∂AssignmentParameterFibreKernel.fibreMeasure p theta a := by
  let F := AssignmentParameterFibreKernel.successfulSlowSet p theta
  let g := fun v => B0.indicator (fun _ => (1 : ℝ)) (s, (some (F v), v))
  have hF : Measurable F :=
    (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
      measurable_prodMk_left
  have hg : Integrable g (ContinuousControlSlice.assignmentLaw p.K) := by
    apply integrable_test _ _ _ B0 hB0
    exact measurable_const.prodMk
      ((LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable F hF).prodMk
        measurable_id)
  have hpartition := FiniteFibreLift.sum_restrict_fibre
    (ContinuousControlSlice.assignmentLaw p.K) F hF
  calc
    _ = ∫ v, g v ∂∑ a : Outcome p,
        (ContinuousControlSlice.assignmentLaw p.K).restrict (FiniteFibreLift.fibre F a) := by
      rw [hpartition]
    _ = ∑ a : Outcome p, ∫ v in FiniteFibreLift.fibre F a,
        g v ∂ContinuousControlSlice.assignmentLaw p.K :=
      integral_finsetSum_measure (fun _ _ => hg.integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have heq : (∫ v in FiniteFibreLift.fibre F a,
          g v ∂ContinuousControlSlice.assignmentLaw p.K) =
          ∫ v in FiniteFibreLift.fibre F a,
            B0.indicator (fun _ => (1 : ℝ)) (s, (some a, v))
              ∂ContinuousControlSlice.assignmentLaw p.K := by
        apply setIntegral_congr_fun (FiniteFibreLift.measurableSet_fibre F a hF)
        intro v hv
        change F v = a at hv
        simp only [g, hv]
      rw [heq, ← AssignmentParameterFibreKernel.fibreMass_smul_fibreMeasure,
        integral_smul_measure, smul_eq_mul]

/-- On the original cell, projecting the whole-control section gives exactly
all finite fibre sections, even for moving Borel tests of the source prefix. -/
theorem physicalSection_eq_fibreSum_on_cell
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T)
    (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0) (z : SourceInput p)
    (hz : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalSection
      rate rewards C_star C_h control0 t
      (physicalProjection rate rewards C_star C_h t ⁻¹' B0) z =
      ∑ a : Outcome p, pastFibreSection rate rewards C_star C_h control0 t a B0 z := by
  let s := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z
  obtain ⟨theta, _o, htheta, _ho, _hs, _hv, _hc, _ha⟩ :=
    ReferenceFirstCollectionSamplerFibreLaw.firstCell_actualSamplerTrace
      rate rewards C_star C_h u t z hz
  have hactive (c : ContinuousLearningRows.TimeControl p) :
      ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t s c) =
      some (AssignmentParameterFibreKernel.successfulSlowSet p theta
        (ContinuousControlSlice.assignmentVector c.1)) := by
    obtain ⟨theta', _o', htheta', _ho', _hs', _hv', _hc', ha'⟩ :=
      ReferenceFirstCollectionSamplerFibreLaw.firstCell_actualSamplerTrace
        rate rewards C_star C_h u t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t s c)
        (cell_replacement rate rewards C_star C_h control0 u t z hz c)
    have hthetaEq : theta' = theta := Option.some.inj
      (htheta'.symm.trans
        ((parameters_replacement rate rewards C_star C_h control0 t z c).trans htheta))
    rw [hthetaEq, vector_replacement] at ha'
    exact ha'
  let g : AssignmentVector p → ℝ := fun v => B0.indicator (fun _ => (1 : ℝ))
    (s, (some (AssignmentParameterFibreKernel.successfulSlowSet p theta v), v))
  have hF : Measurable (AssignmentParameterFibreKernel.successfulSlowSet p theta) :=
    (AssignmentParameterFibreKernel.measurable_successfulSlowSet_joint p).comp
      measurable_prodMk_left
  have hg : StronglyMeasurable g :=
    ((measurable_const.indicator hB0).comp
      (measurable_const.prodMk
        ((LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable _ hF).prodMk
          measurable_id))).stronglyMeasurable
  have hvec : Measurable (fun c : ContinuousLearningRows.TimeControl p =>
      ContinuousControlSlice.assignmentVector c.1) :=
    (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp measurable_fst
  have hmap : (ContinuousLearningRows.timeControlLaw p).map
      (fun c => ContinuousControlSlice.assignmentVector c.1) =
        ContinuousControlSlice.assignmentLaw p.K := by
    calc
      _ = ((ContinuousLearningRows.timeControlLaw p).map Prod.fst).map
          ContinuousControlSlice.assignmentVector :=
        (Measure.map_map (ContinuousControlSlice.measurable_assignmentVector p.m p.K)
          measurable_fst).symm
      _ = _ := by
        rw [ContinuousLearningRows.map_slice, ContinuousControlSlice.map_assignmentVector]
  have hprojection : ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalSection
      rate rewards C_star C_h control0 t
      (physicalProjection rate rewards C_star C_h t ⁻¹' B0) z =
        ∫ c, g (ContinuousControlSlice.assignmentVector c.1)
          ∂ContinuousLearningRows.timeControlLaw p := by
    unfold ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalSection
    apply integral_congr_ae
    filter_upwards [] with c
    change B0.indicator (fun _ => (1 : ℝ))
      (s, (ReferenceCalendarLaterSamplerFibreMass.activeOutcomeAt
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t s c),
        ContinuousControlSlice.assignmentVector c.1)) = _
    rw [hactive]
  calc
    _ = ∫ c, g (ContinuousControlSlice.assignmentVector c.1)
        ∂ContinuousLearningRows.timeControlLaw p := hprojection
    _ = ∫ v, g v ∂ContinuousControlSlice.assignmentLaw p.K := by
      rw [← hmap]
      exact (integral_map_of_stronglyMeasurable hvec hg).symm
    _ = ∑ a : Outcome p, (AssignmentParameterFibreKernel.fibreMass p theta a).toReal *
        ∫ v, B0.indicator (fun _ => (1 : ℝ)) (s, (some a, v))
          ∂AssignmentParameterFibreKernel.fibreMeasure p theta a :=
      fibre_graph_integral s theta B0 hB0
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [pastFibreSection, htheta]
      rfl

/-- The actual moving-test law, conditioned on the same strict-past field and
restricted to the same original first-call cell. No conditional-law premise is
supplied by its consumer. -/
theorem pastFibre_cell_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (pastFibreTest rate rewards C_star C_h control0 t B0) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
      =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (fun z => ∑ a : Outcome p,
          pastFibreSection rate rewards C_star C_h control0 t a B0 z) := by
  let B' := physicalProjection rate rewards C_star C_h t ⁻¹' B0
  have hB' : MeasurableSet B' :=
    hB0.preimage (physicalProjection_measurable rate rewards C_star C_h t)
  have htest : ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalTest
      rate rewards C_star C_h B' control0 t =
      pastFibreTest rate rewards C_star C_h control0 t B0 := by
    funext z
    change B0.indicator (fun _ => (1 : ℝ))
      (physicalProjection rate rewards C_star C_h t
        (ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalPair
          rate rewards C_star C_h control0 t z)) = _
    rw [physicalProjection_pair_eq]
    rfl
  have hce := ReferenceFirstCollectionPastPhysicalLaw.pastPhysical_cell_condExp
    rate rewards C_star C_h control0 u t B' hB'
  rw [htest] at hce
  filter_upwards [hce] with z hz
  rw [hz]
  by_cases hc : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t
  · simp only [Set.indicator_of_mem hc]
    exact physicalSection_eq_fibreSum_on_cell
      rate rewards C_star C_h control0 u t B0 hB0 z hc
  · simp only [Set.indicator_of_notMem hc]

/-- Equal unnormalized restricted integrals on the actual original cell. -/
theorem pastFibre_cell_integral (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (B0 : Set (MarkedPayload p)) (hB0 : MeasurableSet B0) :
    (∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
      pastFibreTest rate rewards C_star C_h control0 t B0 z
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t,
        (∑ a : Outcome p, pastFibreSection rate rewards C_star C_h control0 t a B0 z)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let B' := physicalProjection rate rewards C_star C_h t ⁻¹' B0
  have hB' := hB0.preimage (physicalProjection_measurable rate rewards C_star C_h t)
  have htest : ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalTest
      rate rewards C_star C_h B' control0 t =
      pastFibreTest rate rewards C_star C_h control0 t B0 := by
    funext z
    change B0.indicator (fun _ => (1 : ℝ))
      (physicalProjection rate rewards C_star C_h t
        (ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalPair
          rate rewards C_star C_h control0 t z)) = _
    rw [physicalProjection_pair_eq]
    rfl
  rw [← htest, ReferenceFirstCollectionPastPhysicalLaw.pastPhysical_cell_integral
    rate rewards C_star C_h control0 u t B' hB']
  apply setIntegral_congr_fun (cell_measurable rate rewards C_star C_h control0 u t)
  intro z hz
  exact physicalSection_eq_fibreSum_on_cell
    rate rewards C_star C_h control0 u t B0 hB0 z hz

/-- The explicit administrative projection of the marked physical observer. -/
def projectPastPhysical (y : ReferenceFirstCollectionPastPhysicalLaw.PastY p rate) :
    PastFibreY p :=
  y.map (fun c => (c.1, (c.2.1,
    physicalProjection rate rewards C_star C_h c.2.1 c.2.2)))

/-- The projection keeps original tags and is Borel. -/
theorem projectPastPhysical_measurable :
    Measurable (projectPastPhysical rate rewards C_star C_h) := by
  have hprojection : Measurable (fun y : Fin p.T ×
      (SourceInput p × (Option (ReferenceFirstCollectionPastPhysicalLaw.Code p rate) ×
        ContinuousLearningRows.TimeControl p)) =>
      physicalProjection rate rewards C_star C_h y.1 y.2) :=
    measurable_from_prod_countable_right fun t =>
      physicalProjection_measurable rate rewards C_star C_h t
  exact LaterAssignmentFullOutputMeasurability.measurable_optionMap _
    (measurable_fst.prodMk
      (measurable_snd.fst.prodMk (hprojection.comp measurable_snd))) _ measurable_id

/-- Pointwise projection of the same original first invocation. -/
theorem projectPastPhysical_output_eq (control0 : ContinuousLearningRows.TimeControl p)
    (z : SourceInput p) :
    projectPastPhysical rate rewards C_star C_h
      (ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalOutput
        rate rewards C_star C_h control0 z) =
      pastFibreOutput rate rewards C_star C_h control0 z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      simp [projectPastPhysical, ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalOutput,
        ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
        pastFibreOutput, hcall]
  | some c =>
      have hpair := physicalProjection_pair_eq rate rewards C_star C_h control0 c.2.1 z
      change physicalProjection rate rewards C_star C_h c.2.1
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 c.2.1.val z,
          (ReferenceCalendarActualControlCallbackSections.codeAt
            rate rewards C_star C_h c.2.1 z,
            ReferenceSourceCurrentControlFreshness.u_t p c.2.1 z)) = _ at hpair
      simp only [projectPastPhysical,
        ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalOutput,
        ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
        pastFibreOutput, hcall, Option.map_some, hpair]
      rfl

/-- The arbitrary Borel observation law of the actual original first call.
All outcomes, including checked failure, and all unnormalized cells are kept. -/
theorem pastFibreOutput_borel_test_law
    (control0 : ContinuousLearningRows.TimeControl p) (B : Set (PastFibreY p))
    (hB : MeasurableSet B) :
    (∫ z, B.indicator (fun _ => (1 : ℝ))
      (pastFibreOutput rate rewards C_star C_h control0 z)
        ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h) * B.indicator (fun _ => (1 : ℝ)) none +
      ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
        ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t,
          pastFibreSection rate rewards C_star C_h control0 t a (stratumSet B u t) z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let B' := projectPastPhysical rate rewards C_star C_h ⁻¹' B
  have hB' : MeasurableSet B' :=
    hB.preimage (projectPastPhysical_measurable rate rewards C_star C_h)
  have hlaw := ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalOutput_borel_test_law
    rate rewards C_star C_h control0 B' hB'
  have hleft : (fun z : SourceInput p => B'.indicator (fun _ => (1 : ℝ))
      (ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalOutput
        rate rewards C_star C_h control0 z)) =
      fun z => B.indicator (fun _ => (1 : ℝ))
        (pastFibreOutput rate rewards C_star C_h control0 z) := by
    funext z
    change B.indicator (fun _ => (1 : ℝ))
      (projectPastPhysical rate rewards C_star C_h
        (ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalOutput
          rate rewards C_star C_h control0 z)) = _
    rw [projectPastPhysical_output_eq]
  rw [hleft] at hlaw
  have hnone : B'.indicator (fun _ => (1 : ℝ)) none =
      B.indicator (fun _ => (1 : ℝ)) none := rfl
  rw [hnone] at hlaw
  rw [hlaw]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro t _
  have hslice : ReferenceFirstCollectionPastPhysicalLaw.pastPhysicalStratumSet
      rate B' u t =
      physicalProjection rate rewards C_star C_h t ⁻¹' stratumSet B u t := rfl
  rw [hslice]
  calc
    _ = ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        (∑ a : Outcome p,
          pastFibreSection rate rewards C_star C_h control0 t a (stratumSet B u t) z)
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
      apply setIntegral_congr_fun (cell_measurable rate rewards C_star C_h control0 u t)
      intro z hz
      exact physicalSection_eq_fibreSum_on_cell rate rewards C_star C_h control0 u t
        (stratumSet B u t) (stratumSet_measurable B hB u t) z hz
    _ = _ := integral_finsetSum Finset.univ fun a _ =>
      (pastFibreSection_integrable rate rewards C_star C_h control0 t a
        (stratumSet B u t) (stratumSet_measurable B hB u t)).integrableOn

/-- The univ test retains exactly the original cell mass, without conditioning
on success, dividing by a cell mass, or omitting zero fibres. -/
theorem pastFibre_cell_mass_conservation
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    (∑ a : Outcome p,
      ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t,
        pastFibreSection rate rewards C_star C_h control0 t a Set.univ z
          ∂BootstrapPrivateRoundStreams.sourceInputLaw p) =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceCalendarCollectionCallControlLaw.firstCell rate rewards C_star C_h u t) := by
  have hsection (a : Outcome p) :
      pastFibreSection rate rewards C_star C_h control0 t a Set.univ =
      ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability
        rate rewards C_star C_h t a Set.univ := by
    funext z
    cases ht : ReferenceCalendarLaterSamplerPredictability.calendarParameters
        rate rewards C_star C_h t z with
    | none => simp [pastFibreSection,
        ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability, ht]
    | some theta =>
        have := fibre_probability theta a
        simp [pastFibreSection,
          ReferenceFirstCollectionSamplerFibreLaw.firstFibreProbability, ht]
  simp_rw [hsection]
  exact ReferenceFirstCollectionSamplerFibreLaw.firstCell_fibreMass_conservation
    rate rewards C_star C_h control0 u t

/-- Total mass is the original no-call mass plus every original tagged fibre. -/
theorem pastFibreOutput_mass_conservation
    (control0 : ContinuousLearningRows.TimeControl p) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p).real
        (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h) +
      (∑ u : Fin p.T, ∑ t : Fin p.T, ∑ a : Outcome p,
        ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t,
          pastFibreSection rate rewards C_star C_h control0 t a Set.univ z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p) = 1 := by
  have h := pastFibreOutput_borel_test_law
    rate rewards C_star C_h control0 Set.univ MeasurableSet.univ
  simpa only [stratumSet, Set.mem_univ, Set.ofPred_true, Set.indicator_univ,
    integral_const, probReal_univ, smul_eq_mul, one_mul, mul_one] using h.symm

end Bandits.Support.ReferenceFirstCollectionPastSamplerFibreLaw

end
