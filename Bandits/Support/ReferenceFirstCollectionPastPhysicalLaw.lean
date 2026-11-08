/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionPhysicalCallbackLaw

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Strict-past marked physical law for the first collection invocation

The mark retains the original source with selected current and future controls
replaced by the fixed baseline. It is an analysis observation and does not
alter the physical observer or any player's information.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionPastPhysicalLaw

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

abbrev Code (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceFirstCollectionPhysicalCallbackLaw.Code p rate

/-- The first-call observation with its original tags, strict-past source mark,
and actual optional physical code and complete current control. -/
abbrev PastY (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Option (Fin p.T × (Fin p.T ×
    (SourceInput p × (Option (Code p rate) × ContinuousLearningRows.TimeControl p))))

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The actual first physical output paired with the original strict-past
source prefix at its tagged date. -/
def pastPhysicalOutput
    (control0 : ContinuousLearningRows.TimeControl p) (z : SourceInput p) :
    PastY p rate :=
  (ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput
    rate rewards C_star C_h z).map
    (fun c => (c.1, (c.2.1,
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 c.2.1.val z,
        c.2.2))))

/-- The strict-past source prefix and actual physical code/control at `t`. -/
def pastPhysicalPair (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T) (z : SourceInput p) :
    SourceInput p × (Option (Code p rate) × ContinuousLearningRows.TimeControl p) :=
  (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
    (ReferenceCalendarActualControlCallbackSections.codeAt
      rate rewards C_star C_h t z,
      ReferenceSourceCurrentControlFreshness.u_t p t z))

/-- Integrate a marked physical test over a fresh complete current control,
retaining the whole original source prefix as a mark. -/
def pastPhysicalSection (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (z : SourceInput p) : ℝ :=
  ∫ c, B0.indicator (fun _ => (1 : ℝ))
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
      (ReferenceCalendarActualControlCallbackSections.codeAt
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c), c))
    ∂ContinuousLearningRows.timeControlLaw p

/-- The slice of a Borel test corresponding to one original cutoff/date tag. -/
def pastPhysicalStratumSet (B : Set (PastY p rate)) (u t : Fin p.T) :
    Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)) :=
  {y | some (u, (t, y)) ∈ B}

/-- Test a marked pair at one fixed original source and calendar date. -/
def pastPhysicalTest (B0 : Set (SourceInput p ×
    (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  B0.indicator (fun _ => (1 : ℝ)) (pastPhysicalPair rate rewards C_star C_h control0 t z)

private theorem integrable_indicator_one_comp {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    [IsFiniteMeasure μ] (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) μ := by
  have hmeas : Measurable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) :=
    (measurable_const.indicator hB).comp hf
  apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : f x ∈ B <;> simp [Set.indicator, hx]

/-- The strict-past marked physical pair is Borel. -/
theorem pastPhysicalPair_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T) :
    Measurable (pastPhysicalPair rate rewards C_star C_h control0 t) := by
  exact (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix
      control0 t.val).prodMk
    ((ReferenceCalendarActualControlCallbackSections.measurable_codeAt
      rate rewards C_star C_h t).prodMk
      (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t))

/-- A Borel marked-output test has Borel slices at every original tag. -/
theorem pastPhysicalStratumSet_measurable
    (B : Set (PastY p rate)) (hB : MeasurableSet B) (u t : Fin p.T) :
    MeasurableSet (pastPhysicalStratumSet rate B u t) := by
  apply hB.preimage
  exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
    (fun y : SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p) =>
        (u, (t, y)))
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- The marked physical output's Borel decomposition uses the unchanged
first-call no-call event and original cutoff/date cells. -/
theorem pastPhysicalOutput_preimage_eq
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PastY p rate)) :
    pastPhysicalOutput rate rewards C_star C_h control0 ⁻¹' B =
      (if none ∈ B then
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h else ∅) ∪
        ⋃ u : Fin p.T, ⋃ t : Fin p.T,
          ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t ∩
            (pastPhysicalPair rate rewards C_star C_h control0 t ⁻¹'
              pastPhysicalStratumSet rate B u t) := by
  ext z
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hcellnone (u t : Fin p.T) :
          z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t := by
        intro hz
        have htag :=
          (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
            rate rewards C_star C_h u t z).mp hz
        rw [hcall] at htag
        simp at htag
      simp [pastPhysicalOutput, pastPhysicalStratumSet,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
        hcall, hcellnone]
  | some c =>
      have hcelltags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t ↔ (c.1, c.2.1) = (u, t) := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags]
        rw [hcall]
        simp
      simp [pastPhysicalOutput, pastPhysicalStratumSet, pastPhysicalPair,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
        hcall, hcelltags]

/-- Borel measurability of the literal strict-past marked physical output. -/
theorem pastPhysicalOutput_measurable
    (control0 : ContinuousLearningRows.TimeControl p) :
    Measurable (pastPhysicalOutput rate rewards C_star C_h control0) := by
  intro B hB
  rw [pastPhysicalOutput_preimage_eq rate rewards C_star C_h control0 B]
  have hnone : MeasurableSet
      (if none ∈ B then
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h else ∅) := by
    by_cases h : none ∈ B
    · simpa [h] using
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent_measurable
          rate rewards C_star C_h
    · simp [h]
  apply hnone.union
  refine MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun t => ?_
  have hcellField : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hcell : MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) := by
    have hfieldLe :=
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0).le (t.val + 1)
    exact hfieldLe _ hcellField
  exact hcell.inter
    ((pastPhysicalPair_measurable rate rewards C_star C_h control0 t)
      (pastPhysicalStratumSet_measurable rate B hB u t))

/-- The outer `none` tag is exactly absence of the original first invocation. -/
theorem pastPhysicalOutput_eq_none_iff_original_call_eq_none
    (control0 : ContinuousLearningRows.TimeControl p) (z : SourceInput p) :
    pastPhysicalOutput rate rewards C_star C_h control0 z = none ↔
      ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z = none := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;>
    simp [pastPhysicalOutput,
      ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput, hcall]

/-- Erasing only the retained strict-past mark recovers the exact existing
physical output pointwise, including every inner optional/failure tag. -/
theorem pastPhysicalOutput_erasePast_eq
    (control0 : ContinuousLearningRows.TimeControl p) (z : SourceInput p) :
    (pastPhysicalOutput rate rewards C_star C_h control0 z).map
      (fun c => (c.1, (c.2.1, c.2.2.2))) =
      ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput
        rate rewards C_star C_h z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;>
    simp [pastPhysicalOutput, ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
      hcall]

private theorem pastPhysicalReplacementMap_measurable
    (t : Fin p.T) :
    Measurable (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      (x.1,
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2),
          x.2))) := by
  have hreplace :=
    ReferenceSourcePhysicalFlagConditionalLaw.measurable_replaceSourceControl p t
  have hcode : Measurable (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      ReferenceCalendarActualControlCallbackSections.codeAt
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) :=
    (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
      rate rewards C_star C_h t).comp hreplace
  exact measurable_fst.prodMk (hcode.prodMk measurable_snd)

private theorem pastPhysical_replacementCode_eq
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (z : SourceInput p) :
    ReferenceCalendarActualControlCallbackSections.codeAt
        rate rewards C_star C_h t z =
      ReferenceCalendarActualControlCallbackSections.codeAt
        rate rewards C_star C_h t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z)
          (ReferenceSourceCurrentControlFreshness.u_t p t z)) := by
  have hfactor :=
    ReferenceCalendarActualControlCallbackSections.codeAt_successor_factor
      rate rewards C_star C_h control0 t z
  rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore
      control0 t z] at hfactor
  exact hfactor

/-- The marked section is strongly measurable in precisely the original
source-prefix field through the end of round `t`. -/
theorem pastPhysicalSection_stronglyMeasurable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (pastPhysicalSection rate rewards C_star C_h control0 t B0) := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
  let G : SourceInput p → ℝ := fun s =>
    ∫ c, B0.indicator (fun _ => (1 : ℝ))
      (s,
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t s c), c))
      ∂ContinuousLearningRows.timeControlLaw p
  have hmap := pastPhysicalReplacementMap_measurable rate rewards C_star C_h t
  have hfun : Measurable (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      B0.indicator (fun _ => (1 : ℝ))
        (x.1,
          (ReferenceCalendarActualControlCallbackSections.codeAt
            rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2),
            x.2))) :=
    (measurable_const.indicator hB0).comp hmap
  have hG : StronglyMeasurable G := by
    dsimp [G]
    exact hfun.stronglyMeasurable.integral_prod_right'
      (ν := ContinuousLearningRows.timeControlLaw p)
  have hpref : Measurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] pref := by
    rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_succ
      control0 t.val]
    exact comap_measurable pref
  have hfactor :
      pastPhysicalSection rate rewards C_star C_h control0 t B0 = fun z => G (pref z) := by
    funext z
    rfl
  rw [hfactor]
  exact hG.comp_measurable hpref

/-- Every marked section is a whole-`TimeControl` average of indicators and
therefore has pointwise values in `[0,1]`. -/
theorem pastPhysicalSection_bounds
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) (z : SourceInput p) :
    0 ≤ pastPhysicalSection rate rewards C_star C_h control0 t B0 z ∧
      pastPhysicalSection rate rewards C_star C_h control0 t B0 z ≤ 1 := by
  let f : ContinuousLearningRows.TimeControl p → ℝ := fun c =>
    B0.indicator (fun _ => (1 : ℝ))
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c), c))
  have hfun : Measurable f := by
    exact (measurable_const.indicator hB0).comp
      ((pastPhysicalReplacementMap_measurable rate rewards C_star C_h t).comp
        (measurable_const.prodMk measurable_id))
  have hfi : Integrable f (ContinuousLearningRows.timeControlLaw p) := by
    have hbound : ∀ c, ‖f c‖ ≤ 1 := by
      intro c
      by_cases hc :
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
            (ReferenceCalendarActualControlCallbackSections.codeAt
              rate rewards C_star C_h t
              (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c), c))
            ∈ B0 <;>
        simp [f, Set.indicator, hc]
    exact (integrable_const (1 : ℝ)).mono' hfun.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hnonneg : ∀ c, 0 ≤ f c := by
    intro c
    by_cases hc :
        (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
          (ReferenceCalendarActualControlCallbackSections.codeAt
            rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c), c))
          ∈ B0 <;>
      simp [f, Set.indicator, hc]
  constructor
  · change 0 ≤ ∫ c, f c ∂ContinuousLearningRows.timeControlLaw p
    exact integral_nonneg hnonneg
  · change (∫ c, f c ∂ContinuousLearningRows.timeControlLaw p) ≤ 1
    calc
      _ ≤ ∫ _ : ContinuousLearningRows.TimeControl p, (1 : ℝ)
          ∂ContinuousLearningRows.timeControlLaw p :=
        integral_mono hfi (integrable_const (1 : ℝ)) (by
          intro c
          by_cases hc :
              (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z,
                (ReferenceCalendarActualControlCallbackSections.codeAt
                  rate rewards C_star C_h t
                  (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
                    (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val z) c), c))
                ∈ B0 <;>
            simp [f, Set.indicator, hc])
      _ = 1 := by simp

/-- Integrability of a marked section on the original source law. -/
theorem pastPhysicalSection_integrable
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) :
    Integrable (pastPhysicalSection rate rewards C_star C_h control0 t B0)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  let pref := ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val
  let G : SourceInput p → ℝ := fun s =>
    ∫ c, B0.indicator (fun _ => (1 : ℝ))
      (s,
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t s c), c))
      ∂ContinuousLearningRows.timeControlLaw p
  have hmap := pastPhysicalReplacementMap_measurable rate rewards C_star C_h t
  have hfun : Measurable (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      B0.indicator (fun _ => (1 : ℝ))
        (x.1,
          (ReferenceCalendarActualControlCallbackSections.codeAt
            rate rewards C_star C_h t
            (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2),
            x.2))) :=
    (measurable_const.indicator hB0).comp hmap
  have hGsm : StronglyMeasurable G := by
    dsimp [G]
    exact hfun.stronglyMeasurable.integral_prod_right'
      (ν := ContinuousLearningRows.timeControlLaw p)
  have hG : Measurable G := hGsm.measurable
  have hfactor :
      pastPhysicalSection rate rewards C_star C_h control0 t B0 = fun z => G (pref z) := by
    funext z
    rfl
  have hmeas :
      Measurable (pastPhysicalSection rate rewards C_star C_h control0 t B0) := by
    rw [hfactor]
    exact hG.comp
      (ReferenceSourcePrefixHistoryFiltration.measurable_sourcePrefix control0 t.val)
  have hbound (z : SourceInput p) :
      ‖pastPhysicalSection rate rewards C_star C_h control0 t B0 z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pastPhysicalSection_bounds rate rewards C_star C_h control0 t B0 hB0 z).1]
    exact (pastPhysicalSection_bounds rate rewards C_star C_h control0 t B0 hB0 z).2
  exact (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

/-- A marked section is integrable on each original first-call cell, including
zero-mass cells. -/
theorem pastPhysical_cellSection_integrable
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) :
    IntegrableOn (pastPhysicalSection rate rewards C_star C_h control0 t B0)
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (pastPhysicalSection_integrable
    rate rewards C_star C_h control0 t B0 hB0).integrableOn

private theorem pastPhysicalTest_condExp
    (control0 : ContinuousLearningRows.TimeControl p) (t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      pastPhysicalTest rate rewards C_star C_h B0 control0 t |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      pastPhysicalSection rate rewards C_star C_h control0 t B0 := by
  let B' : Set (SourceInput p × ContinuousLearningRows.TimeControl p) :=
    (fun x : SourceInput p × ContinuousLearningRows.TimeControl p =>
      (x.1,
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2),
          x.2))) ⁻¹' B0
  have hmap := pastPhysicalReplacementMap_measurable rate rewards C_star C_h t
  have hB' : MeasurableSet B' := hmap hB0
  have htest :
      ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t B' =
        pastPhysicalTest rate rewards C_star C_h B0 control0 t := by
    funext z
    rw [ReferenceSourceCurrentControlFreshness.sourceControlTest,
      ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    have hcode := pastPhysical_replacementCode_eq
      rate rewards C_star C_h control0 t z
    simp [B', pastPhysicalTest, pastPhysicalPair, Set.indicator, hcode]
  have hsection :
      (fun z => ∫ c, B'.indicator (fun _ => (1 : ℝ))
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t z, c)
        ∂ContinuousLearningRows.timeControlLaw p) =
        pastPhysicalSection rate rewards C_star C_h control0 t B0 := by
    funext z
    rw [ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]
    rfl
  have hcond := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t B' hB'
  rw [← htest, ← hsection]
  simpa only [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t
    control0 t] using hcond

/-- The exact same-field first-cell conditional law for the joint strict-past
mark and actual physical callback. -/
theorem pastPhysical_cell_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (pastPhysicalTest rate rewards C_star C_h B0 control0 t) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (pastPhysicalSection rate rewards C_star C_h control0 t B0) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell
    rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := pastPhysicalTest rate rewards C_star C_h B0 control0 t
  let sectionValue := pastPhysicalSection rate rewards C_star C_h control0 t B0
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt : Integrable test μ :=
    integrable_indicator_one_comp (μ := μ)
      (pastPhysicalPair rate rewards C_star C_h control0 t)
      (pastPhysicalPair_measurable rate rewards C_star C_h control0 t)
      B0 hB0
  have hsectionCE := pastPhysicalTest_condExp
    rate rewards C_star C_h control0 t B0 hB0
  have hsectionCE' : μ[test | H (t.val + 1)] =ᵐ[μ] sectionValue := by
    simpa [μ, H, test, sectionValue] using hsectionCE
  have hcellStrong : StronglyMeasurable[H (t.val + 1)]
      (cell.indicator (fun _ => (1 : ℝ))) :=
    stronglyMeasurable_const.indicator hcellField
  have hproduct :
      (fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) =
        cell.indicator test := by
    funext z
    by_cases hz : z ∈ cell <;> simp [Set.indicator, hz]
  have hrestrictedInt : Integrable (cell.indicator test) μ :=
    htestInt.indicator hcellGlobal
  have hproductInt : Integrable
      (fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) μ := by
    rw [hproduct]
    exact hrestrictedInt
  have hproductAE :
      (fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) =ᵐ[μ]
        cell.indicator test :=
    Filter.Eventually.of_forall (fun z => congrFun hproduct z)
  have hpull := condExp_mul_of_stronglyMeasurable_left
    hcellStrong hproductInt htestInt
  have hleft := condExp_congr_ae (μ := μ) (m := H (t.val + 1)) hproductAE.symm
  filter_upwards [hleft, hpull, hsectionCE'] with z h₁ h₂ h₃
  calc
    μ[cell.indicator test | H (t.val + 1)] z =
        μ[(fun z => cell.indicator (fun _ => (1 : ℝ)) z * test z) |
          H (t.val + 1)] z := h₁
    _ = cell.indicator (fun _ => (1 : ℝ)) z * μ[test | H (t.val + 1)] z := h₂
    _ = cell.indicator (fun _ => (1 : ℝ)) z * sectionValue z := by rw [h₃]
    _ = cell.indicator sectionValue z := by
      by_cases hz : z ∈ cell <;> simp [Set.indicator, hz]

/-- The same joint test and its whole-control section have equal integrals on
the same original first-call cell, without normalizing its mass. -/
theorem pastPhysical_cell_integral
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B0 : Set (SourceInput p ×
      (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))
    (hB0 : MeasurableSet B0) :
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        pastPhysicalTest rate rewards C_star C_h B0 control0 t z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        pastPhysicalSection rate rewards C_star C_h control0 t B0 z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell
    rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := pastPhysicalTest rate rewards C_star C_h B0 control0 t
  let sectionValue := pastPhysicalSection rate rewards C_star C_h control0 t B0
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt := integrable_indicator_one_comp
    (μ := μ) (pastPhysicalPair rate rewards C_star C_h control0 t)
    (pastPhysicalPair_measurable rate rewards C_star C_h control0 t) B0 hB0
  have hrestrictedInt : Integrable (cell.indicator test) μ :=
    htestInt.indicator hcellGlobal
  have hce := pastPhysical_cell_condExp
    rate rewards C_star C_h control0 u t B0 hB0
  have hce' : μ[cell.indicator test | H (t.val + 1)] =ᵐ[μ]
      cell.indicator sectionValue := by
    simpa [μ, H, cell, test, sectionValue] using hce
  calc
    ∫ z in cell, test z ∂μ = ∫ z in cell, cell.indicator test z ∂μ := by
      apply setIntegral_congr_ae hcellGlobal
      filter_upwards [] with z hz
      simp [Set.indicator, hz]
    _ = ∫ z in cell, μ[cell.indicator test | H (t.val + 1)] z ∂μ := by
      symm
      exact setIntegral_condExp hfieldLe hrestrictedInt hcellField
    _ = ∫ z in cell, cell.indicator sectionValue z ∂μ := by
      exact setIntegral_congr_ae hcellGlobal (hce'.mono fun z hz _ => hz)
    _ = ∫ z in cell, sectionValue z ∂μ := by
      apply setIntegral_congr_ae hcellGlobal
      filter_upwards [] with z hz
      simp [Set.indicator, hz]

private theorem pastPhysical_cell_global_measurable
    (control0 : ContinuousLearningRows.TimeControl p) (u t : Fin p.T) :
    MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) := by
  have hfield := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  exact hfieldLe _ hfield

/-- Pointwise reconstruction of an arbitrary joint marked-output test from
the original no-call event and finite first-call tags. -/
theorem pastPhysical_indicator_reconstruction
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PastY p rate)) (z : SourceInput p) :
    B.indicator (fun _ => (1 : ℝ))
        (pastPhysicalOutput rate rewards C_star C_h control0 z) =
      (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
        rate rewards C_star C_h).indicator
        (fun _ => B.indicator (fun _ => (1 : ℝ)) none) z +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
            (pastPhysicalTest rate rewards C_star C_h
              (pastPhysicalStratumSet rate B u t)
              control0 t) z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      simp [pastPhysicalOutput,
        ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        pastPhysicalStratumSet,
        ReferenceCalendarCollectionCallControlLaw.firstCell, hcall]
  | some c =>
      let value : ℝ := B.indicator (fun _ => (1 : ℝ))
        (pastPhysicalOutput rate rewards C_star C_h control0 z)
      let u₀ : Fin p.T := c.1
      let t₀ : Fin p.T := c.2.1
      have hcelltags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t ↔ (c.1, c.2.1) = (u, t) := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags]
        rw [hcall]
        simp
      have htest_eq :
          pastPhysicalTest rate rewards C_star C_h
            (pastPhysicalStratumSet rate B u₀ t₀)
            control0 t₀ z =
          B.indicator (fun _ => (1 : ℝ))
            (pastPhysicalOutput rate rewards C_star C_h control0 z) := by
        simp only [pastPhysicalTest, Set.indicator, pastPhysicalStratumSet,
          Set.mem_ofPred_eq]
        simp [pastPhysicalOutput,
          ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
          pastPhysicalPair, hcall, u₀, t₀]
        rfl
      have hterm (u t : Fin p.T) :
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
            (pastPhysicalTest rate rewards C_star C_h
              (pastPhysicalStratumSet rate B u t)
              control0 t) z =
          if (u, t) = (u₀, t₀) then value else 0 := by
        by_cases hpair : (u, t) = (u₀, t₀)
        · have hu : u = u₀ := congrArg Prod.fst hpair
          have ht : t = t₀ := congrArg Prod.snd hpair
          subst u
          subst t
          have hcell : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u₀ t₀ := by
            exact (hcelltags u₀ t₀).mpr (by simp [u₀, t₀])
          simp [value, htest_eq, hcell]
        · have hnot : z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t := by
            intro hz
            have htag := (hcelltags u t).mp hz
            exact hpair (by simpa [u₀, t₀] using htag.symm)
          simp [hnot, hpair]
      have hinner (u : Fin p.T) :
          (∑ t : Fin p.T,
            (ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t).indicator
              (pastPhysicalTest rate rewards C_star C_h
                (pastPhysicalStratumSet rate B u t)
                control0 t) z) =
            if u = u₀ then value else 0 := by
        by_cases hu : u = u₀
        · subst u
          simp_rw [hterm]
          simp [u₀, t₀]
        · simp_rw [hterm]
          simp [hu, u₀]
      have hsum :
          (∑ u : Fin p.T, ∑ t : Fin p.T,
            (ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t).indicator
              (pastPhysicalTest rate rewards C_star C_h
                (pastPhysicalStratumSet rate B u t)
                control0 t) z) = value := by
        simp_rw [hinner]
        simp [u₀]
      rw [hsum]
      simp [pastPhysicalOutput,
        ReferenceFirstCollectionPhysicalCallbackLaw.firstPhysicalOutput,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        hcall, value]

private theorem pastPhysical_cellTest_integrable
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PastY p rate)) (hB : MeasurableSet B) (u t : Fin p.T) :
    Integrable
      ((ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (pastPhysicalTest rate rewards C_star C_h
          (pastPhysicalStratumSet rate B u t)
          control0 t))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hslice := pastPhysicalStratumSet_measurable rate B hB u t
  have htest := integrable_indicator_one_comp
    (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (pastPhysicalPair rate rewards C_star C_h control0 t)
    (pastPhysicalPair_measurable rate rewards C_star C_h control0 t)
    (pastPhysicalStratumSet rate B u t) hslice
  have hfield := ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
    rate rewards C_star C_h control0 u t
  have hcell := by
    have hfieldLe :=
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0).le (t.val + 1)
    exact hfieldLe _ hfield
  exact htest.indicator hcell

/-- The exact arbitrary-Borel-test joint law of the original first call,
strict-past source mark, physical code, and whole current control. -/
theorem pastPhysicalOutput_borel_test_law
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (PastY p rate)) (hB : MeasurableSet B) :
    ∫ z, B.indicator (fun _ => (1 : ℝ))
        (pastPhysicalOutput rate rewards C_star C_h control0 z)
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
            rate rewards C_star C_h) *
        B.indicator (fun _ => (1 : ℝ)) none +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t,
            pastPhysicalSection rate rewards C_star C_h control0 t
              (pastPhysicalStratumSet rate B u t) z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let noneValue : ℝ := B.indicator (fun _ => (1 : ℝ)) none
  let noneTerm : SourceInput p → ℝ :=
    (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
      rate rewards C_star C_h).indicator (fun _ => noneValue)
  let cellTerm (u t : Fin p.T) : SourceInput p → ℝ :=
    (ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t).indicator
      (pastPhysicalTest rate rewards C_star C_h
        (pastPhysicalStratumSet rate B u t) control0 t)
  have hnoneMeas :=
    ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent_measurable
      rate rewards C_star C_h
  have hnoneInt : Integrable noneTerm μ :=
    (integrable_const noneValue).indicator hnoneMeas
  have hcellInt (u t : Fin p.T) : Integrable (cellTerm u t) μ := by
    exact pastPhysical_cellTest_integrable rate rewards C_star C_h control0 B hB u t
  have hsumInt : Integrable
      (fun z => ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) μ := by
    apply integrable_finsetSum
    intro u hu
    apply integrable_finsetSum
    intro t ht
    exact hcellInt u t
  have _hleftInt := integrable_indicator_one_comp
    (μ := μ)
    (pastPhysicalOutput rate rewards C_star C_h control0)
    (pastPhysicalOutput_measurable rate rewards C_star C_h control0) B hB
  have hpoint (z : SourceInput p) :
      B.indicator (fun _ => (1 : ℝ))
          (pastPhysicalOutput rate rewards C_star C_h control0 z) =
        noneTerm z + ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z := by
    simpa [noneTerm, cellTerm, noneValue] using
      pastPhysical_indicator_reconstruction rate rewards C_star C_h control0 B z
  have hnoneIntegral :
      ∫ z, noneTerm z ∂μ =
        μ.real (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h) * noneValue := by
    change ∫ z,
      (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
        rate rewards C_star C_h).indicator (fun _ => noneValue) z ∂μ = _
    rw [integral_indicator_const noneValue hnoneMeas, smul_eq_mul]
  have hsumIntegral :
      ∫ z, ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z ∂μ =
        ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z, cellTerm u t z ∂μ := by
    calc
      _ = ∑ u : Fin p.T, ∫ z, ∑ t : Fin p.T, cellTerm u t z ∂μ := by
        simpa using
          (integral_finsetSum Finset.univ
            (f := fun u z => ∑ t : Fin p.T, cellTerm u t z)
            (fun u hu => by
              apply integrable_finsetSum
              intro t ht
              exact hcellInt u t))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u hu
        exact integral_finsetSum Finset.univ
          (fun t ht => hcellInt u t)
  have hcellMix (u t : Fin p.T) :
      ∫ z, cellTerm u t z ∂μ =
        ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t,
          pastPhysicalSection rate rewards C_star C_h control0 t
            (pastPhysicalStratumSet rate B u t) z ∂μ := by
    rw [show cellTerm u t =
        (ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t).indicator
          (pastPhysicalTest rate rewards C_star C_h
            (pastPhysicalStratumSet rate B u t)
            control0 t) from rfl]
    rw [integral_indicator
      (pastPhysical_cell_global_measurable rate rewards C_star C_h control0 u t)]
    exact pastPhysical_cell_integral rate rewards C_star C_h control0 u t
      (pastPhysicalStratumSet rate B u t)
      (pastPhysicalStratumSet_measurable rate B hB u t)
  calc
    _ = ∫ z, noneTerm z +
          (∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = ∫ z, noneTerm z ∂μ +
          ∫ z, ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z ∂μ :=
      integral_add' hnoneInt hsumInt
    _ = (∫ z, noneTerm z ∂μ) +
          ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z, cellTerm u t z ∂μ := by
      rw [hsumIntegral]
    _ = μ.real (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h) * noneValue +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t,
              pastPhysicalSection rate rewards C_star C_h control0 t
                (pastPhysicalStratumSet rate B u t) z ∂μ := by
      rw [hnoneIntegral]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      exact hcellMix u t

end Bandits.Support.ReferenceFirstCollectionPastPhysicalLaw

end
