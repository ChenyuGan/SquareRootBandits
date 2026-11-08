/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceSourcePrefixHistoryFiltration
public import Bandits.Support.ReferenceSourceCurrentControlFreshness
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Conditional section integrals for the actual physical flags

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:376-426,459-490`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-79`.

The tests below are the actual UP, DATA, and release observations on the
original complete source. Their conditional expectations are represented by
integrating the same tests after replacing the whole current control by a
fresh `TimeControl`. Release support is retained as a separate multiplier.
These identities do not establish the physical service lower bounds or a
waiting-time estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.BootstrapPrivateRoundStreams
open Bandits.Support.ReferenceFixedTimeSourceControlCoupling
open scoped Classical MeasureTheory

namespace Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw

abbrev Parameters := ConstructorDimensions.Parameters
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private def fixedSourceControl (p : Parameters) (t : Fin p.T)
    (q : Fin (M p)) (x : SourceInput p × TimeControl p) : SourceInput p :=
  ((x.1.1.1, Function.update x.1.1.2 q
    ((x.1.1.2 q).1, Function.update (x.1.1.2 q).2 t x.2)), x.1.2)

private theorem measurable_by_countable_cases {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [Countable β]
    [MeasurableSingletonClass β] [MeasurableSpace γ]
    (key : α → β) (hkey : Measurable key) (branch : β → α → γ)
    (hbranch : ∀ b, Measurable (branch b)) :
    Measurable (fun x => branch (key x) x) :=
  (measurable_from_prod_countable_right
    (f := fun v : β × α => branch v.1 v.2) hbranch).comp
      (hkey.prodMk measurable_id)

private theorem measurable_sourceCoordinatorIndex_pair (p : Parameters) :
    Measurable (fun x : SourceInput p × TimeControl p =>
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p x.1) := by
  have hscalar : Measurable (fun x : SourceInput p × TimeControl p => x.1.2.1.2) :=
    measurable_snd.comp
      (measurable_fst.comp (measurable_snd.comp measurable_fst))
  exact (PrivateSourceStreams.measurable_coordinatorIndex p).comp hscalar

/-- Replacing a current control is jointly Borel in the arbitrary original
source and the complete replacement control, including all affine pairs. -/
theorem measurable_replaceSourceControl (p : Parameters) (t : Fin p.T) :
    Measurable (fun x : SourceInput p × TimeControl p =>
      ReferenceFixedTimeSourceControlCoupling.replaceSourceControl
        p t x.1 x.2) := by
  have hcases := measurable_by_countable_cases
    (fun x : SourceInput p × TimeControl p =>
      ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p x.1)
    (measurable_sourceCoordinatorIndex_pair p)
    (fun q x => fixedSourceControl p t q x)
    (fun q => by fun_prop [fixedSourceControl])
  have heq :
      (fun x : SourceInput p × TimeControl p =>
        fixedSourceControl p t
          (ReferenceFixedTimeSourceControlCoupling.sourceCoordinatorIndex p x.1) x) =
      (fun x : SourceInput p × TimeControl p =>
        ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2) := by
    funext x
    simp [fixedSourceControl, ReferenceFixedTimeSourceControlCoupling.replaceSourceControl]
  rw [← heq]
  exact hcases

variable {p : Parameters}

/-- The prefix used by the freshness theorem is exactly A's strict prefix. -/
theorem c_t_eq_sourcePrefix (control0 : TimeControl p) (t : Fin p.T)
    (source : SourceInput p) :
    ReferenceSourceCurrentControlFreshness.c_t p control0 t source =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source := by
  unfold ReferenceSourceCurrentControlFreshness.c_t
  exact (ReferenceSourcePrefixHistoryFiltration.sourcePrefix_eq_suffix
    control0 t.val t.isLt source).symm

/-- The outcome field at `t.val + 1` is B's current-prefix field. -/
theorem sourcePrefixField_eq_m_t (control0 : TimeControl p) (t : Fin p.T) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1) =
      ReferenceSourceCurrentControlFreshness.m_t p control0 t := by
  rw [ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration_round
    control0 t]
  rfl

private theorem selectedCurrentControl_eq_u_t (t : Fin p.T)
    (source : SourceInput p) :
    ReferenceSourceCurrentControlFreshness.u_t p t source =
      (source.1.2
        (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t := rfl

def actualUpControlTest (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Set (SourceInput p × TimeControl p) :=
  {x | ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2) = true}

def actualDataControlTest (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Set (SourceInput p × TimeControl p) :=
  {x | ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2) = true}

def actualReleaseControlTest (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Set (SourceInput p × TimeControl p) :=
  {x | ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2) = true}

def actualUpControlSectionIntegrand (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (x : SourceInput p × TimeControl p) : ℝ :=
  if ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)
  then 1 else 0

def actualDataControlSectionIntegrand (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (x : SourceInput p × TimeControl p) : ℝ :=
  if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)
  then 1 else 0

def actualReleaseControlSectionIntegrand (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    (x : SourceInput p × TimeControl p) : ℝ :=
  if ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t
      (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)
  then 1 else 0

def actualUpControlSection (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) : ℝ :=
  ∫ control, actualUpControlSectionIntegrand rate rewards C_star C_h i t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
    ∂ContinuousLearningRows.timeControlLaw p

def actualDataControlSection (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) : ℝ :=
  ∫ control, actualDataControlSectionIntegrand rate rewards C_star C_h i t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
    ∂ContinuousLearningRows.timeControlLaw p

def actualReleaseControlSection (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) : ℝ :=
  ∫ control, actualReleaseControlSectionIntegrand rate rewards C_star C_h i t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
    ∂ContinuousLearningRows.timeControlLaw p

private theorem actualUp_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (ReferenceSourcePrefixHistoryFiltration.actualUp
      rate rewards C_star C_h i t) :=
  measurable_fst.comp (ReferenceSourcePrefixHistoryFiltration.measurable_flags
    rate rewards C_star C_h control0 i t)

private theorem actualData_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (ReferenceSourcePrefixHistoryFiltration.actualData
      rate rewards C_star C_h i t) := by
  exact measurable_fst.comp (measurable_snd.comp
    (ReferenceSourcePrefixHistoryFiltration.measurable_flags
      rate rewards C_star C_h control0 i t))

private theorem actualRelease_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (ReferenceSourcePrefixHistoryFiltration.actualRelease
      rate rewards C_star C_h i t) := by
  exact measurable_snd.comp (measurable_snd.comp
    (ReferenceSourcePrefixHistoryFiltration.measurable_flags
      rate rewards C_star C_h control0 i t))

private theorem actualBoolIndicator_measurable {α : Type*} [MeasurableSpace α]
    {f : α → Bool} (hf : Measurable f) :
    Measurable (fun x => if f x then (1 : ℝ) else 0) :=
  (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp hf

private theorem integrable_measurable_norm_le_one {α : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f μ := by
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

private theorem measurableSet_option_singleton {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : Option α) :
    MeasurableSet ({a} : Set (Option α)) := by
  let e := Equiv.optionEquivSumPUnit α
  have he : Measurable e := comap_measurable _
  have hset : ({a} : Set (Option α)) = e ⁻¹' {e a} := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage]
    exact ⟨congrArg e, fun h => e.injective h⟩
  rw [hset]
  apply he
  cases h : e a with
  | inl value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inl_image (β := PUnit)
  | inr value =>
      simpa only [Set.image_singleton] using
        (measurableSet_singleton value).inr_image (α := α)

theorem actualUpControlTest_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (actualUpControlTest rate rewards C_star C_h i t) := by
  change MeasurableSet
    ((fun x : SourceInput p × TimeControl p =>
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) ⁻¹'
      ({true} : Set Bool))
  exact (actualUp_measurable rate rewards C_star C_h control0 i t).comp
    (measurable_replaceSourceControl p t) (MeasurableSet.singleton true)

theorem actualDataControlTest_measurable (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (actualDataControlTest rate rewards C_star C_h i t) := by
  change MeasurableSet
    ((fun x : SourceInput p × TimeControl p =>
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) ⁻¹'
      ({true} : Set Bool))
  exact (actualData_measurable rate rewards C_star C_h control0 i t).comp
    (measurable_replaceSourceControl p t) (MeasurableSet.singleton true)

theorem actualReleaseControlTest_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (actualReleaseControlTest rate rewards C_star C_h i t) := by
  change MeasurableSet
    ((fun x : SourceInput p × TimeControl p =>
      ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t
        (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t x.1 x.2)) ⁻¹'
      ({true} : Set Bool))
  exact (actualRelease_measurable rate rewards C_star C_h control0 i t).comp
    (measurable_replaceSourceControl p t) (MeasurableSet.singleton true)

theorem actualUpControlSectionIntegrand_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualUpControlSectionIntegrand rate rewards C_star C_h i t) :=
  actualBoolIndicator_measurable
    ((actualUp_measurable rate rewards C_star C_h control0 i t).comp
      (measurable_replaceSourceControl p t))

theorem actualDataControlSectionIntegrand_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualDataControlSectionIntegrand rate rewards C_star C_h i t) :=
  actualBoolIndicator_measurable
    ((actualData_measurable rate rewards C_star C_h control0 i t).comp
      (measurable_replaceSourceControl p t))

theorem actualReleaseControlSectionIntegrand_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (actualReleaseControlSectionIntegrand rate rewards C_star C_h i t) :=
  actualBoolIndicator_measurable
    ((actualRelease_measurable rate rewards C_star C_h control0 i t).comp
      (measurable_replaceSourceControl p t))

private theorem sectionIntegral_stronglyMeasurable
    (control0 : TimeControl p) (t : Fin p.T)
    (f : SourceInput p × TimeControl p → ℝ) (hf : Measurable f) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (fun source => ∫ control, f
        (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
        ∂ContinuousLearningRows.timeControlLaw p) := by
  have hbase : StronglyMeasurable
      (fun prefixSource : SourceInput p => ∫ control, f (prefixSource, control)
        ∂ContinuousLearningRows.timeControlLaw p) :=
    hf.stronglyMeasurable.integral_prod_right'
  rw [sourcePrefixField_eq_m_t control0 t]
  exact hbase.comp_measurable (comap_measurable
    (ReferenceSourceCurrentControlFreshness.c_t p control0 t))

private theorem probability_integral_bounds (f : TimeControl p → ℝ)
    (hf : Measurable f) (hzero : ∀ control, 0 ≤ f control)
    (hone : ∀ control, f control ≤ 1) :
    0 ≤ ∫ control, f control ∂ContinuousLearningRows.timeControlLaw p ∧
      (∫ control, f control ∂ContinuousLearningRows.timeControlLaw p) ≤ 1 := by
  have hnorm : ∀ control, ‖f control‖ ≤ 1 := by
    intro control
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hzero control], hone control⟩
  have hfint : Integrable f (ContinuousLearningRows.timeControlLaw p) :=
    integrable_measurable_norm_le_one f hf hnorm
  constructor
  · exact integral_nonneg hzero
  · calc
      (∫ control, f control ∂ContinuousLearningRows.timeControlLaw p) ≤
          ∫ control, (1 : ℝ) ∂ContinuousLearningRows.timeControlLaw p :=
        integral_mono_ae hfint (integrable_const 1)
          (Filter.Eventually.of_forall hone)
      _ = 1 := by simp

theorem actualUpControlSection_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (actualUpControlSection rate rewards C_star C_h control0 i t) := by
  exact sectionIntegral_stronglyMeasurable control0 t
    (actualUpControlSectionIntegrand rate rewards C_star C_h i t)
    (actualUpControlSectionIntegrand_measurable rate rewards C_star C_h control0 i t)

theorem actualDataControlSection_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (actualDataControlSection rate rewards C_star C_h control0 i t) := by
  exact sectionIntegral_stronglyMeasurable control0 t
    (actualDataControlSectionIntegrand rate rewards C_star C_h i t)
    (actualDataControlSectionIntegrand_measurable rate rewards C_star C_h control0 i t)

theorem actualReleaseControlSection_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (actualReleaseControlSection rate rewards C_star C_h control0 i t) := by
  exact sectionIntegral_stronglyMeasurable control0 t
    (actualReleaseControlSectionIntegrand rate rewards C_star C_h i t)
    (actualReleaseControlSectionIntegrand_measurable rate rewards C_star C_h control0 i t)

theorem actualUpControlSection_bounds (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualUpControlSection rate rewards C_star C_h control0 i t source ∧
      actualUpControlSection rate rewards C_star C_h control0 i t source ≤ 1 := by
  change 0 ≤ ∫ control, actualUpControlSectionIntegrand rate rewards C_star C_h i t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
      ∂ContinuousLearningRows.timeControlLaw p ∧ _
  apply probability_integral_bounds
  · exact (actualUpControlSectionIntegrand_measurable
      rate rewards C_star C_h control0 i t).comp
        (measurable_const.prodMk measurable_id)
  · intro control
    simp only [actualUpControlSectionIntegrand]
    split_ifs <;> norm_num
  · intro control
    simp only [actualUpControlSectionIntegrand]
    split_ifs <;> norm_num

theorem actualDataControlSection_bounds (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualDataControlSection rate rewards C_star C_h control0 i t source ∧
      actualDataControlSection rate rewards C_star C_h control0 i t source ≤ 1 := by
  change 0 ≤ ∫ control, actualDataControlSectionIntegrand rate rewards C_star C_h i t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
      ∂ContinuousLearningRows.timeControlLaw p ∧ _
  apply probability_integral_bounds
  · exact (actualDataControlSectionIntegrand_measurable
      rate rewards C_star C_h control0 i t).comp
        (measurable_const.prodMk measurable_id)
  · intro control
    simp only [actualDataControlSectionIntegrand]
    split_ifs <;> norm_num
  · intro control
    simp only [actualDataControlSectionIntegrand]
    split_ifs <;> norm_num

theorem actualReleaseControlSection_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ actualReleaseControlSection rate rewards C_star C_h control0 i t source ∧
      actualReleaseControlSection rate rewards C_star C_h control0 i t source ≤ 1 := by
  change 0 ≤ ∫ control, actualReleaseControlSectionIntegrand rate rewards C_star C_h i t
      (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
      ∂ContinuousLearningRows.timeControlLaw p ∧ _
  apply probability_integral_bounds
  · exact (actualReleaseControlSectionIntegrand_measurable
      rate rewards C_star C_h control0 i t).comp
        (measurable_const.prodMk measurable_id)
  · intro control
    simp only [actualReleaseControlSectionIntegrand]
    split_ifs <;> norm_num
  · intro control
    simp only [actualReleaseControlSectionIntegrand]
    split_ifs <;> norm_num

theorem actualUp_observation_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (fun source =>
      if ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t source
      then (1 : ℝ) else 0) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_measurable_norm_le_one
  · exact actualBoolIndicator_measurable
      (actualUp_measurable rate rewards C_star C_h control0 i t)
  · intro source
    split_ifs <;> norm_num

theorem actualData_observation_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (fun source =>
      if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t source
      then (1 : ℝ) else 0) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_measurable_norm_le_one
  · exact actualBoolIndicator_measurable
      (actualData_measurable rate rewards C_star C_h control0 i t)
  · intro source
    split_ifs <;> norm_num

theorem actualRelease_observation_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (fun source =>
      if ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t source
      then (1 : ℝ) else 0) (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  apply integrable_measurable_norm_le_one
  · exact actualBoolIndicator_measurable
      (actualRelease_measurable rate rewards C_star C_h control0 i t)
  · intro source
    split_ifs <;> norm_num

theorem actual_up_condExp (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun source =>
        if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      actualUpControlSection rate rewards C_star C_h control0 i t := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hrestore (source : SourceInput p) :
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t source =
        ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source) :=
        (ReferenceSourcePrefixHistoryFiltration.flags_factor rate rewards C_star C_h
          control0 i t source).1
      _ = ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source)
            ((source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t)) := by
        rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t source]
      _ = _ := by
        rw [← c_t_eq_sourcePrefix control0 t source,
          ← selectedCurrentControl_eq_u_t t source]
  have htestEq :
      ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
        (actualUpControlTest rate rewards C_star C_h i t) =
      (fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
        rate rewards C_star C_h i t source then (1 : ℝ) else 0) := by
    funext source
    by_cases hflag : ReferenceSourcePrefixHistoryFiltration.actualUp
        rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) = true
    · simp [ReferenceSourceCurrentControlFreshness.sourceControlTest,
        actualUpControlTest, Set.indicator, hrestore source, hflag]
    · simp [ReferenceSourceCurrentControlFreshness.sourceControlTest,
        actualUpControlTest, Set.indicator, hrestore source, hflag]
  have hsectionEq (source : SourceInput p) :
      (∫ control, (actualUpControlTest rate rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
        ∂ContinuousLearningRows.timeControlLaw p) =
        actualUpControlSection rate rewards C_star C_h control0 i t source := by
    apply integral_congr_ae
    filter_upwards [] with control
    by_cases hflag : ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards
        C_star C_h i t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) control)
    · simp [actualUpControlSectionIntegrand, actualUpControlTest,
        Set.indicator, hflag]
    · simp [actualUpControlSectionIntegrand, actualUpControlTest,
        Set.indicator, hflag]
  have htest := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t (actualUpControlTest rate rewards C_star C_h i t)
    (actualUpControlTest_measurable rate rewards C_star C_h control0 i t)
  have hcond :
      μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
        rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[μ]
        actualUpControlSection rate rewards C_star C_h control0 i t := by
    filter_upwards [htest] with source hsource
    have hsource' :
        μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
          (∫ control, (actualUpControlTest rate rewards C_star C_h i t).indicator
            (fun _ => (1 : ℝ))
              (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
            ∂ContinuousLearningRows.timeControlLaw p) := by
      simpa only [htestEq] using hsource
    exact hsource'.trans (hsectionEq source)
  simpa only [sourcePrefixField_eq_m_t control0 t] using hcond

theorem actual_data_condExp (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun source =>
        if ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      actualDataControlSection rate rewards C_star C_h control0 i t := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hrestore (source : SourceInput p) :
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t source =
        ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source) :=
        (ReferenceSourcePrefixHistoryFiltration.flags_factor rate rewards C_star C_h
          control0 i t source).2.1
      _ = ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source)
            ((source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t)) := by
        rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t source]
      _ = _ := by
        rw [← c_t_eq_sourcePrefix control0 t source,
          ← selectedCurrentControl_eq_u_t t source]
  have htestEq :
      ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
        (actualDataControlTest rate rewards C_star C_h i t) =
      (fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
        rate rewards C_star C_h i t source then (1 : ℝ) else 0) := by
    funext source
    by_cases hflag : ReferenceSourcePrefixHistoryFiltration.actualData
        rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) = true
    · simp [ReferenceSourceCurrentControlFreshness.sourceControlTest,
        actualDataControlTest, Set.indicator, hrestore source, hflag]
    · simp [ReferenceSourceCurrentControlFreshness.sourceControlTest,
        actualDataControlTest, Set.indicator, hrestore source, hflag]
  have hsectionEq (source : SourceInput p) :
      (∫ control, (actualDataControlTest rate rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
        ∂ContinuousLearningRows.timeControlLaw p) =
        actualDataControlSection rate rewards C_star C_h control0 i t source := by
    apply integral_congr_ae
    filter_upwards [] with control
    by_cases hflag : ReferenceSourcePrefixHistoryFiltration.actualData rate rewards
        C_star C_h i t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) control)
    · simp [actualDataControlSectionIntegrand, actualDataControlTest,
        Set.indicator, hflag]
    · simp [actualDataControlSectionIntegrand, actualDataControlTest,
        Set.indicator, hflag]
  have htest := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t (actualDataControlTest rate rewards C_star C_h i t)
    (actualDataControlTest_measurable rate rewards C_star C_h control0 i t)
  have hcond :
      μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
        rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[μ]
        actualDataControlSection rate rewards C_star C_h control0 i t := by
    filter_upwards [htest] with source hsource
    have hsource' :
        μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
          (∫ control, (actualDataControlTest rate rewards C_star C_h i t).indicator
            (fun _ => (1 : ℝ))
              (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
            ∂ContinuousLearningRows.timeControlLaw p) := by
      simpa only [htestEq] using hsource
    exact hsource'.trans (hsectionEq source)
  simpa only [sourcePrefixField_eq_m_t control0 t] using hcond

theorem actual_release_condExp (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun source =>
        if ReferenceSourcePrefixHistoryFiltration.actualRelease
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      actualReleaseControlSection rate rewards C_star C_h control0 i t := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hrestore (source : SourceInput p) :
      ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t source =
        ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t
          (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 (t.val + 1) source) :=
        (ReferenceSourcePrefixHistoryFiltration.flags_factor rate rewards C_star C_h
          control0 i t source).2.2
      _ = ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val source)
            ((source.1.2
              (ActualInitializationPhysicalStep.selectedRowIndex p source)).2 t)) := by
        rw [ReferenceSourcePrefixHistoryFiltration.prefix_successor_restore control0 t source]
      _ = _ := by
        rw [← c_t_eq_sourcePrefix control0 t source,
          ← selectedCurrentControl_eq_u_t t source]
  have htestEq :
      ReferenceSourceCurrentControlFreshness.sourceControlTest p control0 t
        (actualReleaseControlTest rate rewards C_star C_h i t) =
      (fun source => if ReferenceSourcePrefixHistoryFiltration.actualRelease
        rate rewards C_star C_h i t source then (1 : ℝ) else 0) := by
    funext source
    by_cases hflag : ReferenceSourcePrefixHistoryFiltration.actualRelease
        rate rewards C_star C_h i t
          (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
            (ReferenceSourceCurrentControlFreshness.c_t p control0 t source)
            (ReferenceSourceCurrentControlFreshness.u_t p t source)) = true
    · simp [ReferenceSourceCurrentControlFreshness.sourceControlTest,
        actualReleaseControlTest, Set.indicator, hrestore source, hflag]
    · simp [ReferenceSourceCurrentControlFreshness.sourceControlTest,
        actualReleaseControlTest, Set.indicator, hrestore source, hflag]
  have hsectionEq (source : SourceInput p) :
      (∫ control, (actualReleaseControlTest rate rewards C_star C_h i t).indicator
        (fun _ => (1 : ℝ))
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
        ∂ContinuousLearningRows.timeControlLaw p) =
        actualReleaseControlSection rate rewards C_star C_h control0 i t source := by
    apply integral_congr_ae
    filter_upwards [] with control
    by_cases hflag : ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards
        C_star C_h i t (ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t
          (ReferenceSourceCurrentControlFreshness.c_t p control0 t source) control)
    · simp [actualReleaseControlSectionIntegrand, actualReleaseControlTest,
        Set.indicator, hflag]
    · simp [actualReleaseControlSectionIntegrand, actualReleaseControlTest,
        Set.indicator, hflag]
  have htest := ReferenceSourceCurrentControlFreshness.source_control_test_condExp
    control0 t (actualReleaseControlTest rate rewards C_star C_h i t)
    (actualReleaseControlTest_measurable rate rewards C_star C_h control0 i t)
  have hcond :
      μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualRelease
        rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[μ]
        actualReleaseControlSection rate rewards C_star C_h control0 i t := by
    filter_upwards [htest] with source hsource
    have hsource' :
        μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualRelease
          rate rewards C_star C_h i t source then (1 : ℝ) else 0) |
            ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
          (∫ control, (actualReleaseControlTest rate rewards C_star C_h i t).indicator
            (fun _ => (1 : ℝ))
              (ReferenceSourceCurrentControlFreshness.c_t p control0 t source, control)
            ∂ContinuousLearningRows.timeControlLaw p) := by
      simpa only [htestEq] using hsource
    exact hsource'.trans (hsectionEq source)
  simpa only [sourcePrefixField_eq_m_t control0 t] using hcond

/-- The full local-release entry and pending-follower support used by waiting
estimates. The outer option is preserved, including absent and empty entries. -/
def actualReleaseSupport (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Set (SourceInput p) :=
  {source |
    (ReferenceSourcePrefixHistoryFiltration.entry rate rewards C_star C_h b t source).map
        Prod.fst = some true ∧
      i ∈ ReferenceSourcePrefixHistoryFiltration.pending
        rate rewards C_star C_h b t source}

def actualReleaseSupportIndicator (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1))
    (source : SourceInput p) : ℝ :=
  (actualReleaseSupport rate rewards C_star C_h b t i).indicator
    (fun _ => (1 : ℝ)) source

theorem actualReleaseSupport_measurableSet
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1)) :
    MeasurableSet[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (actualReleaseSupport rate rewards C_star C_h b t i) := by
  have hentry := ReferenceSourcePrefixHistoryFiltration.entry_measurable
    rate rewards C_star C_h control0 b t
  have hpending := ReferenceSourcePrefixHistoryFiltration.pending_measurable
    rate rewards C_star C_h control0 b t
  have hselect : Measurable
      (fun e : Option (Bool × Option (Finset (Fin (p.m - 1)))) => e.map Prod.fst) := by
    exact ReferenceCollectionInstallOutputMeasurability.measurable_optionMapDependent
      (fun z : (Bool × Option (Finset (Fin (p.m - 1)))) ×
        Option (Bool × Option (Finset (Fin (p.m - 1)))) => z.1.1)
      (measurable_fst.comp measurable_fst) id measurable_id
  have hentryPred : MeasurableSet ({some true} : Set (Option Bool)) :=
    measurableSet_option_singleton (some true)
  have hpendingPred : MeasurableSet
      {s : Finset (Fin (p.m - 1)) | i ∈ s} := by
    let f := fun s : Finset (Fin (p.m - 1)) => decide (i ∈ s)
    have hf : Measurable f := measurable_of_countable _
    have hpre : MeasurableSet (f ⁻¹' ({true} : Set Bool)) :=
      hf (MeasurableSet.singleton true)
    have hEq : {s : Finset (Fin (p.m - 1)) | i ∈ s} =
        f ⁻¹' ({true} : Set Bool) := by
      ext s
      simp [f]
    rw [hEq]
    exact hpre
  have hentrySet : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      {source | (ReferenceSourcePrefixHistoryFiltration.entry
          rate rewards C_star C_h b t source).map Prod.fst = some true} :=
    (hselect.comp hentry) hentryPred
  have hpendingSet : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      {source | i ∈ ReferenceSourcePrefixHistoryFiltration.pending
        rate rewards C_star C_h b t source} := hpending hpendingPred
  change MeasurableSet[
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
    ({source | (ReferenceSourcePrefixHistoryFiltration.entry
        rate rewards C_star C_h b t source).map Prod.fst = some true} ∩
      {source | i ∈ ReferenceSourcePrefixHistoryFiltration.pending
        rate rewards C_star C_h b t source})
  exact hentrySet.inter hpendingSet

theorem actualReleaseSupportIndicator_measurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Measurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (actualReleaseSupportIndicator rate rewards C_star C_h b t i) := by
  exact measurable_const.indicator
    (actualReleaseSupport_measurableSet rate rewards C_star C_h control0 b t i)

theorem actualReleaseSupportIndicator_stronglyMeasurable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1)) :
    StronglyMeasurable[ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1)]
      (actualReleaseSupportIndicator rate rewards C_star C_h b t i) :=
  (actualReleaseSupportIndicator_measurable
    rate rewards C_star C_h control0 b t i).stronglyMeasurable

theorem actualReleaseSupportIndicator_bounds
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1))
    (source : SourceInput p) :
    0 ≤ actualReleaseSupportIndicator rate rewards C_star C_h b t i source ∧
      actualReleaseSupportIndicator rate rewards C_star C_h b t i source ≤ 1 := by
  by_cases h : source ∈ actualReleaseSupport rate rewards C_star C_h b t i
  · simp [actualReleaseSupportIndicator, Set.indicator, h]
  · simp [actualReleaseSupportIndicator, Set.indicator, h]

private theorem outcomeField_le_sourceBorel (control0 : TimeControl p)
    (t : Fin p.T) :
    ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) := by
  rw [sourcePrefixField_eq_m_t control0 t]
  exact (ReferenceSourceCurrentControlFreshness.measurable_c_t
    (p := p) control0 t).comap_le

theorem actualReleaseSupportIndicator_integrable
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (b : ℕ) (t : Fin p.T) (i : Fin (p.m - 1)) :
    Integrable (actualReleaseSupportIndicator rate rewards C_star C_h b t i)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hmeas : Measurable (actualReleaseSupportIndicator
      rate rewards C_star C_h b t i) :=
    (actualReleaseSupportIndicator_measurable
      rate rewards C_star C_h control0 b t i).mono
        (outcomeField_le_sourceBorel control0 t) le_rfl
  apply integrable_measurable_norm_le_one _ hmeas
  intro source
  by_cases h : source ∈ actualReleaseSupport rate rewards C_star C_h b t i
  · simp [actualReleaseSupportIndicator, Set.indicator, h]
  · simp [actualReleaseSupportIndicator, Set.indicator, h]

theorem actual_up_release_support_condExp_pullout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (b : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun source => actualReleaseSupportIndicator rate rewards C_star C_h b t i source *
        (if ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun source => actualReleaseSupportIndicator rate rewards C_star C_h b t i source *
        actualUpControlSection rate rewards C_star C_h control0 i t source := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let G := actualReleaseSupportIndicator rate rewards C_star C_h b t i
  let X := fun source =>
    if ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t source
    then (1 : ℝ) else 0
  have hGsm := actualReleaseSupportIndicator_stronglyMeasurable
    rate rewards C_star C_h control0 b t i
  have hXint := actualUp_observation_integrable
    rate rewards C_star C_h control0 i t
  have hGmeas : Measurable G := hGsm.measurable.mono
    (outcomeField_le_sourceBorel control0 t) le_rfl
  have hXmeas : Measurable X :=
    actualBoolIndicator_measurable (actualUp_measurable
      rate rewards C_star C_h control0 i t)
  have hprodMeas : Measurable (fun source => G source * X source) :=
    hGmeas.mul hXmeas
  have hprodBound : ∀ source, ‖G source * X source‖ ≤ 1 := by
    intro source
    by_cases hs : source ∈ actualReleaseSupport rate rewards C_star C_h b t i
    · by_cases hx : ReferenceSourcePrefixHistoryFiltration.actualUp
          rate rewards C_star C_h i t source
      · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs, hx]
      · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs, hx]
    · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs]
  have hprodInt : Integrable (fun source => G source * X source) μ :=
    integrable_measurable_norm_le_one _ hprodMeas hprodBound
  have hpull := condExp_mul_of_stronglyMeasurable_left hGsm hprodInt hXint
  refine hpull.trans ?_
  filter_upwards [actual_up_condExp rate rewards C_star C_h control0 i t]
    with source hsource
  have hsource' : μ[X |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] source =
        actualUpControlSection rate rewards C_star C_h control0 i t source := by
    simpa only [X] using hsource
  change G source *
      μ[X | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] source =
    G source * actualUpControlSection rate rewards C_star C_h control0 i t source
  rw [hsource']

theorem actual_data_release_support_condExp_pullout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (b : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun source => actualReleaseSupportIndicator rate rewards C_star C_h b t i source *
        (if ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun source => actualReleaseSupportIndicator rate rewards C_star C_h b t i source *
        actualDataControlSection rate rewards C_star C_h control0 i t source := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let G := actualReleaseSupportIndicator rate rewards C_star C_h b t i
  let X := fun source =>
    if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t source
    then (1 : ℝ) else 0
  have hGsm := actualReleaseSupportIndicator_stronglyMeasurable
    rate rewards C_star C_h control0 b t i
  have hXint := actualData_observation_integrable
    rate rewards C_star C_h control0 i t
  have hGmeas : Measurable G := hGsm.measurable.mono
    (outcomeField_le_sourceBorel control0 t) le_rfl
  have hXmeas : Measurable X :=
    actualBoolIndicator_measurable (actualData_measurable
      rate rewards C_star C_h control0 i t)
  have hprodMeas : Measurable (fun source => G source * X source) :=
    hGmeas.mul hXmeas
  have hprodBound : ∀ source, ‖G source * X source‖ ≤ 1 := by
    intro source
    by_cases hs : source ∈ actualReleaseSupport rate rewards C_star C_h b t i
    · by_cases hx : ReferenceSourcePrefixHistoryFiltration.actualData
          rate rewards C_star C_h i t source
      · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs, hx]
      · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs, hx]
    · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs]
  have hprodInt : Integrable (fun source => G source * X source) μ :=
    integrable_measurable_norm_le_one _ hprodMeas hprodBound
  have hpull := condExp_mul_of_stronglyMeasurable_left hGsm hprodInt hXint
  refine hpull.trans ?_
  filter_upwards [actual_data_condExp rate rewards C_star C_h control0 i t]
    with source hsource
  have hsource' : μ[X |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] source =
        actualDataControlSection rate rewards C_star C_h control0 i t source := by
    simpa only [X] using hsource
  change G source *
      μ[X | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] source =
    G source * actualDataControlSection rate rewards C_star C_h control0 i t source
  rw [hsource']

theorem actual_release_release_support_condExp_pullout
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (b : ℕ) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun source => actualReleaseSupportIndicator rate rewards C_star C_h b t i source *
        (if ReferenceSourcePrefixHistoryFiltration.actualRelease
          rate rewards C_star C_h i t source then (1 : ℝ) else 0)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[
            BootstrapPrivateRoundStreams.sourceInputLaw p]
      fun source => actualReleaseSupportIndicator rate rewards C_star C_h b t i source *
        actualReleaseControlSection rate rewards C_star C_h control0 i t source := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let G := actualReleaseSupportIndicator rate rewards C_star C_h b t i
  let X := fun source =>
    if ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t source
    then (1 : ℝ) else 0
  have hGsm := actualReleaseSupportIndicator_stronglyMeasurable
    rate rewards C_star C_h control0 b t i
  have hXint := actualRelease_observation_integrable
    rate rewards C_star C_h control0 i t
  have hGmeas : Measurable G := hGsm.measurable.mono
    (outcomeField_le_sourceBorel control0 t) le_rfl
  have hXmeas : Measurable X :=
    actualBoolIndicator_measurable (actualRelease_measurable
      rate rewards C_star C_h control0 i t)
  have hprodMeas : Measurable (fun source => G source * X source) :=
    hGmeas.mul hXmeas
  have hprodBound : ∀ source, ‖G source * X source‖ ≤ 1 := by
    intro source
    by_cases hs : source ∈ actualReleaseSupport rate rewards C_star C_h b t i
    · by_cases hx : ReferenceSourcePrefixHistoryFiltration.actualRelease
          rate rewards C_star C_h i t source
      · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs, hx]
      · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs, hx]
    · simp [G, X, actualReleaseSupportIndicator, Set.indicator, hs]
  have hprodInt : Integrable (fun source => G source * X source) μ :=
    integrable_measurable_norm_le_one _ hprodMeas hprodBound
  have hpull := condExp_mul_of_stronglyMeasurable_left hGsm hprodInt hXint
  refine hpull.trans ?_
  filter_upwards [actual_release_condExp rate rewards C_star C_h control0 i t]
    with source hsource
  have hsource' : μ[X |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] source =
        actualReleaseControlSection rate rewards C_star C_h control0 i t source := by
    simpa only [X] using hsource
  change G source *
      μ[X | ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] source =
    G source * actualReleaseControlSection rate rewards C_star C_h control0 i t source
  rw [hsource']

end Bandits.Support.ReferenceSourcePhysicalFlagConditionalLaw

end
