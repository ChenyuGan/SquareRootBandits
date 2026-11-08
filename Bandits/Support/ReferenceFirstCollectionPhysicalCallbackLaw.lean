/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionSamplerOutputLaw
public import Bandits.Support.ReferenceCalendarActualControlCallbackSections

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Physical whole-control callback law for the first collection invocation

This observes the literal first collection call and projects its actual
round-record code together with the complete current control. Its strata are
the original first-call cells and retain the original no-call event.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionPhysicalCallbackLaw

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

abbrev Code (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  ReferenceActiveHorizonMeasurability.RoundRecordCode (p := p) (rate := rate)

/-- The first-call observation with its original cutoff/date and the actual
optional physical record code paired with the whole current control. -/
abbrev Y (p : ConstructorDimensions.Parameters)
    (rate : ReferenceActivePhysicalStep.RateInput p) :=
  Option (Fin p.T × (Fin p.T ×
    (Option (Code p rate) × ContinuousLearningRows.TimeControl p)))

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- The literal physical projection of the original first collection call.
The output code and current control are read at its actual date. -/
def firstPhysicalOutput (z : SourceInput p) : Y p rate :=
  (ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z).map
    (fun c => (c.1, (c.2.1,
      (ReferenceCalendarActualControlCallbackSections.codeAt
        rate rewards C_star C_h c.2.1 z,
        ReferenceSourceCurrentControlFreshness.u_t p c.2.1 z))))

/-- The physical-output test stratum for one original cutoff/date cell. -/
def firstPhysicalStratumSet (B : Set (Y p rate)) (u t : Fin p.T) :
    Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p) :=
  {y | some (u, (t, y)) ∈ B}

/-- The actual code/control pair at one fixed calendar date on the original
source. -/
def firstPhysicalPair (t : Fin p.T) (z : SourceInput p) :
    Option (Code p rate) × ContinuousLearningRows.TimeControl p :=
  (ReferenceCalendarActualControlCallbackSections.codeAt
    rate rewards C_star C_h t z,
    ReferenceSourceCurrentControlFreshness.u_t p t z)

/-- Evaluate a stratum test on the actual source code and whole control. -/
def firstPhysicalTest
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (t : Fin p.T) (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (firstPhysicalPair rate rewards C_star C_h t z)

/-- A Borel physical test induces Borel fixed-date slices in the existing
sum/product measurable spaces. -/
theorem firstPhysicalStratumSet_measurable (B : Set (Y p rate))
    (hB : MeasurableSet B) (u t : Fin p.T) :
    MeasurableSet (firstPhysicalStratumSet rate B u t) := by
  apply hB.preimage
  exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
    (fun y : Option (Code p rate) × ContinuousLearningRows.TimeControl p =>
      (u, (t, y)))
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

/-- The actual code/control pair is Borel by the actual physical code map and
the original whole-control coordinate map. -/
theorem firstPhysicalPair_measurable (t : Fin p.T) :
    Measurable (firstPhysicalPair rate rewards C_star C_h t) := by
  exact (ReferenceCalendarActualControlCallbackSections.measurable_codeAt
    rate rewards C_star C_h t).prodMk
      (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t)

private theorem integrable_indicator_one_comp {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure X}
    [IsProbabilityMeasure μ] (f : X → Y) (hf : Measurable f)
    (B : Set Y) (hB : MeasurableSet B) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) μ := by
  have hmeas : Measurable (fun x => B.indicator (fun _ => (1 : ℝ)) (f x)) :=
    (measurable_const.indicator hB).comp hf
  apply (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with x
  by_cases hx : f x ∈ B <;> simp [Set.indicator, hx]

/-- The actual first-call observation is Borel, using the original
first-call partition and no-call event. -/
theorem firstPhysicalOutput_preimage_eq (B : Set (Y p rate)) :
    firstPhysicalOutput rate rewards C_star C_h ⁻¹' B =
      (if none ∈ B then
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
          rate rewards C_star C_h else ∅) ∪
        ⋃ u : Fin p.T, ⋃ t : Fin p.T,
          ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t ∩
            (firstPhysicalPair rate rewards C_star C_h t ⁻¹'
              firstPhysicalStratumSet rate B u t) := by
  ext z
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hcellnone (u t : Fin p.T) :
          z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t := by
        intro hz
        have htag := (ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags
          rate rewards C_star C_h u t z).mp hz
        rw [hcall] at htag
        simp at htag
      simp [firstPhysicalOutput, firstPhysicalStratumSet,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        hcall, hcellnone]
  | some c =>
      have hcelltags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t ↔ (c.1, c.2.1) = (u, t) := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags]
        rw [hcall]
        simp
      simp [firstPhysicalOutput, firstPhysicalStratumSet, firstPhysicalPair,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        hcall, hcelltags]

/-- Borel measurability of the literal physical projection of the first call. -/
theorem firstPhysicalOutput_measurable :
    Measurable (firstPhysicalOutput rate rewards C_star C_h) := by
  intro B hB
  rw [firstPhysicalOutput_preimage_eq rate rewards C_star C_h B]
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
  have hcell : MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) := by
    simpa only [ReferenceCalendarCollectionCallControlLaw.firstCell] using
      ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
        rate rewards C_star C_h u t
  exact hcell.inter ((firstPhysicalPair_measurable rate rewards C_star C_h t)
    (firstPhysicalStratumSet_measurable rate B hB u t))

/-- The outer `none` tag is exactly absence of the original first invocation. -/
theorem firstPhysicalOutput_eq_none_iff_original_call_eq_none (z : SourceInput p) :
    firstPhysicalOutput rate rewards C_star C_h z = none ↔
      ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z = none := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;> simp [firstPhysicalOutput, hcall]

/-- The exact fixed-cell conditional-expectation identity for the actual
physical code and whole current-control test. -/
theorem firstPhysical_cell_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (firstPhysicalTest rate rewards C_star C_h B t) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (ReferenceCalendarActualControlCallbackSections.callbackSection
          rate rewards C_star C_h t B) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell
    rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := firstPhysicalTest rate rewards C_star C_h B t
  let sectionValue := ReferenceCalendarActualControlCallbackSections.callbackSection
    rate rewards C_star C_h t B
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have hpairMeasurable := firstPhysicalPair_measurable rate rewards C_star C_h t
  have htestInt : Integrable test μ := by
    exact integrable_indicator_one_comp
      (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
      (firstPhysicalPair rate rewards C_star C_h t) hpairMeasurable B hB
  have hsectionCE :=
    ReferenceCalendarActualControlCallbackSections.codeAt_controlSection_condExp
      rate rewards C_star C_h control0 t B hB
  have hsectionCE' : μ[test | H (t.val + 1)] =ᵐ[μ] sectionValue := by
    change (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (fun z => B.indicator (fun _ => (1 : ℝ))
        (ReferenceCalendarActualControlCallbackSections.codeAt
          rate rewards C_star C_h t z,
          ReferenceSourceCurrentControlFreshness.u_t p t z)) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      ReferenceCalendarActualControlCallbackSections.callbackSection
        rate rewards C_star C_h t B
    exact hsectionCE
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

/-- Each physical callback section is integrable on the original cell,
including zero-mass strata. -/
theorem firstPhysical_callbackSection_stronglyMeasurable
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    StronglyMeasurable[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)]
      (ReferenceCalendarActualControlCallbackSections.callbackSection
        rate rewards C_star C_h t B) :=
  ReferenceCalendarActualControlCallbackSections.callbackSection_stronglyMeasurable
    rate rewards C_star C_h control0 t B hB

/-- Pointwise unit bounds for each callback section. -/
theorem firstPhysical_callbackSection_bounds
    (t : Fin p.T)
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) (z : SourceInput p) :
    0 ≤ ReferenceCalendarActualControlCallbackSections.callbackSection
        rate rewards C_star C_h t B z ∧
      ReferenceCalendarActualControlCallbackSections.callbackSection
        rate rewards C_star C_h t B z ≤ 1 :=
  ReferenceCalendarActualControlCallbackSections.callbackSection_bounds
    rate rewards C_star C_h t B hB z

/-- Integrability of each whole-control callback section on the original
source measure. -/
theorem firstPhysical_callbackSection_integrable
    (control0 : ContinuousLearningRows.TimeControl p)
    (t : Fin p.T)
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    Integrable
      (ReferenceCalendarActualControlCallbackSections.callbackSection
        rate rewards C_star C_h t B)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
  ReferenceCalendarActualControlCallbackSections.callbackSection_integrable
    rate rewards C_star C_h control0 t B hB

/-- Each physical callback section is integrable on the original cell,
including zero-mass strata. -/
theorem firstPhysical_cell_section_integrable
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    IntegrableOn
      (ReferenceCalendarActualControlCallbackSections.callbackSection
        rate rewards C_star C_h t B)
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (firstPhysical_callbackSection_integrable
    rate rewards C_star C_h control0 t B hB).integrableOn

/-- Restricting the original pair test to its first-call cell gives exactly
the unnormalized callback-section integral over that same cell. -/
theorem firstPhysical_cell_integral (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B : Set (Option (Code p rate) × ContinuousLearningRows.TimeControl p))
    (hB : MeasurableSet B) :
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        firstPhysicalTest rate rewards C_star C_h B t z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        ReferenceCalendarActualControlCallbackSections.callbackSection
          rate rewards C_star C_h t B z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell
    rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := firstPhysicalTest rate rewards C_star C_h B t
  let sectionValue := ReferenceCalendarActualControlCallbackSections.callbackSection
    rate rewards C_star C_h t B
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt := integrable_indicator_one_comp
    (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (firstPhysicalPair rate rewards C_star C_h t)
    (firstPhysicalPair_measurable rate rewards C_star C_h t) B hB
  have hrestrictedInt : Integrable (cell.indicator test) μ :=
    htestInt.indicator hcellGlobal
  have hce := firstPhysical_cell_condExp rate rewards C_star C_h
    control0 u t B hB
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

/-- Pointwise reconstruction of a physical first-call test from the original
no-call event and the original cutoff/date partition. -/
theorem firstPhysical_indicator_reconstruction (B : Set (Y p rate))
    (z : SourceInput p) :
    B.indicator (fun _ => (1 : ℝ))
        (firstPhysicalOutput rate rewards C_star C_h z) =
      (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
        rate rewards C_star C_h).indicator
          (fun _ => B.indicator (fun _ => (1 : ℝ)) none) z +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
            (firstPhysicalTest rate rewards C_star C_h
              (firstPhysicalStratumSet rate B u t) t) z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      simp [firstPhysicalOutput,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        firstPhysicalStratumSet,
        ReferenceCalendarCollectionCallControlLaw.firstCell, hcall]
  | some c =>
      let value : ℝ := B.indicator (fun _ => (1 : ℝ))
        (firstPhysicalOutput rate rewards C_star C_h z)
      let u₀ : Fin p.T := c.1
      let t₀ : Fin p.T := c.2.1
      have hcelltags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t ↔ (c.1, c.2.1) = (u, t) := by
        rw [ReferenceFirstCollectionSamplerOutputLaw.mem_firstCell_iff_originalTags]
        rw [hcall]
        simp
      have htest_eq :
          firstPhysicalTest rate rewards C_star C_h
            (firstPhysicalStratumSet rate B u₀ t₀) t₀ z =
          B.indicator (fun _ => (1 : ℝ))
            (firstPhysicalOutput rate rewards C_star C_h z) := by
        simp only [firstPhysicalTest, Set.indicator,
          firstPhysicalStratumSet, Set.mem_ofPred_eq]
        simp [firstPhysicalOutput, firstPhysicalPair, hcall, u₀, t₀]
        rfl
      have hterm (u t : Fin p.T) :
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
            (firstPhysicalTest rate rewards C_star C_h
              (firstPhysicalStratumSet rate B u t) t) z =
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
              (firstPhysicalTest rate rewards C_star C_h
                (firstPhysicalStratumSet rate B u t) t) z) =
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
              (firstPhysicalTest rate rewards C_star C_h
                (firstPhysicalStratumSet rate B u t) t) z) = value := by
        simp_rw [hinner]
        simp [u₀]
      rw [hsum]
      simp [firstPhysicalOutput,
        ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent,
        hcall, value]

private theorem firstPhysical_cellTest_integrable (B : Set (Y p rate))
    (hB : MeasurableSet B) (u t : Fin p.T) :
    Integrable
      ((ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (firstPhysicalTest rate rewards C_star C_h
          (firstPhysicalStratumSet rate B u t) t))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hstratum := firstPhysicalStratumSet_measurable rate B hB u t
  have htest := integrable_indicator_one_comp
    (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (firstPhysicalPair rate rewards C_star C_h t)
    (firstPhysicalPair_measurable rate rewards C_star C_h t)
    (firstPhysicalStratumSet rate B u t) hstratum
  have hcell : MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) := by
    simpa only [ReferenceCalendarCollectionCallControlLaw.firstCell] using
      ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
        rate rewards C_star C_h u t
  exact htest.indicator hcell

/-- Exact Borel-test law of the physical full-control observation of the
original first sampler call. Every original stratum is retained
unnormalized, including zero-mass strata and the no-call event. -/
theorem firstPhysical_borel_test_law
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (Y p rate)) (hB : MeasurableSet B) :
    ∫ z, B.indicator (fun _ => (1 : ℝ))
        (firstPhysicalOutput rate rewards C_star C_h z)
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
            rate rewards C_star C_h) *
        B.indicator (fun _ => (1 : ℝ)) none +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t,
            ReferenceCalendarActualControlCallbackSections.callbackSection
              rate rewards C_star C_h t
              (firstPhysicalStratumSet rate B u t) z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let noneValue : ℝ := B.indicator (fun _ => (1 : ℝ)) none
  let noneEvent := ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent
    rate rewards C_star C_h
  let noneTerm : SourceInput p → ℝ := noneEvent.indicator (fun _ => noneValue)
  let cellTerm (u t : Fin p.T) : SourceInput p → ℝ :=
    (ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t).indicator
      (firstPhysicalTest rate rewards C_star C_h
        (firstPhysicalStratumSet rate B u t) t)
  have hnoneMeas :=
    ReferenceFirstCollectionSamplerOutputLaw.firstOutputNoCallEvent_measurable
      rate rewards C_star C_h
  have hnoneInt : Integrable noneTerm μ :=
    (integrable_const noneValue).indicator hnoneMeas
  have hcellInt (u t : Fin p.T) : Integrable (cellTerm u t) μ := by
    exact firstPhysical_cellTest_integrable rate rewards C_star C_h B hB u t
  have hsumInt : Integrable
      (fun z => ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) μ := by
    apply integrable_finsetSum
    intro u hu
    apply integrable_finsetSum
    intro t ht
    exact hcellInt u t
  have _hleftInt := integrable_indicator_one_comp
    (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (firstPhysicalOutput rate rewards C_star C_h)
    (firstPhysicalOutput_measurable rate rewards C_star C_h) B hB
  have hpoint (z : SourceInput p) :
      B.indicator (fun _ => (1 : ℝ))
          (firstPhysicalOutput rate rewards C_star C_h z) =
        noneTerm z + ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z := by
    simpa [noneTerm, noneEvent, cellTerm, noneValue] using
      firstPhysical_indicator_reconstruction rate rewards C_star C_h B z
  have hnoneIntegral :
      ∫ z, noneTerm z ∂μ = μ.real noneEvent * noneValue := by
    change ∫ z, noneEvent.indicator (fun _ => noneValue) z ∂μ = _
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
          ReferenceCalendarActualControlCallbackSections.callbackSection
            rate rewards C_star C_h t
            (firstPhysicalStratumSet rate B u t) z ∂μ := by
    rw [show cellTerm u t =
        (ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t).indicator
          (firstPhysicalTest rate rewards C_star C_h
            (firstPhysicalStratumSet rate B u t) t) from rfl]
    have hcell : MeasurableSet
        (ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t) := by
      simpa only [ReferenceCalendarCollectionCallControlLaw.firstCell] using
        ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
          rate rewards C_star C_h u t
    rw [integral_indicator hcell]
    exact firstPhysical_cell_integral rate rewards C_star C_h control0 u t
      (firstPhysicalStratumSet rate B u t)
      (firstPhysicalStratumSet_measurable rate B hB u t)
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
    _ = μ.real noneEvent * noneValue +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t,
              ReferenceCalendarActualControlCallbackSections.callbackSection
                rate rewards C_star C_h t
                (firstPhysicalStratumSet rate B u t) z ∂μ := by
      rw [hnoneIntegral]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      exact hcellMix u t

end Bandits.Support.ReferenceFirstCollectionPhysicalCallbackLaw

end
