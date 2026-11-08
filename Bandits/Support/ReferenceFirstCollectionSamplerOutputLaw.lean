/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCalendarCollectionCallControlLaw
public import Bandits.Support.ReferenceCalendarLaterSamplerOutputSections

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# First actual collection-sampler output law

This module observes the first actual parameter call and retains its original
absence branch, later output diagnostics, and entire continuous assignment
vector. Cellwise identities use the exact original source-prefix filtration.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionSamplerOutputLaw

abbrev SourceInput (p : ConstructorDimensions.Parameters) :=
  BootstrapPrivateRoundStreams.SourceInput p

abbrev FullOutput (p : ConstructorDimensions.Parameters) :=
  LaterAssignmentFullOutputMeasurability.FullOutputObservation p

abbrev AssignmentVector (p : ConstructorDimensions.Parameters) :=
  CheckedAssignmentSample.AssignmentVector p

abbrev FirstStratum (p : ConstructorDimensions.Parameters) :=
  Option (FullOutput p) × AssignmentVector p

/-- The actual first-call observation space, with a distinct outer no-call
branch and the complete full-output/vector payload on every called branch. -/
abbrev Yfirst (p : ConstructorDimensions.Parameters) :=
  Option (Fin p.T × (Fin p.T × FirstStratum p))

local instance sourceInputMeasurableSpace (p : ConstructorDimensions.Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

variable {p : ConstructorDimensions.Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ)

/-- Read the entire assignment-coordinate vector from the actual selected row
at a fixed calendar time. -/
def currentAssignmentVector (t : Fin p.T) (z : SourceInput p) :
    AssignmentVector p :=
  ContinuousControlSlice.assignmentVector
    (ReferenceSourceCurrentControlFreshness.u_t p t z).1

/-- The first actual sampler invocation, mapped to its literal full-output and
whole-vector observation. No-call and all inner output tags are preserved. -/
def firstOutput (z : SourceInput p) : Yfirst p :=
  (ReferenceFirstCollectionSamplerCall.firstCollectionCall rate rewards C_star C_h z).map
    (fun c => (c.1, (c.2.1,
      (ReferenceCalendarLaterSamplerOutputSections.outputAt
        rate rewards C_star C_h c.2.1 z,
        currentAssignmentVector c.2.1 z))))

/-- The event that the actual first-call observer returned no invocation. -/
def firstOutputNoCallEvent : Set (SourceInput p) :=
  {z | ReferenceFirstCollectionSamplerCall.firstCollectionCall
    rate rewards C_star C_h z = none}

/-- The Borel stratum of a first-output test for a fixed original cutoff/date. -/
def firstOutputStratumSet (B : Set (Yfirst p)) (u t : Fin p.T) :
    Set (FirstStratum p) :=
  {y | some (u, (t, y)) ∈ B}

/-- The literal full-output/vector Borel test at one calendar date. -/
def firstOutputPair (t : Fin p.T) (z : SourceInput p) : FirstStratum p :=
  (ReferenceCalendarLaterSamplerOutputSections.outputAt
      rate rewards C_star C_h t z,
    currentAssignmentVector t z)

/-- A stratum test evaluated on the unchanged original source. -/
def firstOutputTest (B : Set (FirstStratum p)) (t : Fin p.T)
    (z : SourceInput p) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    (firstOutputPair rate rewards C_star C_h t z)

private theorem firstCell_global_measurable (u t : Fin p.T) :
    MeasurableSet
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) := by
  simpa only [ReferenceCalendarCollectionCallControlLaw.firstCell] using
    ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_cell
      rate rewards C_star C_h u t

/-- Membership in the original first-call cell is exactly the original call's
cutoff/date tag. -/
theorem mem_firstCell_iff_originalTags (u t : Fin p.T) (z : SourceInput p) :
    z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t ↔
      (ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t) := by
  rfl

/-- Distinct cutoff/date tags give disjoint original first-call cells. -/
theorem firstCell_disjoint_of_ne (u t u' t' : Fin p.T)
    (h : (u, t) ≠ (u', t')) :
    Disjoint
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t)
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u' t') := by
  refine Set.disjoint_left.mpr ?_
  intro z hz hz'
  have htag := (mem_firstCell_iff_originalTags rate rewards C_star C_h u t z).mp hz
  have htag' := (mem_firstCell_iff_originalTags rate rewards C_star C_h u' t' z).mp hz'
  have hpair : (u, t) = (u', t') :=
    Option.some.inj (htag.symm.trans htag')
  exact h hpair

/-- The original cells cover every source with an actual call, and exactly one
cutoff/date cell contains it. -/
theorem firstCell_cover_or_noCall (z : SourceInput p) :
    z ∈ firstOutputNoCallEvent rate rewards C_star C_h ∨
      ∃ u t : Fin p.T,
        z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => exact Or.inl (by simp [firstOutputNoCallEvent, hcall])
  | some c =>
      refine Or.inr ⟨c.1, c.2.1, ?_⟩
      rw [mem_firstCell_iff_originalTags]
      rw [hcall]
      rfl

/-- The original no-call event is disjoint from every original first-call
cell. -/
theorem noCall_disjoint_firstCell (u t : Fin p.T) :
    Disjoint (firstOutputNoCallEvent rate rewards C_star C_h)
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t) := by
  refine Set.disjoint_left.mpr ?_
  intro z hnone hcell
  have htag := (mem_firstCell_iff_originalTags rate rewards C_star C_h u t z).mp hcell
  change ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z = none at hnone
  rw [hnone] at htag
  simp at htag

/-- The no-call event is Borel on the original source. -/
theorem firstOutputNoCallEvent_measurable :
    MeasurableSet (firstOutputNoCallEvent rate rewards C_star C_h) := by
  simpa only [firstOutputNoCallEvent] using
    ReferenceFirstCollectionSamplerCall.measurableSet_firstCollectionCall_none
      rate rewards C_star C_h

/-- Each fixed cutoff/date stratum of a Borel first-output test is Borel. -/
theorem firstOutputStratumSet_measurable (B : Set (Yfirst p))
    (hB : MeasurableSet B) (u t : Fin p.T) :
    MeasurableSet (firstOutputStratumSet B u t) := by
  apply hB.preimage
  exact LaterAssignmentFullOutputMeasurability.measurable_some_of_measurable
    (fun y : FirstStratum p => (u, (t, y)))
    (measurable_const.prodMk (measurable_const.prodMk measurable_id))

private theorem currentAssignmentVector_measurable (t : Fin p.T) :
    Measurable (currentAssignmentVector t) := by
  exact (ContinuousControlSlice.measurable_assignmentVector p.m p.K).comp
    (measurable_fst.comp
      (ReferenceSourceCurrentControlFreshness.measurable_u_t (p := p) t))

/-- The full output/vector pair at a fixed date is Borel on the original source. -/
theorem firstOutputPair_measurable (t : Fin p.T) :
    Measurable (firstOutputPair rate rewards C_star C_h t) := by
  exact (ReferenceCalendarLaterSamplerOutputSections.measurable_outputAt
    rate rewards C_star C_h t).prodMk
      (currentAssignmentVector_measurable t)

/-- The first-output map has the literal finite-cell preimage decomposition.
The cell tags and their payload are read from the same original call. -/
theorem firstOutput_preimage_eq (B : Set (Yfirst p)) :
    firstOutput rate rewards C_star C_h ⁻¹' B =
      (if none ∈ B then firstOutputNoCallEvent rate rewards C_star C_h else ∅) ∪
        ⋃ u : Fin p.T, ⋃ t : Fin p.T,
          ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t ∩
            (firstOutputPair rate rewards C_star C_h t ⁻¹'
              firstOutputStratumSet B u t) := by
  ext z
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      have hcellnone (u t : Fin p.T) :
          z ∉ ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t := by
        intro hz
        have htag := (mem_firstCell_iff_originalTags
          rate rewards C_star C_h u t z).mp hz
        rw [hcall] at htag
        simp at htag
      simp [firstOutput, firstOutputNoCallEvent, hcall, hcellnone]
  | some c =>
      have hcelltags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t ↔ (c.1, c.2.1) = (u, t) := by
        rw [mem_firstCell_iff_originalTags]
        rw [hcall]
        simp
      simp [firstOutput, firstOutputNoCallEvent, firstOutputStratumSet,
        firstOutputPair, hcall, hcelltags]

/-- Borel measurability of the actual first-call observation on its existing
sum/product Borel spaces. -/
theorem firstOutput_measurable :
    Measurable (firstOutput rate rewards C_star C_h) := by
  intro B hB
  rw [firstOutput_preimage_eq rate rewards C_star C_h B]
  have hnone : MeasurableSet
      (if none ∈ B then firstOutputNoCallEvent rate rewards C_star C_h else ∅) := by
    by_cases h : none ∈ B
    · simpa [h] using firstOutputNoCallEvent_measurable rate rewards C_star C_h
    · simp [h]
  apply hnone.union
  refine MeasurableSet.iUnion fun u => MeasurableSet.iUnion fun t => ?_
  apply (firstCell_global_measurable rate rewards C_star C_h u t).inter
  exact (firstOutputPair_measurable rate rewards C_star C_h t)
    (firstOutputStratumSet_measurable B hB u t)

/-- The actual outer none branch is equivalent to absence of the original
first invocation. -/
theorem firstOutput_eq_none_iff_original_call_eq_none (z : SourceInput p) :
    firstOutput rate rewards C_star C_h z = none ↔
      ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z = none := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z <;> simp [firstOutput, hcall]

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

/-- The original first-cell test identity, using precisely its successor
source-prefix filtration. -/
theorem firstOutput_cell_condExp (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B : Set (FirstStratum p)) (hB : MeasurableSet B) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (firstOutputTest rate rewards C_star C_h B t) |
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 1)] =ᵐ[BootstrapPrivateRoundStreams.sourceInputLaw p]
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (ReferenceCalendarLaterSamplerOutputSections.vectorSection
          rate rewards C_star C_h t B) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell
    rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := firstOutputTest rate rewards C_star C_h B t
  let sectionValue := ReferenceCalendarLaterSamplerOutputSections.vectorSection
    rate rewards C_star C_h t B
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt : Integrable test μ := by
    exact integrable_indicator_one_comp (μ := μ)
      (firstOutputPair rate rewards C_star C_h t)
      (firstOutputPair_measurable rate rewards C_star C_h t) B hB
  have hsectionCE :=
    ReferenceCalendarLaterSamplerOutputSections.outputAt_vectorSection_condExp
      rate rewards C_star C_h control0 t B hB
  have hsectionCE' : μ[test | H (t.val + 1)] =ᵐ[μ] sectionValue := by
    change μ[(fun z => B.indicator (fun _ => (1 : ℝ))
      (firstOutputPair rate rewards C_star C_h t z)) |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
          control0 (t.val + 1)] =ᵐ[μ]
      ReferenceCalendarLaterSamplerOutputSections.vectorSection
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

/-- The imported full-output section is integrable on every original
first-call cell, including zero-mass cells. -/
theorem firstOutput_cell_section_integrable
    (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) (B : Set (FirstStratum p)) (hB : MeasurableSet B) :
    IntegrableOn
      (ReferenceCalendarLaterSamplerOutputSections.vectorSection
        rate rewards C_star C_h t B)
      (ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  exact (ReferenceCalendarLaterSamplerOutputSections.vectorSection_integrable
    rate rewards C_star C_h control0 t B hB).integrableOn

/-- Restricting the same original first-cell test to its cell gives the
unnormalized section integral; no cell mass is divided out. -/
theorem firstOutput_cell_integral (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T)
    (B : Set (FirstStratum p)) (hB : MeasurableSet B) :
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        firstOutputTest rate rewards C_star C_h B t z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
    ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t,
        ReferenceCalendarLaterSamplerOutputSections.vectorSection
          rate rewards C_star C_h t B z
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let cell := ReferenceCalendarCollectionCallControlLaw.firstCell
    rate rewards C_star C_h u t
  let H := ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
  let test := firstOutputTest rate rewards C_star C_h B t
  let sectionValue := ReferenceCalendarLaterSamplerOutputSections.vectorSection
    rate rewards C_star C_h t B
  have hcellField : MeasurableSet[H (t.val + 1)] cell :=
    ReferenceCalendarCollectionCallControlLaw.firstCell_measurable
      rate rewards C_star C_h control0 u t
  have hfieldLe : H (t.val + 1) ≤
      (inferInstance : MeasurableSpace (SourceInput p)) := H.le (t.val + 1)
  have hcellGlobal : MeasurableSet cell := hfieldLe _ hcellField
  have htestInt := integrable_indicator_one_comp (μ := μ)
    (firstOutputPair rate rewards C_star C_h t)
    (firstOutputPair_measurable rate rewards C_star C_h t) B hB
  have hrestrictedInt : Integrable (cell.indicator test) μ :=
    htestInt.indicator hcellGlobal
  have hce := firstOutput_cell_condExp rate rewards C_star C_h control0 u t B hB
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

/-- Pointwise reconstruction of the first-output test from the actual
no-invocation event and the original finite cutoff/date cell partition. -/
theorem firstOutput_indicator_reconstruction (B : Set (Yfirst p))
    (z : SourceInput p) :
    B.indicator (fun _ => (1 : ℝ)) (firstOutput rate rewards C_star C_h z) =
      (firstOutputNoCallEvent rate rewards C_star C_h).indicator
        (fun _ => B.indicator (fun _ => (1 : ℝ)) none) z +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
            (firstOutputTest rate rewards C_star C_h
              (firstOutputStratumSet B u t) t) z := by
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none =>
      simp [firstOutput, firstOutputNoCallEvent,
        firstOutputStratumSet, ReferenceCalendarCollectionCallControlLaw.firstCell,
        hcall]
  | some c =>
      let value : ℝ := B.indicator (fun _ => (1 : ℝ))
        (firstOutput rate rewards C_star C_h z)
      let u₀ : Fin p.T := c.1
      let t₀ : Fin p.T := c.2.1
      have hcelltags (u t : Fin p.T) :
          z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t ↔ (c.1, c.2.1) = (u, t) := by
        rw [mem_firstCell_iff_originalTags]
        rw [hcall]
        simp
      have htest_eq :
          firstOutputTest rate rewards C_star C_h
            (firstOutputStratumSet B u₀ t₀) t₀ z =
          B.indicator (fun _ => (1 : ℝ)) (firstOutput rate rewards C_star C_h z) := by
        simp only [firstOutputTest, Set.indicator, firstOutputStratumSet,
          Set.mem_ofPred_eq]
        simp [firstOutput, firstOutputPair, hcall, u₀, t₀]
        rfl
      have hterm (u t : Fin p.T) :
          (ReferenceCalendarCollectionCallControlLaw.firstCell
            rate rewards C_star C_h u t).indicator
            (firstOutputTest rate rewards C_star C_h
              (firstOutputStratumSet B u t) t) z =
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
              (firstOutputTest rate rewards C_star C_h
                (firstOutputStratumSet B u t) t) z) =
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
              (firstOutputTest rate rewards C_star C_h
                (firstOutputStratumSet B u t) t) z) = value := by
        simp_rw [hinner]
        simp [u₀]
      rw [hsum]
      simp [firstOutput, firstOutputNoCallEvent, hcall, value]

private theorem integrable_cellTest (B : Set (Yfirst p))
    (hB : MeasurableSet B) (u t : Fin p.T) :
    Integrable
      ((ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t).indicator
        (firstOutputTest rate rewards C_star C_h
          (firstOutputStratumSet B u t) t))
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hstratum := firstOutputStratumSet_measurable B hB u t
  have htest := integrable_indicator_one_comp
    (μ := BootstrapPrivateRoundStreams.sourceInputLaw p)
    (firstOutputPair rate rewards C_star C_h t)
    (firstOutputPair_measurable rate rewards C_star C_h t)
    (firstOutputStratumSet B u t) hstratum
  exact htest.indicator
    (firstCell_global_measurable rate rewards C_star C_h u t)

/-- The exact Borel-test mixture law of the actual first collection-sampler
invocation. All strata are finite, original, and unnormalized; no-call mass is
retained separately. -/
theorem firstOutput_borel_test_law
    (control0 : ContinuousLearningRows.TimeControl p)
    (B : Set (Yfirst p)) (hB : MeasurableSet B) :
    ∫ z, B.indicator (fun _ => (1 : ℝ))
        (firstOutput rate rewards C_star C_h z)
      ∂BootstrapPrivateRoundStreams.sourceInputLaw p =
      (BootstrapPrivateRoundStreams.sourceInputLaw p).real
          (firstOutputNoCallEvent rate rewards C_star C_h) *
        B.indicator (fun _ => (1 : ℝ)) none +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
              rate rewards C_star C_h u t,
            ReferenceCalendarLaterSamplerOutputSections.vectorSection
              rate rewards C_star C_h t
              (firstOutputStratumSet B u t) z
            ∂BootstrapPrivateRoundStreams.sourceInputLaw p := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let noneValue : ℝ := B.indicator (fun _ => (1 : ℝ)) none
  let noneTerm : SourceInput p → ℝ :=
    (firstOutputNoCallEvent rate rewards C_star C_h).indicator (fun _ => noneValue)
  let cellTerm (u t : Fin p.T) : SourceInput p → ℝ :=
    (ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t).indicator
      (firstOutputTest rate rewards C_star C_h
        (firstOutputStratumSet B u t) t)
  have hnoneMeas := firstOutputNoCallEvent_measurable rate rewards C_star C_h
  have hnoneInt : Integrable noneTerm μ :=
    (integrable_const noneValue).indicator hnoneMeas
  have hcellInt (u t : Fin p.T) : Integrable (cellTerm u t) μ := by
    exact integrable_cellTest rate rewards C_star C_h B hB u t
  have hsumInt : Integrable
      (fun z => ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z) μ := by
    apply integrable_finsetSum
    intro u hu
    apply integrable_finsetSum
    intro t ht
    exact hcellInt u t
  have _hleftInt := integrable_indicator_one_comp (μ := μ)
    (firstOutput rate rewards C_star C_h)
    (firstOutput_measurable rate rewards C_star C_h) B hB
  have hpoint (z : SourceInput p) :
      B.indicator (fun _ => (1 : ℝ)) (firstOutput rate rewards C_star C_h z) =
        noneTerm z + ∑ u : Fin p.T, ∑ t : Fin p.T, cellTerm u t z := by
    simpa [noneTerm, cellTerm, noneValue] using
      firstOutput_indicator_reconstruction rate rewards C_star C_h B z
  have hnoneIntegral :
      ∫ z, noneTerm z ∂μ =
        μ.real (firstOutputNoCallEvent rate rewards C_star C_h) * noneValue := by
    change ∫ z, (firstOutputNoCallEvent rate rewards C_star C_h).indicator
      (fun _ => noneValue) z ∂μ = _
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
          ReferenceCalendarLaterSamplerOutputSections.vectorSection
            rate rewards C_star C_h t (firstOutputStratumSet B u t) z ∂μ := by
    rw [show cellTerm u t =
        (ReferenceCalendarCollectionCallControlLaw.firstCell
          rate rewards C_star C_h u t).indicator
          (firstOutputTest rate rewards C_star C_h
            (firstOutputStratumSet B u t) t) from rfl]
    rw [integral_indicator
      (firstCell_global_measurable rate rewards C_star C_h u t)]
    exact firstOutput_cell_integral rate rewards C_star C_h control0 u t
      (firstOutputStratumSet B u t)
      (firstOutputStratumSet_measurable B hB u t)
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
    _ = μ.real (firstOutputNoCallEvent rate rewards C_star C_h) * noneValue +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ∫ z in ReferenceCalendarCollectionCallControlLaw.firstCell
                rate rewards C_star C_h u t,
              ReferenceCalendarLaterSamplerOutputSections.vectorSection
                rate rewards C_star C_h t
                (firstOutputStratumSet B u t) z ∂μ := by
      rw [hnoneIntegral]
      congr 1
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      exact hcellMix u t

end Bandits.Support.ReferenceFirstCollectionSamplerOutputLaw

end
