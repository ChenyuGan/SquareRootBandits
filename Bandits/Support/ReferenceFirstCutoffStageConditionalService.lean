/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceCutoffStageSupportMeasurability
public import Bandits.Support.ReferenceFirstCutoffDownConditionalService

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Lean.Elab.Tactic.Omega

/-!
# Actual first-cutoff OLD/formed-UP stage service

This module joins the literal OLD-DOWN and formed-UP cutoff supports into one
before-current analytic observation and proves its conditional rate at the
actual first cutoff. It retains the original source law, continuous controls,
and the source's fixed rate, whole reward table, and unrestricted thresholds.

Sources: `sources/zip4/manuscript/06_interruptions.tex:425-426,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108`.
This is only the B[0] service adapter. It does not prove the stopped 4Q quota,
waiting bound, all-calendar coverage, manuscript-filtration equality, or main
regret theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCutoffStageConditionalService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev RoundRecord (p : Parameters) (rate : RateInput p) :=
  ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)
abbrev DownWord (p : Parameters) :=
  AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev UpRecord (p : Parameters) (rate : RateInput p) :=
  OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  exact Prod.instMeasurableSpace

variable {p : Parameters} {rate : RateInput p}

/-- The literal union of all existing fixed-word OLD-DOWN supports. -/
def cutoffOldStageSupport (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) : Set (SourceInput p) :=
  ⋃ w : DownWord p,
    ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t w

/-- The literal union of all existing typed formed-UP supports. -/
def cutoffFormedUpStageSupport (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) : Set (SourceInput p) :=
  ⋃ reply : UpRecord p rate,
    ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t reply

/-- The staged analytic readout on the whole original source. -/
def stagedReadout (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) : ℝ :=
  (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t) source +
    (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t) source

/-- Countable-union Borelness in the exact fixed-time field. -/
theorem measurableSet_cutoffOldStageSupport (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t) := by
  classical
  exact MeasurableSet.iUnion fun w =>
    ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport_measurableSet
      (p := p) (rate := rate) rewards C_star C_h control0 i t w

/-- Countable-union Borelness in the exact fixed-time field. -/
theorem measurableSet_cutoffFormedUpStageSupport (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t) := by
  classical
  exact MeasurableSet.iUnion fun reply =>
    ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport_measurableSet
      (p := p) (rate := rate) rewards C_star C_h control0 i t reply

/-- The OLD union retains the accepted source-prefix factorization. -/
theorem cutoffOldStageSupport_factor (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹'
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t ⁻¹'
          (⋃ w : DownWord p,
            ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupportCodeSet
              (p := p) (rate := rate) i t w)) := by
  ext source
  simp only [cutoffOldStageSupport, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨w, hsource⟩
    refine ⟨w, ?_⟩
    rw [ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport_factor
      (p := p) (rate := rate) rewards C_star C_h control0 i t w] at hsource
    exact hsource
  · rintro ⟨w, hsource⟩
    refine ⟨w, ?_⟩
    rw [ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport_factor
      (p := p) (rate := rate) rewards C_star C_h control0 i t w]
    exact hsource

/-- The formed-UP union retains the accepted source-prefix factorization. -/
theorem cutoffFormedUpStageSupport_factor (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t =
      ReferenceSourcePrefixHistoryFiltration.sourcePrefix control0 t.val ⁻¹'
        (ReferenceSourcePrefixHistoryFiltration.incoming rate rewards C_star C_h t ⁻¹'
          (⋃ reply : UpRecord p rate,
            ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupportCodeSet
              (p := p) (rate := rate) i t reply)) := by
  ext source
  simp only [cutoffFormedUpStageSupport, Set.mem_iUnion, Set.mem_preimage]
  constructor
  · rintro ⟨reply, hsource⟩
    refine ⟨reply, ?_⟩
    rw [ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport_factor
      (p := p) (rate := rate) rewards C_star C_h control0 i t reply] at hsource
    exact hsource
  · rintro ⟨reply, hsource⟩
    refine ⟨reply, ?_⟩
    rw [ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport_factor
      (p := p) (rate := rate) rewards C_star C_h control0 i t reply]
    exact hsource

/-- OLD membership is invariant under replacing any complete current control. -/
theorem cutoffOldStageSupport_replaceSourceControl_iff
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control ∈
        cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t ↔
      source ∈ cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t := by
  classical
  simp only [cutoffOldStageSupport, Set.mem_iUnion]
  constructor
  · rintro ⟨w, hsource⟩
    exact ⟨w,
      (ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport_replaceSourceControl_iff
        (p := p) (rate := rate) rewards C_star C_h i t w source control).mp hsource⟩
  · rintro ⟨w, hsource⟩
    exact ⟨w,
      (ReferenceCutoffStageSupportMeasurability.cutoffDownStageSupport_replaceSourceControl_iff
        (p := p) (rate := rate) rewards C_star C_h i t w source control).mpr hsource⟩

/-- Formed-UP membership is invariant under replacing any complete current control. -/
theorem cutoffFormedUpStageSupport_replaceSourceControl_iff
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (control : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t source control ∈
        cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t ↔
      source ∈ cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t := by
  classical
  simp only [cutoffFormedUpStageSupport, Set.mem_iUnion]
  constructor
  · rintro ⟨reply, hsource⟩
    exact ⟨reply,
      (ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport_replaceSourceControl_iff
        (p := p) (rate := rate) rewards C_star C_h i t reply source control).mp hsource⟩
  · rintro ⟨reply, hsource⟩
    exact ⟨reply,
      (ReferenceCutoffStageSupportMeasurability.cutoffUpStageSupport_replaceSourceControl_iff
        (p := p) (rate := rate) rewards C_star C_h i t reply source control).mpr hsource⟩

/-- OLD and formed-UP supports are disjoint: their unique actual incoming
record has one ordinary old follower, whose `lastDown` cannot be both absent
and have a positive accepted start. -/
theorem disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Disjoint
      (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t)
      (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t) := by
  classical
  rw [Set.disjoint_left]
  intro source hOld hFormed
  rcases Set.mem_iUnion.mp hOld with ⟨word, hOld⟩
  rcases Set.mem_iUnion.mp hFormed with ⟨reply, hFormed⟩
  rcases hOld with ⟨r, hrecord, registers, owned, base, hlive, hcutoff,
    hordinary, old, memory, hfocus, hnone, hword⟩
  rcases hFormed with ⟨r', hrecord', registers', owned', base', hlive', hcutoff',
    hordinary', old', memory', hfocus', hpositive, hfields⟩
  have hrecordEq : r = r' := Option.some.inj (hrecord.symm.trans hrecord')
  subst r'
  have hfollowerEq := hfocus.symm.trans hfocus'
  injection hfollowerEq with hold hmemory
  have hpositive' := hpositive
  rw [← hold] at hpositive'
  simp only [ReferencePrelaunchFollower.acceptedStart, hnone] at hpositive'
  omega

/-- On OLD support the staged readout is exactly the executed OLD readout. -/
theorem stagedReadout_eq_downReadout_of_mem_cutoffOldStageSupport
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (hOld : source ∈ cutoffOldStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t) :
    stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source =
      ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t source := by
  have hnotFormed : source ∉
      cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t := by
    intro hFormed
    exact (Set.disjoint_left.mp
      (disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed
  simp [stagedReadout, hOld, hnotFormed]

/-- On formed-UP support the staged readout is exactly the executed UP readout. -/
theorem stagedReadout_eq_upReadout_of_mem_cutoffFormedUpStageSupport
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (hFormed : source ∈ cutoffFormedUpStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t) :
    stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source =
      ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t source := by
  have hnotOld : source ∉
      cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t := by
    intro hOld
    exact (Set.disjoint_left.mp
      (disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed
  simp [stagedReadout, hnotOld, hFormed]

/-- The observation is zero away from both literal stage supports. -/
theorem stagedReadout_eq_zero_of_mem_compl_supports
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p)
    (hOld : source ∉ cutoffOldStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t)
    (hFormed : source ∉ cutoffFormedUpStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t) :
    stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source = 0 := by
  simp [stagedReadout, hOld, hFormed]

/-- The staged readout remains binary because its two supports are disjoint. -/
theorem stagedReadout_zero_or_one (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source = 0 ∨
      stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source = 1 := by
  classical
  have hDown := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout_zero_or_one
    (rate := rate) rewards C_star C_h i t source
  have hUp := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout_zero_or_one
    (rate := rate) rewards C_star C_h i t source
  by_cases hOld : source ∈ cutoffOldStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t
  · have hFormed : source ∉ cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t := by
      intro hFormed
      exact (Set.disjoint_left.mp
        (disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
          (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed
    rw [stagedReadout_eq_downReadout_of_mem_cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t source hOld]
    exact hDown
  · by_cases hFormed : source ∈ cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t
    · rw [stagedReadout_eq_upReadout_of_mem_cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t source hFormed]
      exact hUp
    · rw [stagedReadout_eq_zero_of_mem_compl_supports
        (p := p) (rate := rate) rewards C_star C_h i t source hOld hFormed]
      exact Or.inl rfl

/-- Pointwise bounds for the binary staged readout. -/
theorem stagedReadout_bounds (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (source : SourceInput p) :
    0 ≤ stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source ∧
      stagedReadout (p := p) (rate := rate) rewards C_star C_h i t source ≤ 1 := by
  rcases stagedReadout_zero_or_one (p := p) (rate := rate)
    rewards C_star C_h i t source with h | h <;> simp [h]

/-- The exact fixed-time field is contained in the source's ambient Borel field. -/
theorem m_t_le_sourceBorel (control0 : TimeControl p) (t : Fin p.T) :
    ReferenceSourceCurrentControlFreshness.m_t p control0 t ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
  (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comap_le

/-- The OLD union is ambient Borel measurable. -/
theorem measurableSet_cutoffOldStageSupport_ambient (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (cutoffOldStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t) :=
  m_t_le_sourceBorel (p := p) control0 t
    (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t)
    (measurableSet_cutoffOldStageSupport (p := p) (rate := rate)
      rewards C_star C_h control0 i t)

/-- The formed-UP union is ambient Borel measurable. -/
theorem measurableSet_cutoffFormedUpStageSupport_ambient (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet (cutoffFormedUpStageSupport (p := p) (rate := rate)
      rewards C_star C_h i t) :=
  m_t_le_sourceBorel (p := p) control0 t
    (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t)
    (measurableSet_cutoffFormedUpStageSupport (p := p) (rate := rate)
      rewards C_star C_h control0 i t)

/-- Ambient Borel measurability from the actual readouts and support Borelness. -/
theorem measurable_stagedReadout (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (stagedReadout (p := p) (rate := rate) rewards C_star C_h i t) := by
  have hOld := measurableSet_cutoffOldStageSupport_ambient
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hFormed := measurableSet_cutoffFormedUpStageSupport_ambient
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hDown := ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout
    (rate := rate) rewards C_star C_h i t
  have hUp := ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout
    (rate := rate) rewards C_star C_h i t
  exact (hDown.indicator hOld).add (hUp.indicator hFormed)

/-- On the original source law and the exact current-prefix field, conditional
expectation distributes over the two measurable stage indicators and reduces
to their existing fresh-control sections. -/
theorem stagedReadout_condExp (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      stagedReadout (p := p) (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
    fun source =>
      (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i t) source +
      (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i t) source := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let m := ReferenceSourceCurrentControlFreshness.m_t p control0 t
  let OLD := cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t
  let FORMED := cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t
  let XD := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
    (rate := rate) rewards C_star C_h i t
  let XU := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
    (rate := rate) rewards C_star C_h i t
  let XDfresh := ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
    (rate := rate) rewards C_star C_h control0 i t
  let XUfresh := ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
    (rate := rate) rewards C_star C_h control0 i t
  have hOLD : MeasurableSet[m] OLD := by
    exact measurableSet_cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hFORMED : MeasurableSet[m] FORMED := by
    exact measurableSet_cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hOLDambient : @MeasurableSet (SourceInput p)
      (sourceInputMeasurableSpace p) OLD :=
    m_t_le_sourceBorel (p := p) control0 t OLD hOLD
  have hFORMEDambient : @MeasurableSet (SourceInput p)
      (sourceInputMeasurableSpace p) FORMED :=
    m_t_le_sourceBorel (p := p) control0 t FORMED hFORMED
  have hXDint : Integrable XD μ := by
    exact ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  have hXUint : Integrable XU μ := by
    exact ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  have hOldInt : Integrable (OLD.indicator XD) μ := hXDint.indicator hOLDambient
  have hFormedInt : Integrable (FORMED.indicator XU) μ := hXUint.indicator hFORMEDambient
  have hAdd :
      μ[stagedReadout (p := p) (rate := rate) rewards C_star C_h i t | m] =ᵐ[μ]
        μ[OLD.indicator XD | m] + μ[FORMED.indicator XU | m] := by
    change μ[(OLD.indicator XD) + (FORMED.indicator XU) | m] =ᵐ[μ] _
    exact MeasureTheory.condExp_add hOldInt hFormedInt m
  have hOldInd := MeasureTheory.condExp_indicator hXDint hOLD
  have hFormedInd := MeasureTheory.condExp_indicator hXUint hFORMED
  have hDownCE :=
    ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp
      (rate := rate) rewards C_star C_h control0 i t
  have hUpCE :=
    ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp
      (rate := rate) rewards C_star C_h control0 i t
  filter_upwards [hAdd, hOldInd, hFormedInd, hDownCE, hUpCE]
    with source hAdd hOldInd hFormedInd hDownCE hUpCE
  have hOldSection : OLD.indicator (μ[XD | m]) source = OLD.indicator XDfresh source := by
    by_cases hmem : source ∈ OLD
    · simpa only [Set.indicator_of_mem hmem] using hDownCE
    · simp [Set.indicator_of_notMem hmem]
  have hFormedSection :
      FORMED.indicator (μ[XU | m]) source = FORMED.indicator XUfresh source := by
    by_cases hmem : source ∈ FORMED
    · simpa only [Set.indicator_of_mem hmem] using hUpCE
    · simp [Set.indicator_of_notMem hmem]
  calc
    μ[stagedReadout (p := p) (rate := rate) rewards C_star C_h i t | m] source =
        (μ[OLD.indicator XD | m] + μ[FORMED.indicator XU | m]) source := hAdd
    _ = OLD.indicator (μ[XD | m]) source + FORMED.indicator (μ[XU | m]) source := by
      change μ[OLD.indicator XD | m] source + μ[FORMED.indicator XU | m] source = _
      rw [hOldInd, hFormedInd]
    _ = OLD.indicator XDfresh source + FORMED.indicator XUfresh source := by
      rw [hOldSection, hFormedSection]

private theorem cutoff_cut_eq_of_same_actual_stream
    {source : SourceInput p} {rewards : RewardTable p} {C_star C_h : ℝ}
    {count : ℕ}
    {hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true}
    {hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + count ≤ p.T}
    {hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
        source rewards C_star C_h hcross count hspan).records).length < count}
    (d₁ d₂ : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
      (p := p) (rate := rate) source rewards C_star C_h count hcross hspan hshort) :
    d₁.stream.cutoff.cut = d₂.stream.cutoff.cut := by
  apply Option.some.inj
  exact d₁.stream.cutoff.cutIndex.symm.trans d₂.stream.cutoff.cutIndex

private theorem ordinaryFollower_eq_of_same_input
    {x y : ReferenceActivePhysicalStep.RoundInput p rate} (hxy : x = y)
    (old₁ old₂ : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta)
    (memory₁ memory₂ : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p)
    (hf₁ : ∀ j, x.state.followers j = .ordinary (old₁ j) (memory₁ j))
    (hf₂ : ∀ j, y.state.followers j = .ordinary (old₂ j) (memory₂ j)) :
    ∀ j, old₁ j = old₂ j ∧ memory₁ j = memory₂ j := by
  intro j
  have h₁ : y.state.followers j = .ordinary (old₁ j) (memory₁ j) := by
    rw [← hxy]
    exact hf₁ j
  have hfollower := h₁.symm.trans (hf₂ j)
  injection hfollower with hold hmemory
  exact ⟨hold, hmemory⟩

private theorem acceptedStart_pos_of_lastDown_ne_none
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (hlast : old.lastDown ≠ none) :
    1 ≤ ReferencePrelaunchFollower.acceptedStart old := by
  cases hdown : old.lastDown with
  | none => exact (hlast hdown).elim
  | some down =>
      have hproperty := down.property
      unfold OrdinaryMessageCodec.downAdmissible at hproperty
      simpa [ReferencePrelaunchFollower.acceptedStart, hdown] using hproperty.1

private theorem if_one_eq_if_of_iff {P Q : Prop} [Decidable P] [Decidable Q]
    (h : P ↔ Q) : (if P then (1 : ℝ) else 0) = if Q then 1 else 0 := by
  by_cases hP : P
  · rw [if_pos hP, if_pos (h.mp hP)]
  · have hQ : ¬ Q := fun hq => hP (h.mpr hq)
    rw [if_neg hP, if_neg hQ]

/-- The actual B[0] cutoff has exactly one predictable OLD/formed-UP stage,
and the joined readout has the source's native positive-reward-count service
rate. All fixed-time conditional-expectation versions are intersected over
finite follower/time indices before the random cutoff is evaluated.

The theorem retains the actual original-source dispatch and follower states;
it makes no assumption about stage truth, current-row service, successful
decoding, a future-good event, or a formation date. -/
theorem actual_first_cutoff_staged_service
    (rate : RateInput p) (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) :
    ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
    ∀ (count : ℕ)
      (hcross : (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
      (hspan : ReferenceFirstCollectionReadyStream.startTime (rate := rate)
        source rewards C_star C_h + count ≤ p.T)
      (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionReadyStream.actualEpoch (rate := rate)
          source rewards C_star C_h hcross count hspan).records).length < count),
    let E := ReferenceFirstCollectionReadyStream.actualEpoch
      (rate := rate) source rewards C_star C_h hcross count hspan
    let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
    let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
        source rewards C_star C_h count hcross hspan hshort,
    ∃ old : Fin (p.m - 1) → ReferencePrelaunchFollower.State p rate.eta,
    ∃ memory : Fin (p.m - 1) → ActiveFollowerLifecycle.LocalMemory p,
    ∃ cut : RoundRecord p rate, cut = d.stream.cutoff.cut ∧
    let x := cut.input
    d.stream.window = B ∧
    d.stream.window[0]'d.stream.windowNonempty = d.stream.cutoff.cut ∧
    x.time.val = ReferenceFirstCollectionReadyStream.startTime (rate := rate)
      source rewards C_star C_h + w ∧
    x.rows = source.1.2 ∧
    x.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
    x.rewards = rewards ∧
    ∃ (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
      (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
      (base : Fin (p.m - 1) → ℕ),
    x.state.coordinator = .live registers owned base ∧
    d.stream.payload = registers.payload ∧
    (∀ j, x.state.followers j = .ordinary (old j) (memory j) ∧
      let cj : ReferencePrelaunchFollower.State p rate.eta :=
        { old j with status := ActiveRoundActions.FollowerStatus.unoccupied }
      cj.lastDown = (old j).lastDown ∧
      cj.S = (old j).S ∧ cj.delta = (old j).delta ∧
      cj.backlog = (old j).backlog ∧ cj.buffer = (old j).buffer ∧
      cj.downBatch = (old j).downBatch ∧
      cj.initializationFailure = (old j).initializationFailure ∧
      ActiveFollowerLifecycle.localStateDomainValid cj ∧
      ActiveFollowerLifecycle.startRound rate.eta x.time (old j) (memory j) =
        .ok (cj, memory j)) ∧
    (∀ j, ((ReferenceActivePhysicalStep.prepare x).followers.followers j).configuration =
      .ordinary ({ old j with status := ActiveRoundActions.FollowerStatus.unoccupied })
        (memory j)) ∧
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      x.time source = some cut ∧
    ReferenceCollectionPhaseHistory.cutoffChosen x = true ∧
    (∃ dispatched : CoordinatorStartRoundCutoffDispatch.Output
        (ReferenceActivePhysicalStep.liveRegistersAt registers x.time)
        (ReferenceActivePhysicalStep.liveOwnedAt registers owned x.time) base,
      (∃ ledger, dispatched.collectionInitialization = .success (some ledger)) ∧
      dispatched.startResult.pending = Finset.univ ∧
      ∃ selection : ReferenceActivePhysicalStep.Selection x,
        (ReferenceActivePhysicalStep.prepare x).coordinator.selection = some selection ∧
        selection.view.payload = registers.payload ∧
        selection.started = dispatched.startResult ∧
        selection.view.pendingAtChoice = Finset.univ) ∧
    ∀ i : Fin (p.m - 1),
      (source ∈ cutoffOldStageSupport (p := p) (rate := rate)
          rewards C_star C_h i x.time ↔ (old i).lastDown = none) ∧
      (source ∈ cutoffFormedUpStageSupport (p := p) (rate := rate)
          rewards C_star C_h i x.time ↔ (old i).lastDown ≠ none) ∧
      ((old i).lastDown = none →
        stagedReadout (p := p) (rate := rate) rewards C_star C_h i x.time source =
          if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (x.row.2 x.time).1 =
                  ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
              ReferenceActiveAffinePositiveTest.downPositive x = true then 1 else 0) ∧
      ((old i).lastDown ≠ none →
        stagedReadout (p := p) (rate := rate) rewards C_star C_h i x.time source =
          if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (x.row.2 x.time).1 =
                  ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
              ReferenceActiveAffinePositiveTest.upPositive x = true then 1 else 0) ∧
      (BootstrapPrivateRoundStreams.sourceInputLaw p)[
        stagedReadout (p := p) (rate := rate) rewards C_star C_h i x.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 x.time] source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards x.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hDownReadoutCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (μ[ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t |
            ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i t source) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp
        (rate := rate) rewards C_star C_h control0 i t
  have hUpReadoutCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (μ[ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t |
            ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i t source) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp
        (rate := rate) rewards C_star C_h control0 i t
  have hreadoutCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      ((μ[ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i t source) ∧
       (μ[ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i t source)) := by
    filter_upwards [hDownReadoutCE, hUpReadoutCE] with source hDown hUp
    intro i t
    exact ⟨hDown i t, hUp i t⟩
  have hstageCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      (μ[stagedReadout (p := p) (rate := rate) rewards C_star C_h i t |
          ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i t) source +
        (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i t) source) :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      stagedReadout_condExp (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hDownRoot :=
    ReferenceFirstCutoffDownConditionalService.actual_first_cutoff_down_condExp_service
      (p := p) rate rewards C_star C_h control0
  have hUpRoot :=
    ReferenceFirstCutoffUpConditionalService.actual_first_cutoff_up_condExp_service
      (p := p) rate rewards C_star C_h control0
  filter_upwards [hDownRoot, hUpRoot, hreadoutCE, hstageCE]
    with source hDownRoot hUpRoot hreadoutCE hstageCE
  intro count hcross hspan hshort
  have hDownData := hDownRoot count hcross hspan hshort
  dsimp only at hDownData
  rcases hDownData with ⟨dDown, hwindow, hhead, htime, hrows, hselected, hreward,
    registersDown, ownedDown, baseDown, oldDown, memoryDown, hphaseDown,
    hpayloadDown, hfamilyDown, hserviceDown⟩
  have hUpData := hUpRoot count hcross hspan hshort
  dsimp only at hUpData
  rcases hUpData with ⟨dUp, oldUp, memoryUp, hfamilyUp, hserviceUp⟩
  have hSupportData :=
    ReferenceCutoffStageSupportMeasurability.actual_first_cutoff_stage_support
      (p := p) rate source rewards C_star C_h count hcross hspan hshort
  dsimp only at hSupportData
  rcases hSupportData with ⟨dSupport, oldSupport, memorySupport, hSupport⟩
  rcases hSupport with ⟨hfamilySupport, cutSupport, hcutSupport,
    registersSupport, ownedSupport, baseSupport, hrecordSupport,
    hphaseSupport, hcutoffSupport, hselectionSupport, hdownSupport, hupSupport⟩
  have hcutDownSupport := cutoff_cut_eq_of_same_actual_stream
    (p := p) (rate := rate) dDown dSupport
  have hcutDownUp := cutoff_cut_eq_of_same_actual_stream
    (p := p) (rate := rate) dDown dUp
  have hcutSupportDown : cutSupport = dDown.stream.cutoff.cut :=
    hcutSupport.trans hcutDownSupport.symm
  have hinputDownSupport : dDown.stream.cutoff.cut.input = dSupport.stream.cutoff.cut.input :=
    congrArg (fun record : RoundRecord p rate => record.input) hcutDownSupport
  have hinputDownUp : dDown.stream.cutoff.cut.input = dUp.stream.cutoff.cut.input :=
    congrArg (fun record : RoundRecord p rate => record.input) hcutDownUp
  have hordinaryDown : ∀ j, dDown.stream.cutoff.cut.input.state.followers j =
      .ordinary (oldDown j) (memoryDown j) := fun j => (hfamilyDown j).1
  have hordinarySupport : ∀ j, dSupport.stream.cutoff.cut.input.state.followers j =
      .ordinary (oldSupport j) (memorySupport j) := fun j => (hfamilySupport j).1
  have hordinaryUp : ∀ j, dUp.stream.cutoff.cut.input.state.followers j =
      .ordinary (oldUp j) (memoryUp j) := fun j => (hfamilyUp j).1
  have hStateSupport := ordinaryFollower_eq_of_same_input
    hinputDownSupport oldDown oldSupport memoryDown memorySupport
    hordinaryDown hordinarySupport
  have hStateUp := ordinaryFollower_eq_of_same_input
    hinputDownUp oldDown oldUp memoryDown memoryUp hordinaryDown hordinaryUp
  have hcoordinatorEq :
      ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          registersSupport ownedSupport baseSupport =
        ReferenceActivePhysicalStep.CoordinatorConfiguration.live
          registersDown ownedDown baseDown := by
    have hphaseSupportDown := hphaseSupport
    rw [hcutSupportDown] at hphaseSupportDown
    exact hphaseSupportDown.symm.trans hphaseDown
  have hregisters : registersSupport = registersDown := by
    injection hcoordinatorEq with hregisters _ _
  have hownedHEq : HEq ownedSupport ownedDown := by
    injection hcoordinatorEq with _ howned _
  have hbase : baseSupport = baseDown := by
    injection hcoordinatorEq with _ _ hbase
  have hrecordDown : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h dDown.stream.cutoff.cut.input.time source =
        some dDown.stream.cutoff.cut := by
    simpa only [hcutSupportDown] using hrecordSupport
  have hcutoffDown : ReferenceCollectionPhaseHistory.cutoffChosen
      dDown.stream.cutoff.cut.input = true := by
    simpa only [hcutSupportDown] using hcutoffSupport
  have hselectionDown := hselectionSupport
  rw [hcutSupportDown] at hselectionDown
  cases hregisters.symm
  have howned : ownedSupport = ownedDown := eq_of_heq hownedHEq
  subst ownedSupport
  subst baseSupport
  have hconfigDown : ∀ j,
      ((ReferenceActivePhysicalStep.prepare dDown.stream.cutoff.cut.input).followers.followers j).configuration =
        .ordinary
          ({ oldDown j with status := ActiveRoundActions.FollowerStatus.unoccupied })
          (memoryDown j) := by
    intro j
    rcases hfamilySupport j with ⟨_, _, hconfig, _⟩
    have hpreparedInput := congrArg
      (fun input : ReferenceActivePhysicalStep.RoundInput p rate =>
        ((ReferenceActivePhysicalStep.prepare input).followers.followers j).configuration)
      hinputDownSupport
    calc
      ((ReferenceActivePhysicalStep.prepare dDown.stream.cutoff.cut.input).followers.followers j).configuration =
          ((ReferenceActivePhysicalStep.prepare dSupport.stream.cutoff.cut.input).followers.followers j).configuration :=
        hpreparedInput
      _ = .ordinary
          ({ oldDown j with status := ActiveRoundActions.FollowerStatus.unoccupied })
          (memoryDown j) := by
        rw [hStateSupport j |>.1, hStateSupport j |>.2]
        exact hconfig
  have hOldMember : ∀ i : Fin (p.m - 1), (oldDown i).lastDown = none →
      source ∈ cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h
        i dDown.stream.cutoff.cut.input.time := by
    intro i hnone
    have hnoneSupport : (oldSupport i).lastDown = none := by
      rw [← (hStateSupport i).1]
      exact hnone
    have hmember := hdownSupport i hnoneSupport
    rw [hcutSupportDown] at hmember
    refine Set.mem_iUnion.mpr ⟨
      CoordinatorLocalArmChoice.storedDownFlatWord registersDown.payload i, ?_⟩
    exact hmember
  have hFormedMember : ∀ i : Fin (p.m - 1), (oldDown i).lastDown ≠ none →
      source ∈ cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h
        i dDown.stream.cutoff.cut.input.time := by
    intro i hsome
    have hsomeSupport : (oldSupport i).lastDown ≠ none := by
      intro hnone
      apply hsome
      rw [(hStateSupport i).1]
      exact hnone
    rcases hupSupport i hsomeSupport with ⟨reply, _, _, _, _, hmember⟩
    rw [hcutSupportDown] at hmember
    exact Set.mem_iUnion.mpr ⟨reply, hmember⟩
  have hclassify : ∀ i : Fin (p.m - 1),
      (source ∈ cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h
          i dDown.stream.cutoff.cut.input.time ↔ (oldDown i).lastDown = none) ∧
      (source ∈ cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h
          i dDown.stream.cutoff.cut.input.time ↔ (oldDown i).lastDown ≠ none) := by
    intro i
    have hdisjoint := disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i dDown.stream.cutoff.cut.input.time
    constructor
    · constructor
      · intro hOld
        by_contra hnone
        have hFormed := hFormedMember i hnone
        exact (Set.disjoint_left.mp hdisjoint) hOld hFormed
      · exact hOldMember i
    · constructor
      · intro hFormed
        by_contra hnone
        have hOld := hOldMember i hnone
        exact (Set.disjoint_left.mp hdisjoint) hOld hFormed
      · exact hFormedMember i
  have hReadoutBranches : ∀ i : Fin (p.m - 1),
      ((oldDown i).lastDown = none →
        stagedReadout (p := p) (rate := rate) rewards C_star C_h i
            dDown.stream.cutoff.cut.input.time source =
          if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (dDown.stream.cutoff.cut.input.row.2
                  dDown.stream.cutoff.cut.input.time).1 =
                  ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
              ReferenceActiveAffinePositiveTest.downPositive
                dDown.stream.cutoff.cut.input = true then 1 else 0) ∧
      ((oldDown i).lastDown ≠ none →
        stagedReadout (p := p) (rate := rate) rewards C_star C_h i
            dDown.stream.cutoff.cut.input.time source =
          if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (dDown.stream.cutoff.cut.input.row.2
                  dDown.stream.cutoff.cut.input.time).1 =
                  ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
              ReferenceActiveAffinePositiveTest.upPositive
                dDown.stream.cutoff.cut.input = true then 1 else 0) := by
    intro i
    constructor
    · intro hnone
      have hOld := hOldMember i hnone
      rw [stagedReadout_eq_downReadout_of_mem_cutoffOldStageSupport
        (p := p) (rate := rate) rewards C_star C_h i
          dDown.stream.cutoff.cut.input.time source hOld]
      unfold ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      rw [hrecordDown]
      apply if_one_eq_if_of_iff
      constructor
      · rintro ⟨hdraw, hpositive⟩
        exact ⟨by simpa only [ReferenceFirstCollectionUpConditionalService.followerIndex] using hdraw,
          hpositive⟩
      · rintro ⟨hdraw, hpositive⟩
        exact ⟨by simpa only [ReferenceFirstCollectionUpConditionalService.followerIndex] using hdraw,
          hpositive⟩
    · intro hsome
      have hFormed := hFormedMember i hsome
      rw [stagedReadout_eq_upReadout_of_mem_cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i
          dDown.stream.cutoff.cut.input.time source hFormed]
      unfold ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      rw [hrecordDown]
  have hRate : ∀ i : Fin (p.m - 1),
      μ[stagedReadout (p := p) (rate := rate) rewards C_star C_h i
          dDown.stream.cutoff.cut.input.time |
        ReferenceSourceCurrentControlFreshness.m_t p control0
          dDown.stream.cutoff.cut.input.time] source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards dDown.stream.cutoff.cut.input.time : ℝ) /
          (8 * (p.m - 1 : ℝ) * p.K) := by
    intro i
    have hstage := hstageCE i dDown.stream.cutoff.cut.input.time
    have hreadout := hreadoutCE i dDown.stream.cutoff.cut.input.time
    by_cases hnone : (oldDown i).lastDown = none
    · rcases hserviceDown i hnone with
        ⟨word, hword, hrecord, hevent, hmass, hsection, hconditional⟩
      have hsectionRate :
          ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i dDown.stream.cutoff.cut.input.time source =
            (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
              rewards dDown.stream.cutoff.cut.input.time : ℝ) /
              (8 * (p.m - 1 : ℝ) * p.K) :=
        hreadout.1.symm.trans hconditional
      have hOld := hOldMember i hnone
      have hnotFormed : source ∉ cutoffFormedUpStageSupport
          (p := p) (rate := rate) rewards C_star C_h i dDown.stream.cutoff.cut.input.time := by
        intro hFormed
        exact (Set.disjoint_left.mp
          (disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
            (p := p) (rate := rate) rewards C_star C_h i dDown.stream.cutoff.cut.input.time))
          hOld hFormed
      calc
        μ[stagedReadout (p := p) (rate := rate) rewards C_star C_h i
            dDown.stream.cutoff.cut.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0
            dDown.stream.cutoff.cut.input.time] source =
          (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i
              dDown.stream.cutoff.cut.input.time).indicator
              (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
                (rate := rate) rewards C_star C_h control0 i
                  dDown.stream.cutoff.cut.input.time) source +
            (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i
              dDown.stream.cutoff.cut.input.time).indicator
              (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
                (rate := rate) rewards C_star C_h control0 i
                  dDown.stream.cutoff.cut.input.time) source := hstage
        _ = ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
              (rate := rate) rewards C_star C_h control0 i
                dDown.stream.cutoff.cut.input.time source := by
          simp [Set.indicator_of_mem hOld, Set.indicator_of_notMem hnotFormed]
        _ = _ := hsectionRate
    · have hlastUp : (oldUp i).lastDown ≠ none := by
        intro hnoneUp
        apply hnone
        rw [(hStateUp i).1]
        exact hnoneUp
      have hpositive := acceptedStart_pos_of_lastDown_ne_none
        (p := p) (rate := rate) (oldUp i) hlastUp
      rcases hserviceUp i hpositive with ⟨reply, hreplyPrepared, hreplyOld,
        hsigma, hpositiveSigma, hconditional⟩
      have hconditionalDownTime :
          μ[ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
              (rate := rate) rewards C_star C_h i dDown.stream.cutoff.cut.input.time |
            ReferenceSourceCurrentControlFreshness.m_t p control0
              dDown.stream.cutoff.cut.input.time] source =
            (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
              rewards dDown.stream.cutoff.cut.input.time : ℝ) /
              (8 * (p.m - 1 : ℝ) * p.K) := by
        simpa only [hcutDownUp] using hconditional
      have hsectionRate :
          ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i dDown.stream.cutoff.cut.input.time source =
            (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
              rewards dDown.stream.cutoff.cut.input.time : ℝ) /
              (8 * (p.m - 1 : ℝ) * p.K) :=
        hreadout.2.symm.trans hconditionalDownTime
      have hFormed := hFormedMember i (by
        intro hnoneDown
        exact hnone hnoneDown)
      have hnotOld : source ∉ cutoffOldStageSupport
          (p := p) (rate := rate) rewards C_star C_h i dDown.stream.cutoff.cut.input.time := by
        intro hOld
        exact (Set.disjoint_left.mp
          (disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
            (p := p) (rate := rate) rewards C_star C_h i dDown.stream.cutoff.cut.input.time))
          hOld hFormed
      calc
        μ[stagedReadout (p := p) (rate := rate) rewards C_star C_h i
            dDown.stream.cutoff.cut.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0
            dDown.stream.cutoff.cut.input.time] source =
          (cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i
              dDown.stream.cutoff.cut.input.time).indicator
              (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
                (rate := rate) rewards C_star C_h control0 i
                  dDown.stream.cutoff.cut.input.time) source +
            (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i
              dDown.stream.cutoff.cut.input.time).indicator
              (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
                (rate := rate) rewards C_star C_h control0 i
                  dDown.stream.cutoff.cut.input.time) source := hstage
        _ = ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
              (rate := rate) rewards C_star C_h control0 i
                dDown.stream.cutoff.cut.input.time source := by
          simp [Set.indicator_of_notMem hnotOld, Set.indicator_of_mem hFormed]
        _ = _ := hsectionRate
  refine ⟨dDown, oldDown, memoryDown, dDown.stream.cutoff.cut, rfl, ?_⟩
  dsimp only
  refine ⟨hwindow, hhead, htime, hrows, hselected, hreward,
    registersDown, ownedDown, baseDown, hphaseDown, hpayloadDown, hfamilyDown,
    hconfigDown, hrecordDown, hcutoffDown, ?_, ?_⟩
  · exact hselectionDown
  · intro i
    refine ⟨(hclassify i).1, (hclassify i).2, ?_, ?_, ?_⟩
    · exact (hReadoutBranches i).1
    · exact (hReadoutBranches i).2
    · exact hRate i

/-- Integrability follows from the actual readout integrability exports and
the ambient Borel support sets. -/
theorem integrable_stagedReadout (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (stagedReadout (p := p) (rate := rate) rewards C_star C_h i t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hOld := measurableSet_cutoffOldStageSupport_ambient
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hFormed := measurableSet_cutoffFormedUpStageSupport_ambient
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hDown := ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
    (rate := rate) rewards C_star C_h i t
  have hUp := ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
    (rate := rate) rewards C_star C_h i t
  change Integrable
    ((cutoffOldStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t) +
      (cutoffFormedUpStageSupport (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t)) _
  exact (hDown.indicator hOld).add (hUp.indicator hFormed)

end Bandits.Support.ReferenceFirstCutoffStageConditionalService

end
