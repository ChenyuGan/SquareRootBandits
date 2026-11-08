/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCutoffStageConditionalService
public import Bandits.Support.ReferenceFirstCollectionFormationOrigin
public import Bandits.Support.ReferenceCollectionDownReadySupportMeasurability

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Actual first-collection staged service observation

This module joins the actual cutoff stage and the continuing first-collection
stage on the original source space. The fixed-time observation retains the
existing local OLD-DOWN and formed-UP supports and the existing actual
readouts; it introduces no run, state, or source law.

The actual-stream theorem below covers the cutoff and continuing indices
`n < out.ell`. It does not identify the observation on the remaining physical
collection suffix when `out.ell < B.length`. The whole-source local supports
alone do not select only the first assignment.

Sources: `sources/zip4/manuscript/06_interruptions.tex:425-426,477-481`,
`sources/zip4/manuscript/05_binary_transport.tex:70-124`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:44-64,100-108`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstCollectionStagedConditionalService

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev DownWord (p : Parameters) := AffineChannelLaw.Word (AffineBatchDecoder.width p)
abbrev UpRecord (p : Parameters) (rate : RateInput p) :=
  OrdinaryMessageCodec.UpRecord (ReferencePrelaunchFollower.codecParams p rate.eta)

local instance sourceInputMeasurableSpace (p : Parameters) :
    MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  exact Prod.instMeasurableSpace

variable {p : Parameters} {rate : RateInput p}

/-- The actual-cutoff OLD support together with every continuing OLD-DOWN
ready support for the same selected follower and round. -/
def OLD (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) : Set (SourceInput p) :=
  ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ wD : DownWord p,
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t wD

/-- The actual-cutoff formed support together with every continuing formed-UP
ready support for the same selected follower and round. -/
def FORMED (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) : Set (SourceInput p) :=
  ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ U : UpRecord p rate,
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t U

/-- The literal combined finite observation on the original source space. -/
def X (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) : ℝ :=
  (OLD (p := p) (rate := rate) rewards C_star C_h i t).indicator
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t) z +
  (FORMED (p := p) (rate := rate) rewards C_star C_h i t).indicator
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t) z

/-- The exact fixed-time current-control field measures the OLD support. -/
theorem measurableSet_OLD (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (OLD (p := p) (rate := rate) rewards C_star C_h i t) := by
  classical
  exact MeasurableSet.union
    (ReferenceFirstCutoffStageConditionalService.measurableSet_cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h control0 i t)
    (MeasurableSet.iUnion fun wD =>
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport_measurableSet
        (p := p) (rate := rate) rewards C_star C_h control0 i t wD)

/-- The exact fixed-time current-control field measures the formed support. -/
theorem measurableSet_FORMED (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    MeasurableSet[ReferenceSourceCurrentControlFreshness.m_t p control0 t]
      (FORMED (p := p) (rate := rate) rewards C_star C_h i t) := by
  classical
  exact MeasurableSet.union
    (ReferenceFirstCutoffStageConditionalService.measurableSet_cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h control0 i t)
    (MeasurableSet.iUnion fun U =>
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport_measurableSet
        (p := p) (rate := rate) rewards C_star C_h control0 i t U)

/-- OLD membership is unchanged by replacing the complete current control. -/
theorem OLD_replaceSourceControl_iff (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : SourceInput p) (c : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
        OLD (p := p) (rate := rate) rewards C_star C_h i t ↔
      z ∈ OLD (p := p) (rate := rate) rewards C_star C_h i t := by
  classical
  simp only [OLD, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (hcut | ⟨wD, hcont⟩)
    · exact Or.inl
        ((ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport_replaceSourceControl_iff
          (p := p) (rate := rate) rewards C_star C_h i t z c).mp hcut)
    · exact Or.inr ⟨wD,
        (ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport_replaceSourceControl
          (p := p) (rate := rate) rewards C_star C_h control0 i t wD z c).symm.mp hcont⟩
  · rintro (hcut | ⟨wD, hcont⟩)
    · exact Or.inl
        ((ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport_replaceSourceControl_iff
          (p := p) (rate := rate) rewards C_star C_h i t z c).mpr hcut)
    · exact Or.inr ⟨wD,
        (ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport_replaceSourceControl
          (p := p) (rate := rate) rewards C_star C_h control0 i t wD z c).mp hcont⟩

/-- FORMED membership is unchanged by replacing the complete current control. -/
theorem FORMED_replaceSourceControl_iff (rewards : RewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T)
    (z : SourceInput p) (c : TimeControl p) :
    ReferenceFixedTimeSourceControlCoupling.replaceSourceControl p t z c ∈
        FORMED (p := p) (rate := rate) rewards C_star C_h i t ↔
      z ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i t := by
  classical
  simp only [FORMED, Set.mem_union, Set.mem_iUnion]
  constructor
  · rintro (hcut | ⟨U, hcont⟩)
    · exact Or.inl
        ((ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport_replaceSourceControl_iff
          (p := p) (rate := rate) rewards C_star C_h i t z c).mp hcut)
    · exact Or.inr ⟨U,
        (ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport_replaceSourceControl
          (p := p) (rate := rate) rewards C_star C_h control0 i t U z c).symm.mp hcont⟩
  · rintro (hcut | ⟨U, hcont⟩)
    · exact Or.inl
        ((ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport_replaceSourceControl_iff
          (p := p) (rate := rate) rewards C_star C_h i t z c).mpr hcut)
    · exact Or.inr ⟨U,
        (ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport_replaceSourceControl
          (p := p) (rate := rate) rewards C_star C_h control0 i t U z c).mp hcont⟩

private theorem cutoffOld_disjoint_continuingUp (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {z : SourceInput p}
    (hcut : z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t)
    {U : UpRecord p rate}
    (hcont : z ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
      (p := p) (rate := rate) rewards C_star C_h i t U) : False := by
  rcases Set.mem_iUnion.mp hcut with ⟨_, hcut⟩
  rcases hcut with ⟨r, hr, registers, owned, base, hlive, hcutoff,
    hordinary, old, memory, hfocus, hnone, hword⟩
  rcases hcont with ⟨r', hr', payload, l, saved, old', memory', hready,
    hip, hfocus', hpositive, hfields, hordinary'⟩
  have hrecord : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  have hcoordinator := hlive.symm.trans hready.1
  cases hcoordinator

private theorem cutoffFormed_disjoint_continuingDown (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {z : SourceInput p}
    (hcut : z ∈ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t)
    {wD : DownWord p}
    (hcont : z ∈ ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
      (p := p) (rate := rate) rewards C_star C_h i t wD) : False := by
  rcases Set.mem_iUnion.mp hcut with ⟨_, hcut⟩
  rcases hcut with ⟨r, hr, registers, owned, base, hlive, hcutoff,
    hordinary, old, memory, hfocus, hpositive, hfields⟩
  rcases hcont with ⟨r', hr', payload, l, saved, old', memory', hready,
    hip, hfocus', hnone, hword, hordinary'⟩
  have hrecord : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  have hcoordinator := hlive.symm.trans hready.1
  cases hcoordinator

private theorem continuingDown_disjoint_continuingUp
    (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {wD : DownWord p} {U : UpRecord p rate}
    (hdown : z ∈ ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
      (p := p) (rate := rate) rewards C_star C_h i t wD)
    (hup : z ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
      (p := p) (rate := rate) rewards C_star C_h i t U) : False := by
  rcases hdown with ⟨r, hr, payload, l, saved, old, memory, hready,
    hip, hfocus, hnone, hword, hordinary⟩
  rcases hup with ⟨r', hr', payload', l', saved', old', memory', hready',
    hip', hfocus', hpositive, hfields, hordinary'⟩
  have hrecord : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  have hstate := hfocus.symm.trans hfocus'
  injection hstate with hold hmemory
  have hpositive' := hpositive
  rw [← hold] at hpositive'
  simp [ReferencePrelaunchFollower.acceptedStart, hnone] at hpositive'

/-- OLD and FORMED are disjoint on the whole original source. The proof
identifies the common actual record, separates the cutoff `.live` and
continuing `.collection` constructors, then uses the follower's literal
`lastDown` field within each phase. -/
theorem disjoint_OLD_FORMED (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) :
    Disjoint (OLD (p := p) (rate := rate) rewards C_star C_h i t)
      (FORMED (p := p) (rate := rate) rewards C_star C_h i t) := by
  classical
  rw [Set.disjoint_left]
  intro z hOld hFormed
  rcases hOld with hcutOld | hdownUnion
  · rcases hFormed with hcutFormed | hupUnion
    · exact (Set.disjoint_left.mp
        (ReferenceFirstCutoffStageConditionalService.disjoint_cutoffOldStageSupport_cutoffFormedUpStageSupport
          (p := p) (rate := rate) rewards C_star C_h i t)) hcutOld hcutFormed
    · obtain ⟨U, hup⟩ := Set.mem_iUnion.mp hupUnion
      exact cutoffOld_disjoint_continuingUp
        (p := p) (rate := rate) rewards C_star C_h i t hcutOld hup
  · obtain ⟨wD, hdown⟩ := Set.mem_iUnion.mp hdownUnion
    rcases hFormed with hcutFormed | hupUnion
    · exact cutoffFormed_disjoint_continuingDown
        (p := p) (rate := rate) rewards C_star C_h i t hcutFormed hdown
    · obtain ⟨U, hup⟩ := Set.mem_iUnion.mp hupUnion
      exact continuingDown_disjoint_continuingUp
        (p := p) (rate := rate) rewards C_star C_h i t hdown hup

/-- The joined observation is exactly zero or one at every source point. -/
theorem X_zero_or_one (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) (z : SourceInput p) :
    X (p := p) (rate := rate) rewards C_star C_h i t z = 0 ∨
      X (p := p) (rate := rate) rewards C_star C_h i t z = 1 := by
  classical
  have hDown :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout_zero_or_one
      (rate := rate) rewards C_star C_h i t z
  have hUp :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout_zero_or_one
      (rate := rate) rewards C_star C_h i t z
  by_cases hOld : z ∈ OLD (p := p) (rate := rate) rewards C_star C_h i t
  · have hFormed : z ∉ FORMED (p := p) (rate := rate) rewards C_star C_h i t := by
      intro hFormed
      exact (Set.disjoint_left.mp (disjoint_OLD_FORMED
        (p := p) (rate := rate) rewards C_star C_h i t)) hOld hFormed
    simpa [X, Set.indicator_of_mem hOld, Set.indicator_of_notMem hFormed] using hDown
  · by_cases hFormed : z ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i t
    · simpa [X, Set.indicator_of_notMem hOld, Set.indicator_of_mem hFormed] using hUp
    · left
      simp [X, Set.indicator_of_notMem hOld, Set.indicator_of_notMem hFormed]

/-- The exact fixed-time field is included in the source's ambient Borel field. -/
private theorem m_t_le_sourceBorel (control0 : TimeControl p) (t : Fin p.T) :
    ReferenceSourceCurrentControlFreshness.m_t p control0 t ≤
      (inferInstance : MeasurableSpace (SourceInput p)) :=
  (ReferenceSourceCurrentControlFreshness.measurable_c_t control0 t).comap_le

/-- The observation is Borel measurable on the original source space. -/
theorem measurable_X (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Measurable (X (p := p) (rate := rate) rewards C_star C_h i t) := by
  have hOld := measurableSet_OLD
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hFormed := measurableSet_FORMED
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hDown :=
    ReferenceFirstCollectionDownConditionalService.measurable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  have hUp :=
    ReferenceFirstCollectionUpConditionalService.measurable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  have hOldAmbient := m_t_le_sourceBorel (p := p) control0 t
    (OLD (p := p) (rate := rate) rewards C_star C_h i t) hOld
  have hFormedAmbient := m_t_le_sourceBorel (p := p) control0 t
    (FORMED (p := p) (rate := rate) rewards C_star C_h i t) hFormed
  exact (hDown.indicator hOldAmbient).add (hUp.indicator hFormedAmbient)

/-- Integrability on the original source law follows from the two admitted
actual readout integrability results and the ambient measurable supports. -/
theorem integrable_X (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    Integrable (X (p := p) (rate := rate) rewards C_star C_h i t)
      (BootstrapPrivateRoundStreams.sourceInputLaw p) := by
  have hOld := measurableSet_OLD
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hFormed := measurableSet_FORMED
    (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hDown :=
    ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  have hUp :=
    ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  have hOldAmbient := m_t_le_sourceBorel (p := p) control0 t
    (OLD (p := p) (rate := rate) rewards C_star C_h i t) hOld
  have hFormedAmbient := m_t_le_sourceBorel (p := p) control0 t
    (FORMED (p := p) (rate := rate) rewards C_star C_h i t) hFormed
  change Integrable
    ((OLD (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t) +
      (FORMED (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t))
      (BootstrapPrivateRoundStreams.sourceInputLaw p)
  exact (hDown.indicator hOldAmbient).add (hUp.indicator hFormedAmbient)

/-- Conditional expectation of the whole-source observation in the exact
current-control field, under the unchanged private source law. -/
theorem X_condExp (rewards : RewardTable p) (C_star C_h : ℝ)
    (control0 : TimeControl p) (i : Fin (p.m - 1)) (t : Fin p.T) :
    (BootstrapPrivateRoundStreams.sourceInputLaw p)[
      X (p := p) (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] =ᵐ[
          BootstrapPrivateRoundStreams.sourceInputLaw p]
    fun z =>
      (OLD (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i t) z +
      (FORMED (p := p) (rate := rate) rewards C_star C_h i t).indicator
        (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i t) z := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  let m := ReferenceSourceCurrentControlFreshness.m_t p control0 t
  let oldSet := OLD (p := p) (rate := rate) rewards C_star C_h i t
  let formedSet := FORMED (p := p) (rate := rate) rewards C_star C_h i t
  let downReadout :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  let upReadout :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  let downSection :=
    ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  let upSection :=
    ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
      (rate := rate) rewards C_star C_h control0 i t
  have hOld : MeasurableSet[m] oldSet :=
    measurableSet_OLD (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hFormed : MeasurableSet[m] formedSet :=
    measurableSet_FORMED (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hOldAmbient : @MeasurableSet (SourceInput p)
      (sourceInputMeasurableSpace p) oldSet :=
    m_t_le_sourceBorel (p := p) control0 t oldSet hOld
  have hFormedAmbient : @MeasurableSet (SourceInput p)
      (sourceInputMeasurableSpace p) formedSet :=
    m_t_le_sourceBorel (p := p) control0 t formedSet hFormed
  have hDownInt : Integrable downReadout μ :=
    ReferenceFirstCollectionDownConditionalService.integrable_actualFirstCollectionDownReadout
      (rate := rate) rewards C_star C_h i t
  have hUpInt : Integrable upReadout μ :=
    ReferenceFirstCollectionUpConditionalService.integrable_actualFirstCollectionUpReadout
      (rate := rate) rewards C_star C_h i t
  have hOldInt : Integrable (oldSet.indicator downReadout) μ :=
    hDownInt.indicator hOldAmbient
  have hFormedInt : Integrable (formedSet.indicator upReadout) μ :=
    hUpInt.indicator hFormedAmbient
  have hAdd : μ[X (p := p) (rate := rate) rewards C_star C_h i t | m] =ᵐ[μ]
      μ[oldSet.indicator downReadout | m] + μ[formedSet.indicator upReadout | m] := by
    change μ[(oldSet.indicator downReadout) +
      (formedSet.indicator upReadout) | m] =ᵐ[μ] _
    exact MeasureTheory.condExp_add hOldInt hFormedInt m
  have hOldInd := MeasureTheory.condExp_indicator hDownInt hOld
  have hFormedInd := MeasureTheory.condExp_indicator hUpInt hFormed
  have hDownCE :=
    ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp
      (rate := rate) rewards C_star C_h control0 i t
  have hUpCE :=
    ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp
      (rate := rate) rewards C_star C_h control0 i t
  filter_upwards [hAdd, hOldInd, hFormedInd, hDownCE, hUpCE]
    with z hAdd hOldInd hFormedInd hDownCE hUpCE
  have hOldSection : oldSet.indicator (μ[downReadout | m]) z =
      oldSet.indicator downSection z := by
    by_cases hz : z ∈ oldSet
    · simpa only [Set.indicator_of_mem hz] using hDownCE
    · simp [Set.indicator_of_notMem hz]
  have hFormedSection : formedSet.indicator (μ[upReadout | m]) z =
      formedSet.indicator upSection z := by
    by_cases hz : z ∈ formedSet
    · simpa only [Set.indicator_of_mem hz] using hUpCE
    · simp [Set.indicator_of_notMem hz]
  calc
    μ[X (p := p) (rate := rate) rewards C_star C_h i t | m] z =
        (μ[oldSet.indicator downReadout | m] +
          μ[formedSet.indicator upReadout | m]) z := hAdd
    _ = oldSet.indicator (μ[downReadout | m]) z +
        formedSet.indicator (μ[upReadout | m]) z := by
      change μ[oldSet.indicator downReadout | m] z +
        μ[formedSet.indicator upReadout | m] z = _
      rw [hOldInd, hFormedInd]
    _ = oldSet.indicator downSection z + formedSet.indicator upSection z := by
      rw [hOldSection, hFormedSection]

private theorem actualRecord_window (rewards : RewardTable p) (C_star C_h : ℝ)
    {source : SourceInput p} (count : ℕ)
    (hcross : (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
    (hspan : ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
    (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records).length < count)
    (n : Fin (ReferenceCollectionPhaseHistory.collectionWindow
      (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
        rate source rewards C_star C_h hcross count hspan).records
      (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records).length).length) :
    ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
      (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val].input.time
      source = some (ReferenceCollectionPhaseHistory.collectionWindow
        (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan).records
        (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length)[n.val] := by
  let s := ReferenceInitializationRun.elapsed p
    (ReferenceInitializationRun.output
      (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
  let initial := ReferenceFirstCollectionEpochAlignment.actualLaunchState
    rate source rewards C_star C_h hcross
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hwindow := ReferenceFirstCollectionReadyStep.actual_collection_window_record_alignment
    rate source rewards C_star C_h count hcross hspan hshort n
  have hlaunch : ReferenceCorrectedInitializationLaunch.correctedLaunch
      rate source rewards C_star C_h = some initial :=
    Option.eq_some_of_isSome
      ((ReferenceCorrectedInitializationLaunch.correctedLaunch_isSome_iff_crossing
        rate source rewards C_star C_h).2 hcross)
  have hactive :=
    (ReferenceFirstCollectionEpochAlignment.actualLaunchState_first_active
      rate source rewards C_star C_h hcross).1
  have htime : B[n.val].input.time.val = s + (w + n.val) := by
    have ht := hwindow.2.1
    change B[n.val].input.time.val + 1 = s + w + 1 + n.val at ht
    omega
  have hcount : E.records.length = count :=
    ReferenceActivePhysicalHorizon.run_record_count _ _ _ _ _ _ _ _
  have hindex : w + n.val < count := by
    have hb := (List.getElem?_eq_some_iff.mp hwindow.1).1
    rwa [hcount] at hb
  have hrecordAt : B[n.val] = ReferenceAssignmentPayloadChronology.actualRunRecordAt
      initial source.1.2 (ActualInitializationPhysicalStep.selectedRowIndex p source)
      rewards s (w + n.val) (by omega) hactive := by
    have hat := ReferenceLocalReleaseGateChronology.run_record_at initial source.1.2
      (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s hactive count
      hspan ⟨w + n.val, hindex⟩
    apply Option.some.inj
    calc
      some B[n.val] = E.records[w + n.val]? := hwindow.1.symm
      _ = _ := by
        rw [List.getElem?_eq_getElem (by rw [hcount]; exact hindex)]
        simpa only [E, initial,
          ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun] using
          congrArg some hat
  have hsource := ReferenceSourcePrefixHistoryFiltration.actualRecord_on_launch
    rate rewards C_star C_h B[n.val].input.time source initial hlaunch
    (by rw [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime]; omega)
  have hsource' : ReferenceSourcePrefixHistoryFiltration.actualRecord
      rate rewards C_star C_h B[n.val].input.time source =
        some (ReferenceAssignmentPayloadChronology.actualRunRecordAt initial source.1.2
          (ActualInitializationPhysicalStep.selectedRowIndex p source) rewards s
          (w + n.val) (by omega) hactive) := by
    simpa only [show ReferenceCompletePhysicalHistory.physicalStart rate source rewards C_star C_h = s by rfl,
      htime, Nat.add_sub_cancel_left] using hsource
  simpa only [B, E, w] using hsource'.trans (congrArg some hrecordAt.symm)

private theorem no_continuingDown_of_live (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {z : SourceInput p} {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : r.input.state.coordinator = .live registers owned base) :
    z ∉ ⋃ wD : DownWord p,
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t wD := by
  intro hz
  obtain ⟨wD, hz⟩ := Set.mem_iUnion.mp hz
  rcases hz with ⟨r', hr', payload, l, saved, old, memory, hready, hip, hfi,
    hnone, hword, hordinary⟩
  have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
  subst r'
  have hphase := hlive.symm.trans hready.1
  cases hphase

private theorem no_continuingUp_of_live (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T)
    {z : SourceInput p} {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : r.input.state.coordinator = .live registers owned base) :
    z ∉ ⋃ U : UpRecord p rate,
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t U := by
  intro hz
  obtain ⟨U, hz⟩ := Set.mem_iUnion.mp hz
  rcases hz with ⟨r', hr', payload, l, saved, old, memory, hready, hip, hfi,
    hpositive, hfields, hordinary⟩
  have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
  subst r'
  have hphase := hlive.symm.trans hready.1
  cases hphase

private theorem OLD_iff_cutoff_of_live (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : r.input.state.coordinator = .live registers owned base) :
    z ∈ OLD (p := p) (rate := rate) rewards C_star C_h i t ↔
      z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t := by
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ wD : DownWord p,
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t wD ↔ _
  constructor
  · rintro (hcut | hdown)
    · exact hcut
    · exact False.elim ((no_continuingDown_of_live (p := p) (rate := rate)
        rewards C_star C_h i t hrecord registers owned base hlive) hdown)
  · intro hcut
    exact Or.inl hcut

private theorem FORMED_iff_cutoff_of_live (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : r.input.state.coordinator = .live registers owned base) :
    z ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i t ↔
      z ∈ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t := by
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ U : UpRecord p rate,
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t U ↔ _
  constructor
  · rintro (hcut | hup)
    · exact hcut
    · exact False.elim ((no_continuingUp_of_live (p := p) (rate := rate)
        rewards C_star C_h i t hrecord registers owned base hlive) hup)
  · intro hcut
    exact Or.inl hcut

private theorem no_OLD_of_notPending (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      r.input payload l saved)
    (hnot : i ∉ l.pending) :
    z ∉ OLD (p := p) (rate := rate) rewards C_star C_h i t := by
  intro hOld
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ wD : DownWord p,
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t wD at hOld
  rcases hOld with hcut | hdown
  · rcases Set.mem_iUnion.mp hcut with ⟨wD, hcut⟩
    rcases hcut with ⟨r', hr', registers, owned, base, hlive, hchosen,
      hordinary, old, memory, hfocus, hnone, hword⟩
    have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
    subst r'
    have hphase := hready.1.symm.trans hlive
    cases hphase
  · obtain ⟨wD, hdown⟩ := Set.mem_iUnion.mp hdown
    rcases hdown with ⟨r', hr', payload', l', saved', old, memory, hready',
      hip, hfocus, hnone, hword, hordinary⟩
    have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
    subst r'
    have hphase := hready'.1.symm.trans hready.1
    injection hphase with hp hl hs
    exact hnot (hl ▸ hip)

private theorem no_FORMED_of_notPending (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      r.input payload l saved)
    (hnot : i ∉ l.pending) :
    z ∉ FORMED (p := p) (rate := rate) rewards C_star C_h i t := by
  intro hFormed
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ U : UpRecord p rate,
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t U at hFormed
  rcases hFormed with hcut | hup
  · rcases Set.mem_iUnion.mp hcut with ⟨U, hcut⟩
    rcases hcut with ⟨r', hr', registers, owned, base, hlive, hchosen,
      hordinary, old, memory, hfocus, hpositive, hfields⟩
    have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
    subst r'
    have hphase := hready.1.symm.trans hlive
    cases hphase
  · obtain ⟨U, hup⟩ := Set.mem_iUnion.mp hup
    rcases hup with ⟨r', hr', payload', l', saved', old, memory, hready',
      hip, hfocus, hpositive, hfields, hordinary⟩
    have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
    subst r'
    have hphase := hready'.1.symm.trans hready.1
    injection hphase with hp hl hs
    exact hnot (hl ▸ hip)

private theorem OLD_iff_lastDown (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      r.input payload l saved)
    (hfi : r.input.state.followers i = .ordinary old memory)
    {wD : DownWord p}
    (hdown : z ∈ ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
      (p := p) (rate := rate) rewards C_star C_h i t wD) :
    z ∈ OLD (p := p) (rate := rate) rewards C_star C_h i t ↔ old.lastDown = none := by
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ word : DownWord p,
      ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t word ↔ _
  constructor
  · rintro (hcut | hcont)
    · rcases Set.mem_iUnion.mp hcut with ⟨word, hcut⟩
      rcases hcut with ⟨r', hr', registers, owned, base, hlive, hchosen,
        hordinary, old', memory', hfocus, hnone, hword⟩
      have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
      subst r'
      have hphase := hready.1.symm.trans hlive
      cases hphase
    · obtain ⟨word, hcont⟩ := Set.mem_iUnion.mp hcont
      rcases hcont with ⟨r', hr', payload', l', saved', old', memory', hready',
        hip', hfocus', hnone, hword, hordinary⟩
      have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
      subst r'
      have hphase := hready'.1.symm.trans hready.1
      injection hphase with hp hl hs
      have hstate := hfi.symm.trans hfocus'
      injection hstate with hold hmemory
      rw [hold]
      exact hnone
  · intro hnone
    exact Or.inr (Set.mem_iUnion.mpr ⟨wD, hdown⟩)

private theorem FORMED_iff_lastDown_ne (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (payload : ReferenceActivePhysicalStep.Payload rate)
    (l : ReferenceActivePhysicalStep.Ledger rate) (saved : Option (Fin p.T × Bool))
    (old : ReferencePrelaunchFollower.State p rate.eta)
    (memory : ActiveFollowerLifecycle.LocalMemory p)
    (hready : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
      r.input payload l saved)
    (hfi : r.input.state.followers i = .ordinary old memory)
    {U : UpRecord p rate}
    (hup : z ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
      (p := p) (rate := rate) rewards C_star C_h i t U) :
    z ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i t ↔ old.lastDown ≠ none := by
  change z ∈ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
    ⋃ reply : UpRecord p rate,
      ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
        (p := p) (rate := rate) rewards C_star C_h i t reply ↔ _
  constructor
  · rintro (hcut | hcont)
    · rcases Set.mem_iUnion.mp hcut with ⟨reply, hcut⟩
      rcases hcut with ⟨r', hr', registers, owned, base, hlive, hchosen,
        hordinary, old', memory', hfocus, hpositive, hfields⟩
      have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
      subst r'
      have hphase := hready.1.symm.trans hlive
      cases hphase
    · obtain ⟨reply, hcont⟩ := Set.mem_iUnion.mp hcont
      rcases hcont with ⟨r', hr', payload', l', saved', old', memory', hready',
        hip', hfocus', hpositive, hfields, hordinary⟩
      have hr : r' = r := Option.some.inj (hr'.symm.trans hrecord)
      subst r'
      have hphase := hready'.1.symm.trans hready.1
      injection hphase with hp hl hs
      have hstate := hfi.symm.trans hfocus'
      injection hstate with hold hmemory
      rw [← hold] at hpositive
      intro hlast
      simp [ReferencePrelaunchFollower.acceptedStart, hlast] at hpositive
  · intro hpositive
    exact Or.inr (Set.mem_iUnion.mpr ⟨U, hup⟩)

private theorem X_eq_down_test (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hOld : z ∈ OLD (p := p) (rate := rate) rewards C_star C_h i t)
    (hFormed : z ∉ FORMED (p := p) (rate := rate) rewards C_star C_h i t) :
    X (p := p) (rate := rate) rewards C_star C_h i t z =
      if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 t).1 = ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
        ReferenceActiveAffinePositiveTest.downPositive r.input = true then 1 else 0 := by
  rw [X, Set.indicator_of_mem hOld, Set.indicator_of_notMem hFormed]
  simp [ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout,
    hrecord]
  by_cases h : PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
      (r.input.row.2 t).1 = i ∧ ReferenceActiveAffinePositiveTest.downPositive r.input = true
  · simp [h, ReferenceFirstCollectionUpConditionalService.followerIndex]
  · simp [h, ReferenceFirstCollectionUpConditionalService.followerIndex]

private theorem X_eq_up_test (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (hOld : z ∉ OLD (p := p) (rate := rate) rewards C_star C_h i t)
    (hFormed : z ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i t) :
    X (p := p) (rate := rate) rewards C_star C_h i t z =
      if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
          (r.input.row.2 t).1 = ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
        ReferenceActiveAffinePositiveTest.upPositive r.input = true then 1 else 0 := by
  rw [X, Set.indicator_of_notMem hOld, Set.indicator_of_mem hFormed]
  simp [ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout,
    hrecord]

private theorem X_eq_staged_on_live (rewards : RewardTable p) (C_star C_h : ℝ)
    (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    {r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate)}
    (hrecord : ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h t z = some r)
    (registers : CoordinatorLiveChoiceRecorderStep.Registers p rate.eta)
    (owned : CoordinatorLiveServiceFinish.OwnedRegisters registers)
    (base : Fin (p.m - 1) → ℕ)
    (hlive : r.input.state.coordinator = .live registers owned base) :
    X (p := p) (rate := rate) rewards C_star C_h i t z =
      ReferenceFirstCutoffStageConditionalService.stagedReadout
        (p := p) (rate := rate) rewards C_star C_h i t z := by
  have hnotDown := no_continuingDown_of_live
    (p := p) (rate := rate) rewards C_star C_h i t hrecord registers owned base hlive
  have hnotUp := no_continuingUp_of_live
    (p := p) (rate := rate) rewards C_star C_h i t hrecord registers owned base hlive
  have hdown : ((ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
      ⋃ wD : DownWord p,
        ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
          (p := p) (rate := rate) rewards C_star C_h i t wD).indicator
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t)) z =
      (ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t).indicator
      (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
        (rate := rate) rewards C_star C_h i t) z := by
    by_cases hc : z ∈ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t
    · simp [Set.indicator_of_mem, hc, hnotDown]
    · have hnone : z ∉ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
          (p := p) (rate := rate) rewards C_star C_h i t ∪
        ⋃ wD : DownWord p,
          ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
            (p := p) (rate := rate) rewards C_star C_h i t wD := by
        simpa [hc] using hnotDown
      simp [Set.indicator_of_notMem, hc, hnone]
  have hup : ((ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
      (p := p) (rate := rate) rewards C_star C_h i t ∪
      ⋃ U : UpRecord p rate,
        ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
          (p := p) (rate := rate) rewards C_star C_h i t U).indicator
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t)) z =
      (ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t).indicator
      (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
        (rate := rate) rewards C_star C_h i t) z := by
    by_cases hc : z ∈ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
        (p := p) (rate := rate) rewards C_star C_h i t
    · simp [Set.indicator_of_mem, hc, hnotUp]
    · have hnone : z ∉ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
          (p := p) (rate := rate) rewards C_star C_h i t ∪
        ⋃ U : UpRecord p rate,
          ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
            (p := p) (rate := rate) rewards C_star C_h i t U := by
        simpa [hc] using hnotUp
      simp [Set.indicator_of_notMem, hc, hnone]
  rw [X, ReferenceFirstCutoffStageConditionalService.stagedReadout]
  dsimp only [OLD, FORMED]
  rw [hdown, hup]

private theorem X_eq_zero_of_no_support (rewards : RewardTable p)
    (C_star C_h : ℝ) (i : Fin (p.m - 1)) (t : Fin p.T) {z : SourceInput p}
    (hOld : z ∉ OLD (p := p) (rate := rate) rewards C_star C_h i t)
    (hFormed : z ∉ FORMED (p := p) (rate := rate) rewards C_star C_h i t) :
    X (p := p) (rate := rate) rewards C_star C_h i t z = 0 := by
  simp [X, Set.indicator_of_notMem hOld, Set.indicator_of_notMem hFormed]

/-- The actual first collection's cutoff and produced continuing pending
boundaries with `n < out.ell` use this same whole-source observation and the
same original source law. The returned stream witness is F's actual dispatch;
the cutoff witness from C is identified by the common actual cut index.
No conclusion about the remaining physical suffix is asserted here. -/
theorem actual_initialized_first_collection_staged_service
    (rewards : RewardTable p) (C_star C_h : ℝ) (control0 : TimeControl p) :
    ∀ᵐ source ∂BootstrapPrivateRoundStreams.sourceInputLaw p,
      ∀ (count : ℕ)
        (hcross : (ReferenceInitializationRun.output
          (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).crossing.isSome = true)
        (hspan : ReferenceInitializationRun.elapsed p
          (ReferenceInitializationRun.output
            (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed + count ≤ p.T)
        (hshort : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
          (ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
            rate source rewards C_star C_h hcross count hspan).records).length < count),
    ∃ d : ReferenceFirstCollectionStreamEmptyDispatch.ActualInitializedStreamDispatch
          source rewards C_star C_h count hcross hspan hshort,
        let out := d.stream
        let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
          rate source rewards C_star C_h hcross count hspan
        let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
        let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
        out.window = B ∧
        (∀ i : Fin (p.m - 1),
          X (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time source =
            ReferenceFirstCutoffStageConditionalService.stagedReadout
              (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time source ∧
          (BootstrapPrivateRoundStreams.sourceInputLaw p)[
            X (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time |
              ReferenceSourceCurrentControlFreshness.m_t p control0
                out.cutoff.cut.input.time] source =
            (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
              rewards out.cutoff.cut.input.time : ℝ) /
              (8 * (p.m - 1 : ℝ) * p.K)) ∧
          (∀ (n : Fin out.ell), 0 < n.val →
            ∀ i : Fin (p.m - 1),
              i ∈ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              ∃ (r : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate))
                (incoming : ReferenceActivePhysicalStep.Ledger rate)
                (old : ReferencePrelaunchFollower.State p rate.eta)
                (memory : ActiveFollowerLifecycle.LocalMemory p),
                out.window[n.val]? = some r ∧
                r.input.time.val + 1 =
                  ReferenceInitializationRun.elapsed p
                    (ReferenceInitializationRun.output
                      (ActualReferenceInitializationBlock.referenceInput
                        source rewards C_star C_h rate)).completed + w + 1 + n.val ∧
                r.input.rows = source.1.2 ∧
                r.input.selected = ActualInitializationPhysicalStep.selectedRowIndex p source ∧
                r.input.rewards = rewards ∧
                incoming = out.ledgers ⟨n.val - 1, by omega⟩ ∧
                i ∈ incoming.pending ∧
                ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
                  r.input out.payload incoming out.saved ∧
                r.input.state.followers i = .ordinary old memory ∧
                old.status = .unoccupied ∧
                ActiveFollowerLifecycle.localStateDomainValid old ∧
                ((old.lastDown = none ∧ old.S = 0 ∧ old.delta = 0 ∧ old.backlog = 0) ∨
                  old.lastDown = some (out.payload.downRecord i)) ∧
                (old.lastDown = some (out.payload.downRecord i) →
                  ∃ U : UpRecord p rate,
                    U.val = ActiveFollowerQueueOperation.upOfferFields old ∧
                    1 ≤ U.val.sigma) ∧
                (source ∈ OLD (p := p) (rate := rate) rewards C_star C_h i r.input.time ↔
                  old.lastDown = none) ∧
                (source ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time ↔
                  old.lastDown ≠ none) ∧
                (old.lastDown = none →
                  X (p := p) (rate := rate) rewards C_star C_h i r.input.time source =
                    if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (r.input.row.2 r.input.time).1 =
                          ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
                      ReferenceActiveAffinePositiveTest.downPositive r.input = true then 1 else 0) ∧
                (old.lastDown ≠ none →
                  X (p := p) (rate := rate) rewards C_star C_h i r.input.time source =
                    if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                        (r.input.row.2 r.input.time).1 =
                          ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
                      ReferenceActiveAffinePositiveTest.upPositive r.input = true then 1 else 0) ∧
                (BootstrapPrivateRoundStreams.sourceInputLaw p)[
                  X (p := p) (rate := rate) rewards C_star C_h i r.input.time |
                    ReferenceSourceCurrentControlFreshness.m_t p control0 r.input.time] source =
                  (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
                    rewards r.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K)) ∧
          (∀ (n : Fin out.ell), 0 < n.val →
            ∀ i : Fin (p.m - 1),
              i ∉ (out.ledgers ⟨n.val - 1, by omega⟩).pending →
              X (p := p) (rate := rate) rewards C_star C_h i
                (out.window[n.val]'(Nat.lt_of_lt_of_le n.isLt out.withinWindow)).input.time source = 0) := by
  let μ := BootstrapPrivateRoundStreams.sourceInputLaw p
  have hcutRoot :=
    ReferenceFirstCutoffStageConditionalService.actual_first_cutoff_staged_service
      (rate := rate) rewards C_star C_h control0
  have hdownRoot :=
    ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp_service
      (rate := rate) rewards C_star C_h control0
  have hupRoot :=
    ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp_service
      (rate := rate) rewards C_star C_h control0
  have hXCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      μ[X (p := p) (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        (OLD (p := p) (rate := rate) rewards C_star C_h i t).indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i t) source +
        (FORMED (p := p) (rate := rate) rewards C_star C_h i t).indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i t) source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      X_condExp (p := p) (rate := rate) rewards C_star C_h control0 i t
  have hDownCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      μ[ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownReadout
          (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
          (rate := rate) rewards C_star C_h control0 i t source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionDownConditionalService.actual_first_collection_down_condExp
        (rate := rate) rewards C_star C_h control0 i t
  have hUpCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      μ[ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpReadout
          (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
          (rate := rate) rewards C_star C_h control0 i t source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCollectionUpConditionalService.actual_first_collection_up_condExp
        (rate := rate) rewards C_star C_h control0 i t
  have hCutStageCE : ∀ᵐ source ∂μ, ∀ i : Fin (p.m - 1), ∀ t : Fin p.T,
      μ[ReferenceFirstCutoffStageConditionalService.stagedReadout
          (p := p) (rate := rate) rewards C_star C_h i t |
        ReferenceSourceCurrentControlFreshness.m_t p control0 t] source =
        (ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
          (p := p) (rate := rate) rewards C_star C_h i t).indicator
            (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
              (rate := rate) rewards C_star C_h control0 i t) source +
        (ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
          (p := p) (rate := rate) rewards C_star C_h i t).indicator
            (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
              (rate := rate) rewards C_star C_h control0 i t) source :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun t =>
      ReferenceFirstCutoffStageConditionalService.stagedReadout_condExp
        (p := p) (rate := rate) rewards C_star C_h control0 i t
  filter_upwards [hcutRoot, hdownRoot, hupRoot, hXCE, hDownCE, hUpCE,
      hCutStageCE] with source hcutRoot hdownRoot hupRoot hXCE hDownCE hUpCE hCutStageCE
  intro count hcross hspan hshort
  have hspanC : ReferenceFirstCollectionReadyStream.startTime
      (rate := rate) source rewards C_star C_h + count ≤ p.T := by
    simpa only [ReferenceFirstCollectionReadyStream.startTime] using hspan
  have hshortC : (ReferenceFirstLiveConfirmationHistory.firstLiveWindow
      (ReferenceFirstCollectionReadyStream.actualEpoch
        (rate := rate) source rewards C_star C_h hcross count hspanC).records).length < count := by
    simpa only [ReferenceFirstCollectionReadyStream.actualEpoch] using hshort
  have hCutData := hcutRoot count hcross hspanC hshortC
  dsimp only at hCutData
  obtain ⟨dC, oldC, memoryC, cutC, hcutC, hwindowC, hheadC,
    htimeC, hrowsC, hselectedC, hrewardsC, hregsC, hownedC, hbaseC,
    hliveC, hpayloadC, hfamilyC, hpreparedC, hrecordC, hchosenC,
    hstartC, hclassC⟩ := hCutData
  have hOrigin := ReferenceFirstCollectionFormationOrigin.actual_initialized_first_collection_formation_origin
    rate source rewards C_star C_h count hcross hspan hshort
  let d := Classical.choose hOrigin
  have hOriginSpec := Classical.choose_spec hOrigin
  rcases hOriginSpec with ⟨_, _, _, _, _, _, _, _, hboundaries⟩
  let out := d.stream
  let E := ReferenceFirstCollectionEpochAlignment.actualFirstCollectionRun
    rate source rewards C_star C_h hcross count hspan
  let w := (ReferenceFirstLiveConfirmationHistory.firstLiveWindow E.records).length
  let B := ReferenceCollectionPhaseHistory.collectionWindow E.records w
  have hwindow : out.window = B := by
    simpa only [ReferenceFirstCollectionReadyStream.actualWindow,
      ReferenceFirstCollectionReadyStream.actualEpoch] using out.windowIsActual
  have hcutEq : cutC = out.cutoff.cut := by
    calc
      cutC = dC.stream.cutoff.cut := hcutC
      _ = d.stream.cutoff.cut := by
        apply Option.some.inj
        exact dC.stream.cutoff.cutIndex.symm.trans d.stream.cutoff.cutIndex
  have hcutInput : cutC.input = out.cutoff.cut.input :=
    congrArg (fun record : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => record.input) hcutEq
  have hcutActual :
      ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
        out.cutoff.cut.input.time source = some out.cutoff.cut := by
    calc
      _ = ReferenceSourcePrefixHistoryFiltration.actualRecord rate rewards C_star C_h
          cutC.input.time source := by rw [hcutInput]
      _ = some cutC := hrecordC
      _ = some out.cutoff.cut := congrArg some hcutEq
  have hcutLive : out.cutoff.cut.input.state.coordinator = .live hregsC hownedC hbaseC := by
    rw [← hcutInput]
    exact hliveC
  refine ⟨d, ?_⟩
  dsimp only [out, E, w, B]
  refine ⟨hwindow, ?_, ?_, ?_⟩
  · intro i
    have hi := hclassC i
    have hOldCut := OLD_iff_cutoff_of_live (p := p) (rate := rate)
      rewards C_star C_h i out.cutoff.cut.input.time hcutActual hregsC hownedC hbaseC hcutLive
    have hFormedCut := FORMED_iff_cutoff_of_live (p := p) (rate := rate)
      rewards C_star C_h i out.cutoff.cut.input.time hcutActual hregsC hownedC hbaseC hcutLive
    have hXStage := X_eq_staged_on_live (p := p) (rate := rate)
      rewards C_star C_h i out.cutoff.cut.input.time hcutActual hregsC hownedC hbaseC hcutLive
    have hXCutCE := hXCE i out.cutoff.cut.input.time
    have hStageCutCE := hCutStageCE i out.cutoff.cut.input.time
    have hOldIndicator :
        (OLD (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time).indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i out.cutoff.cut.input.time) source =
        (ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
          (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time).indicator
          (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i out.cutoff.cut.input.time) source := by
      by_cases hz : source ∈ OLD (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time
      · simp [hz, hOldCut.mp hz]
      · have hz' : source ∉ ReferenceFirstCutoffStageConditionalService.cutoffOldStageSupport
            (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time :=
          fun hs => hz (hOldCut.mpr hs)
        simp [hz, hz']
    have hFormedIndicator :
        (FORMED (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time).indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i out.cutoff.cut.input.time) source =
        (ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
          (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time).indicator
          (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i out.cutoff.cut.input.time) source := by
      by_cases hz : source ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time
      · simp [hz, hFormedCut.mp hz]
      · have hz' : source ∉ ReferenceFirstCutoffStageConditionalService.cutoffFormedUpStageSupport
            (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time :=
          fun hs => hz (hFormedCut.mpr hs)
        simp [hz, hz']
    have hsameCE :
        μ[X (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 out.cutoff.cut.input.time] source =
        μ[ReferenceFirstCutoffStageConditionalService.stagedReadout
            (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 out.cutoff.cut.input.time] source := by
      calc
        _ = (OLD (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time).indicator
              (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
                (rate := rate) rewards C_star C_h control0 i out.cutoff.cut.input.time) source +
            (FORMED (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time).indicator
              (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
                (rate := rate) rewards C_star C_h control0 i out.cutoff.cut.input.time) source := hXCutCE
        _ = _ := by rw [hOldIndicator, hFormedIndicator]
        _ = _ := hStageCutCE.symm
    rcases hi with ⟨hOldClass, hFormedClass, _, _, hCservice⟩
    have hCservice' : μ[ReferenceFirstCutoffStageConditionalService.stagedReadout
        (p := p) (rate := rate) rewards C_star C_h i out.cutoff.cut.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 out.cutoff.cut.input.time] source =
        (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
          rewards out.cutoff.cut.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
      simpa only [hcutInput] using hCservice
    exact ⟨hXStage, hsameCE.trans hCservice'⟩
  · intro n hn i hip
    have hnB : n.val < B.length := by
      rw [← hwindow]
      exact Nat.lt_of_lt_of_le n.isLt out.withinWindow
    let nB : Fin B.length := ⟨n.val, hnB⟩
    have hF := hboundaries n hn i hip
    rcases hF with ⟨r, incoming, cell, old, memory, hlookup, htime, hrows,
      hselected, hrewards, hincoming, hiIncoming, hReady, hservice, hfi,
      hstatus, hdomain, hS, hdelta, hbacklog, hmass, hbank, hcompleted,
      hlast, hup, hformed⟩
    have hlookupB : B[nB.val]? = some r := by
      simpa only [out, d, hwindow] using hlookup
    have hgetB : B[nB.val]? = some B[nB.val] := List.getElem?_eq_getElem hnB
    have hrB : r = B[nB.val] := Option.some.inj (hlookupB.symm.trans hgetB)
    have hReadyB : ReferenceContinuingCollectionStartDomains.continuingCollectionReadyDomain
        B[nB.val].input out.payload incoming out.saved := by
      simpa only [out, d, nB, hrB] using hReady
    have hfiB : B[nB.val].input.state.followers i = .ordinary old memory := by
      simpa only [nB, hrB] using hfi
    have hrecordB := actualRecord_window (p := p) (rate := rate)
      rewards C_star C_h count hcross hspan hshort nB
    have hrecordR : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h r.input.time source = some r := by
      rw [hrB]
      exact hrecordB
    have htimeRecord : B[nB.val].input.time = r.input.time :=
      congrArg (fun q : ReferenceActivePhysicalHorizon.RoundRecord (p := p) (rate := rate) => q.input.time)
        hrB.symm
    have hnoneWord := ReferenceCollectionDownReadySupportMeasurability.actual_first_collection_mem_collectionDownReadySupport
      rate source rewards C_star C_h count hcross hspan hshort nB (by simpa [nB] using hn)
      out.payload incoming out.saved hReadyB i old memory hfiB hiIncoming
    let s := ReferenceInitializationRun.elapsed p
      (ReferenceInitializationRun.output
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate)).completed
    have hserviceDown := hdownRoot count hcross s rfl hspan hshort nB
      (by simpa [nB] using hn) out.payload incoming out.saved hReadyB i old memory hfiB hiIncoming
    have hserviceUpBase := fun hpos => hupRoot count hcross s rfl hspan hshort nB
      (by simpa [nB] using hn) out.payload incoming out.saved hReadyB i old memory hfiB
      hiIncoming hpos
    rcases hlast with ⟨hnone, hS0, hdelta0, hbacklog0⟩ | hsome
    · have hDown := hserviceDown hnone
      rcases hDown with ⟨wD, hwD, hreadRecord, hserviceCE⟩
      have hQ : source ∈ ReferenceCollectionDownReadySupportMeasurability.collectionDownReadySupport
          (p := p) (rate := rate) rewards C_star C_h i r.input.time
          (CoordinatorLocalArmChoice.storedDownFlatWord out.payload i) := by
        simpa [hrB] using hnoneWord hnone
      have hOldiff := OLD_iff_lastDown (p := p) (rate := rate)
        rewards C_star C_h i r.input.time hrecordR out.payload incoming out.saved
        old memory hReady hfi hQ
      have hOld := hOldiff.mpr hnone
      have hFormedNot : source ∉ FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time := by
        intro hFormed
        exact (Set.disjoint_left.mp
          (disjoint_OLD_FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time)) hOld hFormed
      have hFormediff : source ∈ FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time ↔
          old.lastDown ≠ none := by
        constructor
        · intro hf
          exact False.elim (hFormedNot hf)
        · intro hnne
          exact False.elim (hnne hnone)
      have hXdown := X_eq_down_test (p := p) (rate := rate)
        rewards C_star C_h i r.input.time hrecordR hOld hFormedNot
      have hXroot := hXCE i r.input.time
      have hDownRootCE := hDownCE i r.input.time
      have hDownFresh :
          ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
            (rate := rate) rewards C_star C_h control0 i r.input.time source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards r.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) :=
        hDownRootCE.symm.trans (by rw [← htimeRecord]; exact hserviceCE)
      have hXCEroot : μ[X (p := p) (rate := rate) rewards C_star C_h i r.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 r.input.time] source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards r.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
        calc
          _ = (OLD (p := p) (rate := rate) rewards C_star C_h i r.input.time).indicator
                (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
                  (rate := rate) rewards C_star C_h control0 i r.input.time) source +
              (FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time).indicator
                (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
                  (rate := rate) rewards C_star C_h control0 i r.input.time) source := hXroot
          _ = _ := by simp [Set.indicator_of_mem hOld, Set.indicator_of_notMem hFormedNot]
          _ = _ := hDownFresh
      have hNoUpWitness : old.lastDown = some (out.payload.downRecord i) →
          ∃ U : UpRecord p rate, U.val = ActiveFollowerQueueOperation.upOfferFields old ∧
            1 ≤ U.val.sigma := by
        intro hsome'
        rw [hnone] at hsome'
        cases hsome'
      have hNoUpTest : old.lastDown ≠ none →
          X (p := p) (rate := rate) rewards C_star C_h i r.input.time source =
            if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (r.input.row.2 r.input.time).1 =
                  ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
              ReferenceActiveAffinePositiveTest.upPositive r.input = true then 1 else 0 := by
        intro hnne
        exact False.elim (hnne hnone)
      refine ⟨r, incoming, old, memory, hlookup, htime, hrows, hselected,
        hrewards, hincoming, hiIncoming, hReady, hfi, hstatus, hdomain,
        Or.inl ⟨hnone, hS0, hdelta0, hbacklog0⟩, hNoUpWitness, hOldiff,
        hFormediff, fun _ => hXdown, hNoUpTest, hXCEroot⟩
    · have hformedData := hformed hsome
      have haccepted : ReferencePrelaunchFollower.acceptedStart old = s + 1 :=
        hformedData.2.1
      have hpos : 1 ≤ ReferencePrelaunchFollower.acceptedStart old := by omega
      let Uorigin := Classical.choose (hup hsome)
      have hUoriginSpec := Classical.choose_spec (hup hsome)
      have hUorigin : Uorigin.val = ActiveFollowerQueueOperation.upOfferFields old := hUoriginSpec.1
      have hUoriginSigma : 1 ≤ Uorigin.val.sigma := hUoriginSpec.2.1
      obtain ⟨Uservice, hUservice, hUserviceSigma, hUS, hserviceCE⟩ :=
        hserviceUpBase hpos
      have hUeq : Uorigin = Uservice := by
        apply Subtype.ext
        exact hUorigin.trans hUservice.symm
      have hUSrecord : source ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
          (p := p) (rate := rate) rewards C_star C_h i r.input.time Uservice := by
        rw [← htimeRecord]
        exact hUS
      have hUSorigin : source ∈ ReferenceCollectionUpReadySupportMeasurability.collectionUpReadySupport
          (p := p) (rate := rate) rewards C_star C_h i r.input.time Uorigin := by
        rw [hUeq]
        exact hUSrecord
      have hFormediff := FORMED_iff_lastDown_ne (p := p) (rate := rate)
        rewards C_star C_h i r.input.time hrecordR out.payload incoming out.saved old memory
        hReady hfi hUSorigin
      have hlastNe : old.lastDown ≠ none := by
        intro heq
        rw [heq] at hsome
        cases hsome
      have hFormed := hFormediff.mpr hlastNe
      have hOldNot : source ∉ OLD (p := p) (rate := rate) rewards C_star C_h i r.input.time := by
        intro hOld
        exact (Set.disjoint_left.mp
          (disjoint_OLD_FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time)) hOld hFormed
      have hOldiff : source ∈ OLD (p := p) (rate := rate) rewards C_star C_h i r.input.time ↔
          old.lastDown = none := by
        constructor
        · intro hOld
          exact False.elim (hOldNot hOld)
        · intro hnone
          rw [hnone] at hsome
          cases hsome
      have hXup := X_eq_up_test (p := p) (rate := rate)
        rewards C_star C_h i r.input.time hrecordR hOldNot hFormed
      have hXroot := hXCE i r.input.time
      have hUpRootCE := hUpCE i r.input.time
      have hUpFresh :
          ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
            (rate := rate) rewards C_star C_h control0 i r.input.time source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards r.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) :=
        hUpRootCE.symm.trans (by rw [← htimeRecord]; exact hserviceCE)
      have hXCEroot : μ[X (p := p) (rate := rate) rewards C_star C_h i r.input.time |
          ReferenceSourceCurrentControlFreshness.m_t p control0 r.input.time] source =
          (ReferenceFirstCollectionUpConditionalService.positiveRewardCount
            rewards r.input.time : ℝ) / (8 * (p.m - 1 : ℝ) * p.K) := by
        calc
          _ = (OLD (p := p) (rate := rate) rewards C_star C_h i r.input.time).indicator
                (ReferenceFirstCollectionDownConditionalService.actualFirstCollectionDownFreshSection
                  (rate := rate) rewards C_star C_h control0 i r.input.time) source +
              (FORMED (p := p) (rate := rate) rewards C_star C_h i r.input.time).indicator
                (ReferenceFirstCollectionUpConditionalService.actualFirstCollectionUpFreshSection
                  (rate := rate) rewards C_star C_h control0 i r.input.time) source := hXroot
          _ = _ := by simp [Set.indicator_of_notMem hOldNot, Set.indicator_of_mem hFormed]
          _ = _ := hUpFresh
      have hDownTest : old.lastDown = none →
          X (p := p) (rate := rate) rewards C_star C_h i r.input.time source =
            if PublicDiscreteDraws.selectedFollowerDraw p.two_le_m p.m_lt_K
                (r.input.row.2 r.input.time).1 =
                  ReferenceFirstCollectionUpConditionalService.followerIndex i ∧
              ReferenceActiveAffinePositiveTest.downPositive r.input = true then 1 else 0 := by
        intro hnone
        rw [hnone] at hsome
        cases hsome
      refine ⟨r, incoming, old, memory, hlookup, htime, hrows, hselected,
        hrewards, hincoming, hiIncoming, hReady, hfi, hstatus, hdomain,
        Or.inr hsome, (fun _ => ⟨Uorigin, hUorigin, hUoriginSigma⟩), hOldiff, hFormediff,
        hDownTest, fun _ => hXup, hXCEroot⟩
  · intro n hn i hnot
    obtain ⟨j, r, incoming, cell, hj, hlookup, hservice, hprev⟩ := out.cell_at n hn
    have hnB : n.val < B.length := by
      rw [← hwindow]
      exact Nat.lt_of_lt_of_le n.isLt out.withinWindow
    let nB : Fin B.length := ⟨n.val, hnB⟩
    have hrecord := actualRecord_window (p := p) (rate := rate)
      rewards C_star C_h count hcross hspan hshort nB
    have hlookupB : B[nB.val]? = some r := by
      simpa only [out, d, hwindow] using hlookup
    have hget : B[nB.val]? = some B[nB.val] := List.getElem?_eq_getElem hnB
    have hr : r = B[nB.val] := Option.some.inj (hlookupB.symm.trans hget)
    have hrecordR : ReferenceSourcePrefixHistoryFiltration.actualRecord
        rate rewards C_star C_h r.input.time source = some r := by
      rw [hr]
      simpa only [hwindow] using hrecord
    have hready := cell.readyInput
    have hnotIncoming : i ∉ incoming.pending := by
      rw [hprev]
      exact hnot
    have hOld := no_OLD_of_notPending (p := p) (rate := rate)
      rewards C_star C_h i r.input.time hrecordR out.payload incoming out.saved hready hnotIncoming
    have hFormed := no_FORMED_of_notPending (p := p) (rate := rate)
      rewards C_star C_h i r.input.time hrecordR out.payload incoming out.saved hready hnotIncoming
    have hzero := X_eq_zero_of_no_support (p := p) (rate := rate)
      rewards C_star C_h i r.input.time hOld hFormed
    have hzeroB : X (p := p) (rate := rate) rewards C_star C_h i
        B[nB.val].input.time source = 0 := by
      simpa only [hr] using hzero
    simpa only [out, d, hwindow] using hzeroB

end Bandits.Support.ReferenceFirstCollectionStagedConditionalService

end
