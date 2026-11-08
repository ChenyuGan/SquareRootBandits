/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveActualFlagSections

/-!
# First-live guarded conditional service

Sources: `sources/zip4/manuscript/05_binary_transport.tex:74-124,293-345`,
`sources/zip4/manuscript/06_interruptions.tex:376-426,435-492`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

The event is the literal intersection of the actual first-live branch and the
actual release-support event. Conditional expectations remain on the original
source law and the strict source analysis prefix. No reachability, normalization,
whole stopped-support coverage, or source-theorem closure is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped ENNReal

namespace Bandits.Support.ReferenceFirstLiveGuardedConditionalService

abbrev SourceInput := BootstrapPrivateRoundStreams.SourceInput
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (control0 : TimeControl p)
    (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p)) (s : ℕ)
    (hs : s ≤ t.val)

local notation "E" =>
  ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch
    rate rewards C_star C_h control0 i t q s hs
local notation "S" =>
  ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseSupport
    rate rewards C_star C_h
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "m" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)

/-- The literal first-live branch intersected with the actual release support.
The support index `b` remains an explicit argument. -/
def firstLiveGuardedEvent (b : ℕ) : Set (SourceInput p) :=
  E ∩ S b t i

/-- The indicator of the same guarded event, under the original source law. -/
def firstLiveGuardedEventIndicator (b : ℕ) (source : SourceInput p) : ℝ :=
  (firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b).indicator
    (fun _ => (1 : ℝ)) source

/-- The literal indicator of the actual UP source flag. -/
def actualUpSourceIndicator (source : SourceInput p) : ℝ :=
  if ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t source
  then (1 : ℝ) else 0

/-- The literal indicator of the actual DATA source flag. -/
def actualDataSourceIndicator (source : SourceInput p) : ℝ :=
  if ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t source
  then (1 : ℝ) else 0

/-- The literal indicator of the actual release source flag. -/
def actualReleaseSourceIndicator (source : SourceInput p) : ℝ :=
  if ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t source
  then (1 : ℝ) else 0

theorem measurableSet_firstLiveGuardedEvent (b : ℕ) :
    MeasurableSet[m] (firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b) := by
  exact (ReferenceFirstLiveActualFlagSections.firstLiveSourceBranch_measurable
      rate rewards C_star C_h control0 i t q s hs).inter
    (ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseSupport_measurableSet
      rate rewards C_star C_h control0 b t i)

private theorem prefixField_le_sourceBorel :
    m ≤ (inferInstance : MeasurableSpace (SourceInput p)) := by
  rw [ReferenceSourcePhysicalFlagConditionalLaw.sourcePrefixField_eq_m_t control0 t]
  exact (ReferenceSourceCurrentControlFreshness.measurable_c_t (p := p) control0 t).comap_le

private theorem actualUpControlSection_measurable_source :
    Measurable (ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t) := by
  exact (ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection_stronglyMeasurable
      rate rewards C_star C_h control0 i t).measurable.mono
    (prefixField_le_sourceBorel control0 t) le_rfl

private theorem measurable_firstLiveGuardedIndicator (b : ℕ) :
    Measurable[m] (firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b) :=
  measurable_const.indicator (measurableSet_firstLiveGuardedEvent
    rate rewards C_star C_h control0 i t q s hs b)

private theorem stronglyMeasurable_firstLiveGuardedIndicator (b : ℕ) :
    StronglyMeasurable[m] (firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b) :=
  (measurable_firstLiveGuardedIndicator rate rewards C_star C_h control0 i t q s hs b).stronglyMeasurable

private theorem measurable_firstLiveGuardedIndicator_source (b : ℕ) :
    Measurable (firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b) :=
  (measurable_firstLiveGuardedIndicator rate rewards C_star C_h control0 i t q s hs b).mono
    (prefixField_le_sourceBorel control0 t) le_rfl

private theorem actualFlagIndicators_measurable (control0 : TimeControl p) :
    Measurable (actualUpSourceIndicator rate rewards C_star C_h i t) ∧
      Measurable (actualDataSourceIndicator rate rewards C_star C_h i t) ∧
      Measurable (actualReleaseSourceIndicator rate rewards C_star C_h i t) := by
  have hflags := ReferenceSourcePrefixHistoryFiltration.measurable_flags
    rate rewards C_star C_h control0 i t
  refine ⟨?_, ?_, ?_⟩
  · change Measurable (fun z => if
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z
      then (1 : ℝ) else 0)
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (measurable_fst.comp hflags)
  · change Measurable (fun z => if
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z
      then (1 : ℝ) else 0)
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (measurable_fst.comp (measurable_snd.comp hflags))
  · change Measurable (fun z => if
      ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t z
      then (1 : ℝ) else 0)
    exact (measurable_of_countable (fun b : Bool => if b then (1 : ℝ) else 0)).comp
      (measurable_snd.comp (measurable_snd.comp hflags))

private theorem actualFlagIndicators_bounded :
    (∀ z, ‖actualUpSourceIndicator rate rewards C_star C_h i t z‖ ≤ 1) ∧
      (∀ z, ‖actualDataSourceIndicator rate rewards C_star C_h i t z‖ ≤ 1) ∧
      (∀ z, ‖actualReleaseSourceIndicator rate rewards C_star C_h i t z‖ ≤ 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro z <;> dsimp only [actualUpSourceIndicator, actualDataSourceIndicator, actualReleaseSourceIndicator] <;>
    split <;> norm_num

private theorem integrable_measurable_norm_le_one {α : Type*}
    [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    (f : α → ℝ) (hf : Measurable f) (hbound : ∀ x, ‖f x‖ ≤ 1) : Integrable f ν := by
  exact (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)

theorem firstLiveGuardedEventIndicator_integrable (b : ℕ) :
    Integrable (firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b) μ := by
  have hmeas : Measurable (firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b) :=
    measurable_firstLiveGuardedIndicator_source rate rewards C_star C_h control0 i t q s hs b
  apply integrable_measurable_norm_le_one _ hmeas
  intro z
  by_cases hz : z ∈ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b <;> simp [firstLiveGuardedEventIndicator, Set.indicator, hz]

theorem firstLiveGuarded_flagProducts_integrable (b : ℕ) :
    Integrable (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualUpSourceIndicator rate rewards C_star C_h i t z) μ ∧
      Integrable (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualDataSourceIndicator rate rewards C_star C_h i t z) μ ∧
      Integrable (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualReleaseSourceIndicator rate rewards C_star C_h i t z) μ := by
  have hG := measurable_firstLiveGuardedIndicator_source rate rewards C_star C_h control0 i t q s hs b
  have hX := actualFlagIndicators_measurable rate rewards C_star C_h i t control0
  have hproducts :
      (∀ z, ‖firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualUpSourceIndicator rate rewards C_star C_h i t z‖ ≤ 1) ∧
        (∀ z, ‖firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualDataSourceIndicator rate rewards C_star C_h i t z‖ ≤ 1) ∧
        (∀ z, ‖firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualReleaseSourceIndicator rate rewards C_star C_h i t z‖ ≤ 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> intro z <;>
      by_cases hz : z ∈ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b <;>
      simp [firstLiveGuardedEventIndicator, Set.indicator, hz,
        actualUpSourceIndicator, actualDataSourceIndicator, actualReleaseSourceIndicator] <;>
      split_ifs <;> norm_num
  refine ⟨?_, ?_, ?_⟩
  · exact integrable_measurable_norm_le_one _ (hG.mul hX.1) hproducts.1
  · exact integrable_measurable_norm_le_one _ (hG.mul hX.2.1) hproducts.2.1
  · exact integrable_measurable_norm_le_one _ (hG.mul hX.2.2) hproducts.2.2

/-- On the literal first-live event, the actual conditional expectations are
the same computed whole-control masses as the actual sections. The conditional
equalities are only asserted almost everywhere under the original source law. -/
theorem actual_condExp_on_firstLiveBranch :
    ∀ᵐ z ∂μ, ∀ hz : z ∈ E,
      let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
        rate rewards C_star C_h control0 i t q s hs z hz
      let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
        rate rewards C_star C_h control0 i t q s hs z hz
      let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
        rate rewards C_star C_h q t s hs control0 i x hx
      let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
        rate rewards C_star C_h q t s hs control0 i x hx
      let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
      let upMass := ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row
      let dataMass := ReleaseRoundKernel.chi row
        (selected0.view.payload.assignment.assigned i) / (2 * (p.K : ℝ))
      μ[actualUpSourceIndicator rate rewards C_star C_h i t | m] z = upMass ∧
        μ[actualDataSourceIndicator rate rewards C_star C_h i t | m] z = dataMass ∧
        μ[actualReleaseSourceIndicator rate rewards C_star C_h i t | m] z = upMass + dataMass ∧
        ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤ upMass := by
  filter_upwards
    [ReferenceSourcePhysicalFlagConditionalLaw.actual_up_condExp
        rate rewards C_star C_h control0 i t,
      ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
        rate rewards C_star C_h control0 i t,
      ReferenceSourcePhysicalFlagConditionalLaw.actual_release_condExp
        rate rewards C_star C_h control0 i t] with z hup hdata hrelease
  intro hz
  have hsections :=
    ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
      rate rewards C_star C_h control0 i t q s hs z hz
  exact ⟨hup.trans hsections.1,
    hdata.trans hsections.2.1,
    hrelease.trans hsections.2.2.1,
    le_trans hsections.2.2.2 hsections.1.le⟩

/-- Pull out the exact event `E ∩ S_b` from each actual source flag. The actual
control sections are retained on the whole source carrier; only the literal
event indicator guards them. -/
theorem firstLiveGuarded_condExp_pullout (b : ℕ) :
    (μ[fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualUpSourceIndicator rate rewards C_star C_h i t z | m] =ᵐ[μ]
        fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z) ∧
      (μ[fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualDataSourceIndicator rate rewards C_star C_h i t z | m] =ᵐ[μ]
        fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z) ∧
      (μ[fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualReleaseSourceIndicator rate rewards C_star C_h i t z | m] =ᵐ[μ]
        fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
          rate rewards C_star C_h control0 i t z) := by
  have hproducts := firstLiveGuarded_flagProducts_integrable
    rate rewards C_star C_h control0 i t q s hs b
  have hup := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_firstLiveGuardedIndicator rate rewards C_star C_h control0 i t q s hs b)
    hproducts.1
    (ReferenceSourcePhysicalFlagConditionalLaw.actualUp_observation_integrable
      rate rewards C_star C_h control0 i t)
  have hdata := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_firstLiveGuardedIndicator rate rewards C_star C_h control0 i t q s hs b)
    hproducts.2.1
    (ReferenceSourcePhysicalFlagConditionalLaw.actualData_observation_integrable
      rate rewards C_star C_h control0 i t)
  have hrelease := condExp_mul_of_stronglyMeasurable_left
    (stronglyMeasurable_firstLiveGuardedIndicator rate rewards C_star C_h control0 i t q s hs b)
    hproducts.2.2
    (ReferenceSourcePhysicalFlagConditionalLaw.actualRelease_observation_integrable
      rate rewards C_star C_h control0 i t)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ =ᵐ[μ] (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          μ[actualUpSourceIndicator rate rewards C_star C_h i t | m] z) := hup
      _ =ᵐ[μ] (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
            rate rewards C_star C_h control0 i t z) := by
        filter_upwards [ReferenceSourcePhysicalFlagConditionalLaw.actual_up_condExp
          rate rewards C_star C_h control0 i t] with z hz
        have hz' : μ[actualUpSourceIndicator rate rewards C_star C_h i t | m] z =
            ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
              rate rewards C_star C_h control0 i t z := by
          change μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualUp
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) | m] z = _
          exact hz
        exact congrArg (fun y : ℝ =>
          firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * y)
          hz'
  · calc
      _ =ᵐ[μ] (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          μ[actualDataSourceIndicator rate rewards C_star C_h i t | m] z) := hdata
      _ =ᵐ[μ] (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t z) := by
        filter_upwards [ReferenceSourcePhysicalFlagConditionalLaw.actual_data_condExp
          rate rewards C_star C_h control0 i t] with z hz
        have hz' : μ[actualDataSourceIndicator rate rewards C_star C_h i t | m] z =
            ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
              rate rewards C_star C_h control0 i t z := by
          change μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualData
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) | m] z = _
          exact hz
        exact congrArg (fun y : ℝ =>
          firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * y)
          hz'
  · calc
      _ =ᵐ[μ] (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          μ[actualReleaseSourceIndicator rate rewards C_star C_h i t | m] z) := hrelease
      _ =ᵐ[μ] (fun z => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
            rate rewards C_star C_h control0 i t z) := by
        filter_upwards [ReferenceSourcePhysicalFlagConditionalLaw.actual_release_condExp
          rate rewards C_star C_h control0 i t] with z hz
        have hz' : μ[actualReleaseSourceIndicator rate rewards C_star C_h i t | m] z =
            ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
              rate rewards C_star C_h control0 i t z := by
          change μ[(fun source => if ReferenceSourcePrefixHistoryFiltration.actualRelease
            rate rewards C_star C_h i t source then (1 : ℝ) else 0) | m] z = _
          exact hz
        exact congrArg (fun y : ℝ =>
          firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * y)
          hz'

/-- On the guarded event, the pulled-out sections are the same UP/DATA/release
masses and auxiliary-arm lower bound as on `E`. -/
theorem firstLiveGuarded_condExp_values_on_event (b : ℕ) :
    ∀ᵐ z ∂μ, ∀ hzG : z ∈ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b,
      let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
        rate rewards C_star C_h control0 i t q s hs z hzG.1
      let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
        rate rewards C_star C_h control0 i t q s hs z hzG.1
      let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
        rate rewards C_star C_h q t s hs control0 i x hx
      let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
        rate rewards C_star C_h q t s hs control0 i x hx
      let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
      let upMass := ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row
      let dataMass := ReleaseRoundKernel.chi row
        (selected0.view.payload.assignment.assigned i) / (2 * (p.K : ℝ))
      μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualUpSourceIndicator rate rewards C_star C_h i t w | m] z = upMass ∧
        μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualDataSourceIndicator rate rewards C_star C_h i t w | m] z = dataMass ∧
        μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualReleaseSourceIndicator rate rewards C_star C_h i t w | m] z = upMass + dataMass ∧
        ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤ upMass := by
  have hpull := firstLiveGuarded_condExp_pullout
    rate rewards C_star C_h control0 i t q s hs b
  filter_upwards [hpull.1, hpull.2.1, hpull.2.2] with z hup hdata hrelease
  intro hzG
  have hi : firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z = 1 := by
    change z ∈ E ∩ S b t i at hzG
    simp [firstLiveGuardedEventIndicator, firstLiveGuardedEvent, Set.indicator, hzG]
  have hsections :=
    ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
      rate rewards C_star C_h control0 i t q s hs z hzG.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualUpSourceIndicator rate rewards C_star C_h i t w | m] z =
          firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := hup
      _ = _ := by simpa only [hi, one_mul] using hsections.1
  · calc
      μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualDataSourceIndicator rate rewards C_star C_h i t w | m] z =
          firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t z := hdata
      _ = _ := by simpa only [hi, one_mul] using hsections.2.1
  · calc
      μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualReleaseSourceIndicator rate rewards C_star C_h i t w | m] z =
          firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
            rate rewards C_star C_h control0 i t z := hrelease
      _ = _ := by simpa only [hi, one_mul] using hsections.2.2.1
  · exact le_trans hsections.2.2.2 hsections.1.le

/-- Outside `G`, each guarded conditional mean vanishes almost everywhere. -/
theorem firstLiveGuarded_condExp_zero_off_event (b : ℕ) :
    (∀ᵐ z ∂μ,
      z ∉ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b →
        μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w *
          actualUpSourceIndicator rate rewards C_star C_h i t w | m] z = 0) ∧
      (∀ᵐ z ∂μ,
        z ∉ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b →
          μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w *
            actualDataSourceIndicator rate rewards C_star C_h i t w | m] z = 0) ∧
      (∀ᵐ z ∂μ,
        z ∉ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b →
          μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w *
            actualReleaseSourceIndicator rate rewards C_star C_h i t w | m] z = 0) := by
  have hpull := firstLiveGuarded_condExp_pullout
    rate rewards C_star C_h control0 i t q s hs b
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hpull.1] with z hz hnot
    change z ∉ E ∩ S b t i at hnot
    calc
      _ = firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
            rate rewards C_star C_h control0 i t z := hz
      _ = 0 := by
        simp [firstLiveGuardedEventIndicator, firstLiveGuardedEvent, Set.indicator, hnot]
  · filter_upwards [hpull.2.1] with z hz hnot
    change z ∉ E ∩ S b t i at hnot
    calc
      _ = firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t z := hz
      _ = 0 := by
        simp [firstLiveGuardedEventIndicator, firstLiveGuardedEvent, Set.indicator, hnot]
  · filter_upwards [hpull.2.2] with z hz hnot
    change z ∉ E ∩ S b t i at hnot
    calc
      _ = firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
          ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
            rate rewards C_star C_h control0 i t z := hz
      _ = 0 := by
        simp [firstLiveGuardedEventIndicator, firstLiveGuardedEvent, Set.indicator, hnot]

/-- Integrating the three proved conditional identities gives the exact
guarded source means, with the original source law and actual section values. -/
theorem firstLiveGuarded_integral_identities (b : ℕ) :
    (∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualUpSourceIndicator rate rewards C_star C_h i t z ∂μ) =
        ∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z ∂μ ∧
      (∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualDataSourceIndicator rate rewards C_star C_h i t z ∂μ) =
        ∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z ∂μ ∧
      (∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * actualReleaseSourceIndicator rate rewards C_star C_h i t z ∂μ) =
        ∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z * ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
          rate rewards C_star C_h control0 i t z ∂μ := by
  have hmeas : m ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    prefixField_le_sourceBorel control0 t
  have hident := firstLiveGuarded_condExp_pullout
    rate rewards C_star C_h control0 i t q s hs b
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = ∫ z, μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualUpSourceIndicator rate rewards C_star C_h i t w | m] z ∂μ :=
        (integral_condExp hmeas).symm
      _ = _ := integral_congr_ae hident.1
  · calc
      _ = ∫ z, μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualDataSourceIndicator rate rewards C_star C_h i t w | m] z ∂μ :=
        (integral_condExp hmeas).symm
      _ = _ := integral_congr_ae hident.2.1
  · calc
      _ = ∫ z, μ[fun w => firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b w * actualReleaseSourceIndicator rate rewards C_star C_h i t w | m] z ∂μ :=
        (integral_condExp hmeas).symm
      _ = _ := integral_congr_ae hident.2.2

/-- Integrating the guarded UP identity also gives a lower estimate on `G`.
The scalar integrand uses positivity of the actual UP section, which on `E`
is exactly positivity of the computed auxiliary reward indicator. Thus the
integrated estimate keeps the original source measure and does not extend the
dependent selector outside its branch. -/
theorem firstLiveGuarded_upLowerCoefficient_eq_auxiliary (b : ℕ) :
    ∀ z, ∀ hzG : z ∈ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b,
      (if 0 < ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z then
        (1 : ℝ) / (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) else 0) =
      let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
        rate rewards C_star C_h control0 i t q s hs z hzG.1
      let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
        rate rewards C_star C_h control0 i t q s hs z hzG.1
      let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
        rate rewards C_star C_h q t s hs control0 i x hx
      let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
      ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary /
        (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) := by
  intro z hzG
  let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
    rate rewards C_star C_h control0 i t q s hs z hzG.1
  let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
    rate rewards C_star C_h control0 i t q s hs z hzG.1
  let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
    rate rewards C_star C_h q t s hs control0 i x hx
  let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
    rate rewards C_star C_h q t s hs control0 i x hx
  let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
  let upMass := ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row
  let denominator := 12 * (p.m - 1 : ℝ) * (p.K : ℝ)
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    have hm : (1 : ℝ) ≤ (p.m - 1 : ℝ) := by
      have hm' : (2 : ℝ) ≤ p.m := by exact_mod_cast p.two_le_m
      linarith
    have hK : (0 : ℝ) < p.K := by exact_mod_cast ConstructorDimensions.K_pos p
    positivity
  have hbranch :=
    ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
      rate rewards C_star C_h control0 i t q s hs z hzG.1
  change ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z = upMass ∧
    _ ∧ _ ∧
    ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary / denominator ≤
      ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z at hbranch
  change (if 0 < ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
      rate rewards C_star C_h control0 i t z then (1 : ℝ) / denominator else 0) =
    ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary / denominator
  by_cases haux : 0 < row.val selected0.view.payload.assignment.auxiliary
  · have hchi : ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary = 1 := by
      simp [ReleaseRoundKernel.chi, haux]
    have hlower : (1 : ℝ) / denominator ≤
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z := by
      simpa [hchi] using hbranch.2.2.2
    have hpositive : 0 <
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z :=
      lt_of_lt_of_le (div_pos one_pos hdenominator) hlower
    simp [hpositive, hchi]
  · have hzero : upMass = 0 := by
      simp [upMass, ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula,
        ReleaseRoundKernel.chi, haux]
    have hsectionZero :
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z = 0 := hbranch.1.trans hzero
    simp [hsectionZero, ReleaseRoundKernel.chi, haux]

theorem firstLiveGuarded_integrated_up_lower_bound (b : ℕ) :
    (∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
        (if 0 < ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z then
          (1 : ℝ) / (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) else 0) ∂μ) ≤
      ∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z ∂μ ∧
    (∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
        ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z ∂μ) =
      ∫ z, firstLiveGuardedEventIndicator rate rewards C_star C_h control0 i t q s hs b z *
        actualUpSourceIndicator rate rewards C_star C_h i t z ∂μ := by
  let upSection := ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
    rate rewards C_star C_h control0 i t
  let upIndicator := firstLiveGuardedEventIndicator
    rate rewards C_star C_h control0 i t q s hs b
  let denominator := 12 * (p.m - 1 : ℝ) * (p.K : ℝ)
  let measurableLower : SourceInput p → ℝ := fun z =>
    if 0 < upSection z then (1 : ℝ) / denominator else 0
  have hdenominator : 0 < denominator := by
    dsimp [denominator]
    have hm : (1 : ℝ) ≤ (p.m - 1 : ℝ) := by
      have hm' : (2 : ℝ) ≤ p.m := by exact_mod_cast p.two_le_m
      linarith
    have hK : (0 : ℝ) < p.K := by exact_mod_cast ConstructorDimensions.K_pos p
    positivity
  have hsectionBounds := ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection_bounds
    rate rewards C_star C_h control0 i t
  have hsectionMeas : Measurable upSection := by
    dsimp [upSection]
    exact actualUpControlSection_measurable_source
      rate rewards C_star C_h control0 i t
  have hindicatorMeas : Measurable upIndicator := by
    dsimp [upIndicator]
    exact measurable_firstLiveGuardedIndicator_source
      rate rewards C_star C_h control0 i t q s hs b
  have hlowerMeas : Measurable measurableLower := by
    dsimp [measurableLower]
    exact measurable_const.indicator
      (measurableSet_lt measurable_const hsectionMeas)
  have hsectionNorm : ∀ z, ‖upSection z‖ ≤ 1 := by
    intro z
    have hb := hsectionBounds z
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hsectionProductMeas : Measurable (fun z => upIndicator z * upSection z) :=
    hindicatorMeas.mul hsectionMeas
  have hsectionProductBound : ∀ z, ‖upIndicator z * upSection z‖ ≤ 1 := by
    intro z
    by_cases hz : z ∈ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b
    · have hi : upIndicator z = 1 := by
        dsimp [upIndicator, firstLiveGuardedEventIndicator]
        simp [Set.indicator, hz]
      rw [hi, one_mul]
      exact hsectionNorm z
    · have hi : upIndicator z = 0 := by
        dsimp [upIndicator, firstLiveGuardedEventIndicator]
        simp [Set.indicator, hz]
      rw [hi]
      norm_num
  have hsectionProductIntegrable : Integrable (fun z => upIndicator z * upSection z) μ :=
    integrable_measurable_norm_le_one _ hsectionProductMeas hsectionProductBound
  have hlowerProductMeas : Measurable (fun z => upIndicator z * measurableLower z) :=
    hindicatorMeas.mul hlowerMeas
  have hpointwise : ∀ z, 0 ≤ upIndicator z * measurableLower z ∧
      upIndicator z * measurableLower z ≤ upIndicator z * upSection z := by
    intro z
    by_cases hzG : z ∈ firstLiveGuardedEvent rate rewards C_star C_h control0 i t q s hs b
    · have hi : upIndicator z = 1 := by
        dsimp [upIndicator, firstLiveGuardedEventIndicator]
        simp [Set.indicator, hzG]
      let x := ReferenceFirstLiveActualFlagSections.firstLiveRemainder
        rate rewards C_star C_h control0 i t q s hs z hzG.1
      let hx := ReferenceFirstLiveActualFlagSections.firstLiveRemainder_mem
        rate rewards C_star C_h control0 i t q s hs z hzG.1
      let selected0 := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection
        rate rewards C_star C_h q t s hs control0 i x hx
      let hvalid := ReferenceFirstLiveReleaseCylinderIntegral.baselineSelection_valid
        rate rewards C_star C_h q t s hs control0 i x hx
      let row := ReferenceFirstLiveReleaseGeometry.wholeGridRewardRow rewards t
      let upMass := ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula selected0 hvalid row
      have hbranch :=
        ReferenceFirstLiveActualFlagSections.actual_control_sections_on_first_live_branch
          rate rewards C_star C_h control0 i t q s hs z hzG.1
      change ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z = upMass ∧
        _ ∧ _ ∧
        ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary /
          (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤
            ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
              rate rewards C_star C_h control0 i t z at hbranch
      have hsectionZero_of_auxZero (hnot : ¬ 0 < row.val selected0.view.payload.assignment.auxiliary) :
          upSection z = 0 := by
        have hzero : upMass = 0 := by
          simp [upMass, ReferenceFirstLiveReleaseSliceMass.upReleaseMassFormula,
            ReleaseRoundKernel.chi, hnot]
        calc
          upSection z = upMass := by simpa [upSection] using hbranch.1
          _ = 0 := hzero
      have hlower : measurableLower z ≤ upSection z := by
        by_cases hpos : 0 < upSection z
        · have haux : 0 < row.val selected0.view.payload.assignment.auxiliary := by
            by_contra hnot
            exact (ne_of_gt hpos) (hsectionZero_of_auxZero hnot)
          have hchi : ReleaseRoundKernel.chi row selected0.view.payload.assignment.auxiliary = 1 := by
            simp [ReleaseRoundKernel.chi, haux]
          have hmassLower : (1 : ℝ) / denominator ≤ upSection z := by
            simpa [denominator, hchi, upSection] using hbranch.2.2.2
          simpa [measurableLower, hpos] using hmassLower
        · have hzero : upSection z = 0 := le_antisymm (le_of_not_gt hpos) (hsectionBounds z).1
          simp [measurableLower, hzero]
      have hlowerNonneg : 0 ≤ measurableLower z := by
        dsimp [measurableLower]
        split_ifs with hpos
        · exact div_nonneg (by norm_num) hdenominator.le
        · norm_num
      simpa [hi] using ⟨hlowerNonneg, hlower⟩
    · have hi : upIndicator z = 0 := by
        dsimp [upIndicator, firstLiveGuardedEventIndicator]
        simp [Set.indicator, hzG]
      simp [hi]
  have hlowerProductIntegrable : Integrable (fun z => upIndicator z * measurableLower z) μ := by
    apply hsectionProductIntegrable.mono'
      hlowerProductMeas.aestronglyMeasurable
    filter_upwards [] with z
    calc
      ‖upIndicator z * measurableLower z‖ = upIndicator z * measurableLower z := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpointwise z).1]
      _ ≤ upIndicator z * upSection z := (hpointwise z).2
  have hmono : ∀ᵐ z ∂μ,
      upIndicator z * measurableLower z ≤ upIndicator z * upSection z :=
    Filter.Eventually.of_forall fun z => (hpointwise z).2
  have hident := firstLiveGuarded_integral_identities
    rate rewards C_star C_h control0 i t q s hs b
  constructor
  · exact integral_mono_ae hlowerProductIntegrable hsectionProductIntegrable hmono
  · simpa [upSection, upIndicator, actualUpSourceIndicator] using hident.1.symm

end Bandits.Support.ReferenceFirstLiveGuardedConditionalService

end
