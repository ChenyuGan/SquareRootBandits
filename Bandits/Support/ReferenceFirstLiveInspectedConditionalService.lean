/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveInspectedCoefficients

/-!
# Conditional service on the inspected first-live history

Sources: `sources/zip4/manuscript/07_public_setup.tex:127-164`,
`sources/zip4/manuscript/08_main_theorem.tex:29-47,67-83`, and
`sources/zip4/manuscript/appendix_b_communication.tex:724-798`.

This module moves the actual first-live flag products from the successor
source-prefix field to the explicitly generated inspected analysis field. It
then exposes event-restricted means and testing identities for that same
field. These are internal conditional facts on the original source law; they
do not identify the analysis field with a policy filtration or close a
manuscript assertion.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveInspectedConditionalService

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (i : Fin (p.m - 1)) (t : Fin p.T) (q : Fin (M p))
  (s : ℕ) (hs : s ≤ t.val) (b : ℕ)

local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "Kfield" =>
  ReferenceSourceOwnHistoryContainment.inspectedHistorySpace
    rate rewards C_star C_h t.val (le_of_lt t.isLt)
local notation "mPrefix" =>
  ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)
local notation "Gb" =>
  ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEvent
    rate rewards C_star C_h control0 i t q s hs b
local notation "Iguard" =>
  ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator
    rate rewards C_star C_h control0 i t q s hs b
local notation "Xup" =>
  ReferenceFirstLiveGuardedConditionalService.actualUpSourceIndicator
    rate rewards C_star C_h i t
local notation "Xdata" =>
  ReferenceFirstLiveGuardedConditionalService.actualDataSourceIndicator
    rate rewards C_star C_h i t
local notation "Xrelease" =>
  ReferenceFirstLiveGuardedConditionalService.actualReleaseSourceIndicator
    rate rewards C_star C_h i t
local notation "Kup" =>
  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient
    rate rewards C_star C_h control0 i t q s hs b
local notation "Kdata" =>
  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient
    rate rewards C_star C_h control0 i t q s hs b
local notation "chiE" =>
  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryChi
    rate rewards C_star C_h control0 i t q s hs b
local notation "chiAi" =>
  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi
    rate rewards C_star C_h control0 i t q s hs b
local notation "omega" =>
  ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi
    rate rewards C_star C_h control0 i t q s hs b

/-- The three actual guarded flag products have their computed coefficients
as conditional expectations on the inspected field. The common prefix-field
identities are lifted by the existing history tower; the coefficients are
identified on the whole original source by the global coefficient identities.
-/
theorem firstLiveInspected_guarded_flag_condExp :
    (μ[fun z => Iguard z * Xup z | Kfield] =ᵐ[μ] Kup) ∧
    (μ[fun z => Iguard z * Xdata z | Kfield] =ᵐ[μ] Kdata) ∧
    (μ[fun z => Iguard z * Xrelease z | Kfield] =ᵐ[μ]
      fun z => Kup z + Kdata z) := by
  let hmle : Kfield ≤ (inferInstance : MeasurableSpace
      (BootstrapPrivateRoundStreams.SourceInput p)) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  have hproducts :=
    ReferenceFirstLiveGuardedConditionalService.firstLiveGuarded_flagProducts_integrable
      rate rewards C_star C_h control0 i t q s hs b
  have hpull :=
    ReferenceFirstLiveGuardedConditionalService.firstLiveGuarded_condExp_pullout
      rate rewards C_star C_h control0 i t q s hs b
  have hglobalUp : ∀ z,
      Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
        rate rewards C_star C_h control0 i t z = Kup z := by
    intro z
    calc
      Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
          rate rewards C_star C_h control0 i t z =
        Set.indicator Gb (fun w =>
          ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
            rate rewards C_star C_h control0 i t w) z := by
              by_cases hz : z ∈ Gb <;>
                simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
                  hz]
      _ = Kup z :=
        (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_eq_guarded_actualUpControlSection
          rate rewards C_star C_h control0 i t q s hs b z).symm
  have hglobalData : ∀ z,
      Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
        rate rewards C_star C_h control0 i t z = Kdata z := by
    intro z
    calc
      Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
          rate rewards C_star C_h control0 i t z =
        Set.indicator Gb (fun w =>
          ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t w) z := by
              by_cases hz : z ∈ Gb <;>
                simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
                  hz]
      _ = Kdata z :=
        (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient_eq_guarded_actualDataControlSection
          rate rewards C_star C_h control0 i t q s hs b z).symm
  have hglobalRelease : ∀ z,
      Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
        rate rewards C_star C_h control0 i t z = Kup z + Kdata z := by
    intro z
    calc
      Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
          rate rewards C_star C_h control0 i t z =
        Set.indicator Gb (fun w =>
          ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
            rate rewards C_star C_h control0 i t w) z := by
              by_cases hz : z ∈ Gb <;>
                simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
                  hz]
      _ = Kup z + Kdata z :=
        (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficients_sum_eq_guarded_actualReleaseControlSection
          rate rewards C_star C_h control0 i t q s hs b z).symm
  have hprefixUp :
      μ[fun z => Iguard z * Xup z | mPrefix] =ᵐ[μ] Kup := by
    filter_upwards [hpull.1] with z hz
    calc
      μ[fun w => Iguard w * Xup w | mPrefix] z =
          Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualUpControlSection
            rate rewards C_star C_h control0 i t z := hz
      _ = Kup z := hglobalUp z
  have hprefixData :
      μ[fun z => Iguard z * Xdata z | mPrefix] =ᵐ[μ] Kdata := by
    filter_upwards [hpull.2.1] with z hz
    calc
      μ[fun w => Iguard w * Xdata w | mPrefix] z =
          Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualDataControlSection
            rate rewards C_star C_h control0 i t z := hz
      _ = Kdata z := hglobalData z
  have hprefixRelease :
      μ[fun z => Iguard z * Xrelease z | mPrefix] =ᵐ[μ]
        fun z => Kup z + Kdata z := by
    filter_upwards [hpull.2.2] with z hz
    calc
      μ[fun w => Iguard w * Xrelease w | mPrefix] z =
          Iguard z * ReferenceSourcePhysicalFlagConditionalLaw.actualReleaseControlSection
            rate rewards C_star C_h control0 i t z := hz
      _ = Kup z + Kdata z := hglobalRelease z

  have hTowerUp := ReferenceSourceOwnHistoryContainment.inspectedHistory_condExp_tower
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
    (fun z => Iguard z * Xup z) hproducts.1
  have hTowerData := ReferenceSourceOwnHistoryContainment.inspectedHistory_condExp_tower
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
    (fun z => Iguard z * Xdata z) hproducts.2.1
  have hTowerRelease := ReferenceSourceOwnHistoryContainment.inspectedHistory_condExp_tower
    rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
    (fun z => Iguard z * Xrelease z) hproducts.2.2
  change μ[μ[fun z => Iguard z * Xup z | mPrefix] | Kfield] =ᵐ[μ]
      μ[fun z => Iguard z * Xup z | Kfield] at hTowerUp
  change μ[μ[fun z => Iguard z * Xdata z | mPrefix] | Kfield] =ᵐ[μ]
      μ[fun z => Iguard z * Xdata z | Kfield] at hTowerData
  change μ[μ[fun z => Iguard z * Xrelease z | mPrefix] | Kfield] =ᵐ[μ]
      μ[fun z => Iguard z * Xrelease z | Kfield] at hTowerRelease
  have hinnerUp :
      μ[μ[fun z => Iguard z * Xup z | mPrefix] | Kfield] =ᵐ[μ] μ[Kup | Kfield] :=
    MeasureTheory.condExp_congr_ae hprefixUp
  have hinnerData :
      μ[μ[fun z => Iguard z * Xdata z | mPrefix] | Kfield] =ᵐ[μ] μ[Kdata | Kfield] :=
    MeasureTheory.condExp_congr_ae hprefixData
  have hinnerRelease :
      μ[μ[fun z => Iguard z * Xrelease z | mPrefix] | Kfield] =ᵐ[μ]
        μ[(fun z => Kup z + Kdata z) | Kfield] :=
    MeasureTheory.condExp_congr_ae hprefixRelease
  have hceUp : μ[Kup | Kfield] =ᵐ[μ] Kup := by
    have hce := MeasureTheory.condExp_of_stronglyMeasurable hmle
      (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_stronglyMeasurable_in_inspectedField
        rate rewards C_star C_h control0 i t q s hs b)
      (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_integrable
        rate rewards C_star C_h control0 i t q s hs b)
    exact Filter.Eventually.of_forall fun z => congrFun hce z
  have hceData : μ[Kdata | Kfield] =ᵐ[μ] Kdata := by
    have hce := MeasureTheory.condExp_of_stronglyMeasurable hmle
      (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient_stronglyMeasurable_in_inspectedField
        rate rewards C_star C_h control0 i t q s hs b)
      (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient_integrable
        rate rewards C_star C_h control0 i t q s hs b)
    exact Filter.Eventually.of_forall fun z => congrFun hce z
  have hceRelease : μ[(fun z => Kup z + Kdata z) | Kfield] =ᵐ[μ]
      fun z => Kup z + Kdata z := by
    have hstrong : StronglyMeasurable[Kfield] (fun z => Kup z + Kdata z) :=
      (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_stronglyMeasurable_in_inspectedField
          rate rewards C_star C_h control0 i t q s hs b).add
        (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient_stronglyMeasurable_in_inspectedField
          rate rewards C_star C_h control0 i t q s hs b)
    have hint : Integrable (fun z => Kup z + Kdata z) μ :=
      (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_integrable
          rate rewards C_star C_h control0 i t q s hs b).add
        (ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient_integrable
          rate rewards C_star C_h control0 i t q s hs b)
    have hce := MeasureTheory.condExp_of_stronglyMeasurable hmle hstrong hint
    exact Filter.Eventually.of_forall fun z => congrFun hce z
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hTowerUp, hinnerUp, hceUp] with z ht hi hc
    exact ht.symm.trans (hi.trans hc)
  · filter_upwards [hTowerData, hinnerData, hceData] with z ht hi hc
    exact ht.symm.trans (hi.trans hc)
  · filter_upwards [hTowerRelease, hinnerRelease, hceRelease] with z ht hi hc
    exact ht.symm.trans (hi.trans hc)

/-- On almost every point of the same guarded event, the unguarded actual
flag conditional means equal the computed coefficients. The UP lower bound is
the inspected auxiliary readout; the DATA equality retains this follower's
assigned arm from the literal coefficient tuple. -/
theorem firstLiveInspected_actual_condExp_on_guarded_event :
    ∀ᵐ z ∂μ, z ∈ Gb →
      (μ[Xup | Kfield] z = Kup z) ∧
      (μ[Xdata | Kfield] z = Kdata z) ∧
      (μ[Xrelease | Kfield] z = Kup z + Kdata z) ∧
      (chiE z / (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤ μ[Xup | Kfield] z) ∧
      (chiAi z / (2 * (p.K : ℝ)) = μ[Xdata | Kfield] z) := by
  let hmle : Kfield ≤ (inferInstance : MeasurableSpace
      (BootstrapPrivateRoundStreams.SourceInput p)) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  have hguard : MeasurableSet[Kfield] Gb :=
    ReferenceFirstLiveInspectedGuardReadout.measurableSet_inspected_guard
      rate rewards C_star C_h control0 i t q s hs b
  have hflag := firstLiveInspected_guarded_flag_condExp
    rate rewards C_star C_h control0 i t q s hs b
  have hXup : Integrable Xup μ := by
    change Integrable (fun z => if
      ReferenceSourcePrefixHistoryFiltration.actualUp rate rewards C_star C_h i t z
        then (1 : ℝ) else 0) μ
    exact ReferenceSourcePhysicalFlagConditionalLaw.actualUp_observation_integrable
      rate rewards C_star C_h control0 i t
  have hXdata : Integrable Xdata μ := by
    change Integrable (fun z => if
      ReferenceSourcePrefixHistoryFiltration.actualData rate rewards C_star C_h i t z
        then (1 : ℝ) else 0) μ
    exact ReferenceSourcePhysicalFlagConditionalLaw.actualData_observation_integrable
      rate rewards C_star C_h control0 i t
  have hXrelease : Integrable Xrelease μ := by
    change Integrable (fun z => if
      ReferenceSourcePrefixHistoryFiltration.actualRelease rate rewards C_star C_h i t z
        then (1 : ℝ) else 0) μ
    exact ReferenceSourcePhysicalFlagConditionalLaw.actualRelease_observation_integrable
      rate rewards C_star C_h control0 i t
  have hindicatorUp : (fun z => Iguard z * Xup z) = Set.indicator Gb Xup := by
    funext z
    by_cases hz : z ∈ Gb <;>
      simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        hz]
  have hindicatorData : (fun z => Iguard z * Xdata z) = Set.indicator Gb Xdata := by
    funext z
    by_cases hz : z ∈ Gb <;>
      simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        hz]
  have hindicatorRelease : (fun z => Iguard z * Xrelease z) = Set.indicator Gb Xrelease := by
    funext z
    by_cases hz : z ∈ Gb <;>
      simp [ReferenceFirstLiveGuardedConditionalService.firstLiveGuardedEventIndicator,
        hz]
  have hindicatorUpAE : (fun z => Iguard z * Xup z) =ᵐ[μ] Set.indicator Gb Xup :=
    Filter.Eventually.of_forall fun z => congrFun hindicatorUp z
  have hindicatorDataAE : (fun z => Iguard z * Xdata z) =ᵐ[μ] Set.indicator Gb Xdata :=
    Filter.Eventually.of_forall fun z => congrFun hindicatorData z
  have hindicatorReleaseAE : (fun z => Iguard z * Xrelease z) =ᵐ[μ]
      Set.indicator Gb Xrelease :=
    Filter.Eventually.of_forall fun z => congrFun hindicatorRelease z
  have hlinkUp : μ[fun z => Iguard z * Xup z | Kfield] =ᵐ[μ]
      Set.indicator Gb (μ[Xup | Kfield]) :=
    (MeasureTheory.condExp_congr_ae hindicatorUpAE).trans
      (MeasureTheory.condExp_indicator hXup hguard)
  have hlinkData : μ[fun z => Iguard z * Xdata z | Kfield] =ᵐ[μ]
      Set.indicator Gb (μ[Xdata | Kfield]) :=
    (MeasureTheory.condExp_congr_ae hindicatorDataAE).trans
      (MeasureTheory.condExp_indicator hXdata hguard)
  have hlinkRelease : μ[fun z => Iguard z * Xrelease z | Kfield] =ᵐ[μ]
      Set.indicator Gb (μ[Xrelease | Kfield]) :=
    (MeasureTheory.condExp_congr_ae hindicatorReleaseAE).trans
      (MeasureTheory.condExp_indicator hXrelease hguard)
  have hmeanUp : ∀ᵐ z ∂μ, z ∈ Gb → μ[Xup | Kfield] z = Kup z := by
    filter_upwards [hflag.1, hlinkUp] with z hcoeff hlink
    intro hz
    calc
      μ[Xup | Kfield] z = Set.indicator Gb (μ[Xup | Kfield]) z := by simp [hz]
      _ = μ[fun w => Iguard w * Xup w | Kfield] z := hlink.symm
      _ = Kup z := hcoeff
  have hmeanData : ∀ᵐ z ∂μ, z ∈ Gb → μ[Xdata | Kfield] z = Kdata z := by
    filter_upwards [hflag.2.1, hlinkData] with z hcoeff hlink
    intro hz
    calc
      μ[Xdata | Kfield] z = Set.indicator Gb (μ[Xdata | Kfield]) z := by simp [hz]
      _ = μ[fun w => Iguard w * Xdata w | Kfield] z := hlink.symm
      _ = Kdata z := hcoeff
  have hmeanRelease : ∀ᵐ z ∂μ, z ∈ Gb →
      μ[Xrelease | Kfield] z = Kup z + Kdata z := by
    filter_upwards [hflag.2.2, hlinkRelease] with z hcoeff hlink
    intro hz
    calc
      μ[Xrelease | Kfield] z = Set.indicator Gb (μ[Xrelease | Kfield]) z := by simp [hz]
      _ = μ[fun w => Iguard w * Xrelease w | Kfield] z := hlink.symm
      _ = Kup z + Kdata z := hcoeff
  have hdataLiteral : ∀ (z : BootstrapPrivateRoundStreams.SourceInput p), z ∈ Gb →
      Kdata z = chiAi z / (2 * (p.K : ℝ)) := by
    intro z hz
    have hz' : z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
        rate rewards C_star C_h control0 i t q s hs b := hz
    simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedDataCoefficient,
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAssignedChi,
      ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
      dite_eq_left hz']
  have hlower :=
    ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedUpCoefficient_ge_guarded_auxiliary_lower_bound
      rate rewards C_star C_h control0 i t q s hs b
  filter_upwards [hmeanUp, hmeanData, hmeanRelease] with z hup hdata hrelease
  intro hz
  refine ⟨hup hz, hdata hz, hrelease hz, ?_, ?_⟩
  · calc
      chiE z / (12 * (p.m - 1 : ℝ) * (p.K : ℝ)) ≤ Kup z := hlower z
      _ = μ[Xup | Kfield] z := (hup hz).symm
  · calc
      chiAi z / (2 * (p.K : ℝ)) = Kdata z := (hdataLiteral z hz).symm
      _ = μ[Xdata | Kfield] z := (hdata hz).symm

/-- The auxiliary-weighted reward is the original sentinel `Q(e) * chi(e)`.
Its nonnegativity and domination by `chi(e)` follow from the coefficient
tuple bounds and the literal binary reward readout. -/
theorem firstLiveInspected_auxiliaryWeightedChi_bounds
    (z : BootstrapPrivateRoundStreams.SourceInput p) :
    0 ≤ omega z ∧ omega z ≤ chiE z := by
  rcases ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues_bounds
      rate rewards C_star C_h control0 i t q s hs b z with
    ⟨_, _, _, _, _, _, _, _, homega0, homega1⟩
  have hchiBinary : chiE z = 0 ∨ chiE z = 1 := by
    classical
    by_cases hz : z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
        rate rewards C_star C_h control0 i t q s hs b
    · simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryChi,
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
        dite_eq_left hz]
      unfold ReleaseRoundKernel.chi
      split_ifs <;> simp
    · simp [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryChi,
        ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
        ReferenceFirstLiveInspectedCoefficients.zeroValues, hz]
  refine ⟨homega0, ?_⟩
  rcases hchiBinary with hzero | hone
  · have homegaZero : omega z = 0 := by
      classical
      by_cases hz : z ∈ ReferenceFirstLiveInspectedCoefficients.guardedEvent
          rate rewards C_star C_h control0 i t q s hs b
      · simp only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryChi,
          ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi,
          ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
          dite_eq_left hz] at hzero ⊢
        rw [hzero]
        simp
      · simp [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi,
          ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedCoefficientValues,
          ReferenceFirstLiveInspectedCoefficients.zeroValues, hz]
    rw [homegaZero, hzero]
  · have hweightLeOne : omega z ≤ 1 := by
      simpa only [ReferenceFirstLiveInspectedCoefficients.firstLiveInspectedAuxiliaryWeightedChi]
        using homega1
    simpa [hone] using hweightLeOne

/-- Every measurable event of the inspected field tests the same three
guarded flag products against their computed coefficients. Integrability is
inherited from the bounded actual flag products and coefficients. -/
theorem firstLiveInspected_guarded_flag_setIntegrals
    (A : Set (BootstrapPrivateRoundStreams.SourceInput p))
    (hA : MeasurableSet[Kfield] A) :
    (∫ z in A, Iguard z * Xup z ∂μ = ∫ z in A, Kup z ∂μ) ∧
    (∫ z in A, Iguard z * Xdata z ∂μ = ∫ z in A, Kdata z ∂μ) ∧
    (∫ z in A, Iguard z * Xrelease z ∂μ =
      ∫ z in A, Kup z + Kdata z ∂μ) := by
  let hmle : Kfield ≤ (inferInstance : MeasurableSpace
      (BootstrapPrivateRoundStreams.SourceInput p)) :=
    ReferenceSourceOwnHistoryContainment.inspectedHistorySpace_le_original
      rate rewards C_star C_h control0 t.val (le_of_lt t.isLt)
  let : IsProbabilityMeasure (BootstrapPrivateRoundStreams.sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let : SigmaFinite ((BootstrapPrivateRoundStreams.sourceInputLaw p).trim hmle) := by
    infer_instance
  have hAambient : MeasurableSet A := hmle A hA
  have hproducts :=
    ReferenceFirstLiveGuardedConditionalService.firstLiveGuarded_flagProducts_integrable
      rate rewards C_star C_h control0 i t q s hs b
  have hce := firstLiveInspected_guarded_flag_condExp
    rate rewards C_star C_h control0 i t q s hs b
  have hceUpOnA : ∀ᵐ z ∂μ, z ∈ A →
      μ[fun w => Iguard w * Xup w | Kfield] z = Kup z := by
    filter_upwards [hce.1] with z hz
    intro _
    exact hz
  have hceDataOnA : ∀ᵐ z ∂μ, z ∈ A →
      μ[fun w => Iguard w * Xdata w | Kfield] z = Kdata z := by
    filter_upwards [hce.2.1] with z hz
    intro _
    exact hz
  have hceReleaseOnA : ∀ᵐ z ∂μ, z ∈ A →
      μ[fun w => Iguard w * Xrelease w | Kfield] z = Kup z + Kdata z := by
    filter_upwards [hce.2.2] with z hz
    intro _
    exact hz
  refine ⟨?_, ?_, ?_⟩
  · calc
      ∫ z in A, Iguard z * Xup z ∂μ =
          ∫ z in A, μ[fun w => Iguard w * Xup w | Kfield] z ∂μ :=
        (MeasureTheory.setIntegral_condExp hmle hproducts.1 hA).symm
      _ = ∫ z in A, Kup z ∂μ := MeasureTheory.setIntegral_congr_ae hAambient hceUpOnA
  · calc
      ∫ z in A, Iguard z * Xdata z ∂μ =
          ∫ z in A, μ[fun w => Iguard w * Xdata w | Kfield] z ∂μ :=
        (MeasureTheory.setIntegral_condExp hmle hproducts.2.1 hA).symm
      _ = ∫ z in A, Kdata z ∂μ := MeasureTheory.setIntegral_congr_ae hAambient hceDataOnA
  · calc
      ∫ z in A, Iguard z * Xrelease z ∂μ =
          ∫ z in A, μ[fun w => Iguard w * Xrelease w | Kfield] z ∂μ :=
        (MeasureTheory.setIntegral_condExp hmle hproducts.2.2 hA).symm
      _ = ∫ z in A, (Kup z + Kdata z) ∂μ :=
        MeasureTheory.setIntegral_congr_ae hAambient hceReleaseOnA

end Bandits.Support.ReferenceFirstLiveInspectedConditionalService

end
