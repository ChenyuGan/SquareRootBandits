/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveAllArmPrefixAdaptation
public import Bandits.Support.ReferenceFirstLiveAllArmSourceMoments

/-!
# All-arm conditional moments on the common first-live source prefix

Sources: sources/zip4/manuscript/04_slow_fast_learner.tex:140-168,256-264,
sources/zip4/manuscript/05_binary_transport.tex:354-396,
sources/zip4/manuscript/06_interruptions.tex:391-408,425-426,
sources/zip4/manuscript/07_public_setup.tex:127-164, and
sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64.

The first and square moments are conditioned on A's actual strict-prefix
field, on the same inherited unnormalized continuing first-live source measure.
Every measurable field set is factored through a Borel cell of the existing
remainder by the public source-prefix producer. The strict-past mask uses A's
first-n-cells overflow event, so the current update is retained even when it
is the first overflow. The carrier remains exactly the existing continuing
SourcePlus subtype: positive offset, no earlier cutoff, continuing PREPARE
with nonempty pending list, and enabled interior. These internal laws do not
identify the field with the manuscript history or establish an all-phase
recording law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveAllArmConditionalMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
abbrev SourceInput := ReferenceFirstLiveSourceSavedConditionalMoments.SourceInput

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q t s hs control0
local notation "Xplus" =>
  ReferenceFirstLiveRecordingReadoutMeasurability.XPlus rate rewards C_star C_h q t s hs control0
local notation "muPlus" =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t s hs control0
local notation "nuPlus" =>
  ReferenceFirstLiveRecordingSourceCylinder.branchRemainderMeasure rate rewards C_star C_h q t s hs control0
local notation "xof" =>
  ReferenceFirstLiveAllArmSourceMoments.xof rate rewards C_star C_h q t s hs control0
local notation "Fplus" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField rate rewards C_star C_h q t s hs control0
local notation "G" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet rate rewards C_star C_h q t s hs control0
local notation "remainderPrefix" =>
  ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix rate rewards C_star C_h q t s hs control0

local instance sourceInputMeasurableSpace (p : Parameters) : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace (CompletePublicTable.PublishedOutput p ×
    BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- Restrict the public saved-moment remainder prefix to A's existing
continuing remainder subtype. -/
def commonRemainderPrefix (x : Xplus) : SourceInput p :=
  ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix
    rate rewards C_star C_h q t s hs control0 x.val

theorem measurable_commonRemainderPrefix :
    Measurable (commonRemainderPrefix rate rewards C_star C_h q t s hs control0) :=
  (ReferenceFirstLiveSourceSavedConditionalMoments.measurable_remainderPrefix
    rate rewards C_star C_h q t s hs control0).comp measurable_subtype_coe

/-- At the actual branch projection, the restricted remainder prefix is the
literal current-control-erased prefix of the same original source point. -/
theorem commonRemainderPrefix_xof (z : Zplus) :
    commonRemainderPrefix rate rewards C_star C_h q t s hs control0 (xof z) =
      ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val := by
  change ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix
      rate rewards C_star C_h q t s hs control0
      (ReferenceFirstLiveRecordingSourceCylinder.sourceRetained
        rate rewards C_star C_h q t s hs control0 z.val) = _
  rw [ReferenceFirstLiveSourceSavedConditionalMoments.remainderPrefix_sourceRetained,
    ReferenceFirstLiveSourcePrefixBranchInvariance.prefixZ_val,
    ← ReferenceSourcePhysicalFlagConditionalLaw.c_t_eq_sourcePrefix]

/-- Every Fplus-measurable source set has an actual Borel remainder cell.
The cell is built by pulling back a source-input Borel set through the
restricted public remainder prefix; no factorization is assumed. -/
theorem sourcePlusPrefixField_cell (S : Set Zplus) (hS : MeasurableSet[Fplus] S) :
    ∃ B : Set Xplus, MeasurableSet B ∧ {z : Zplus | xof z ∈ B} = S := by
  obtain ⟨V, hV, hVS⟩ := MeasurableSpace.measurableSet_comap.mp hS
  let B : Set Xplus := (commonRemainderPrefix rate rewards C_star C_h q t s hs control0) ⁻¹' V
  refine ⟨B, hV.preimage
    (measurable_commonRemainderPrefix rate rewards C_star C_h q t s hs control0), ?_⟩
  calc
    {z : Zplus | xof z ∈ B} =
        (fun z : Zplus =>
          ReferenceSourceCurrentControlFreshness.c_t p control0 t z.val.val) ⁻¹' V := by
      ext z
      change commonRemainderPrefix rate rewards C_star C_h q t s hs control0 (xof z) ∈ V ↔ _
      rw [commonRemainderPrefix_xof]
      rfl
    _ = S := hVS

/-- A's literal first coefficient equals M's actual marker-rate times the
actual quantized arrival value at the same branch remainder. -/
theorem firstCoefficientPlus_eq_xi_mul_v (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j z =
      ReferenceFirstLiveAllArmSourceMoments.xi rate rewards C_star C_h q t s hs control0
          (xof z) j *
        ReferenceFirstLiveAllArmSourceMoments.v rate rewards C_star C_h q t s hs control0
          (xof z) j := by
  rfl

/-- A's literal square coefficient equals xi times v squared; it does not
square the rate or the first conditional mean. -/
theorem secondCoefficientPlus_eq_xi_mul_v_sq (j : Fin p.K) (z : Zplus) :
    ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j z =
      ReferenceFirstLiveAllArmSourceMoments.xi rate rewards C_star C_h q t s hs control0
          (xof z) j *
        (ReferenceFirstLiveAllArmSourceMoments.v rate rewards C_star C_h q t s hs control0
          (xof z) j) ^ 2 := by
  rfl

/-- Transport an integrand over any Borel remainder cell by M's actual
branch-source map. -/
theorem branchSourceMeasure_cell_integral (g : Xplus → ℝ) (hg : Measurable g)
    (B : Set Xplus) (hB : MeasurableSet B) :
    (∫ z in {z : Zplus | xof z ∈ B}, g (xof z) ∂muPlus) =
      ∫ x in B, g x ∂nuPlus := by
  let sourceCell : Set Zplus := {z | xof z ∈ B}
  have hsourceCell : MeasurableSet sourceCell :=
    hB.preimage (ReferenceFirstLiveAllArmSourceMoments.xof_measurable
      rate rewards C_star C_h q t s hs control0)
  have hindicator :
      (fun z : Zplus => sourceCell.indicator (fun z => g (xof z)) z) =
        (B.indicator g) ∘ xof := by
    funext z
    exact Set.indicator_comp_right xof (s := B) (g := g) (x := z)
  calc
    _ = ∫ z, sourceCell.indicator (fun z => g (xof z)) z ∂muPlus :=
      (integral_indicator hsourceCell).symm
    _ = ∫ z, (B.indicator g) (xof z) ∂muPlus := by
      rw [hindicator]
      rfl
    _ = ∫ x, B.indicator g x ∂
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate rewards C_star C_h q t s hs control0).map xof :=
      (integral_map
        (ReferenceFirstLiveAllArmSourceMoments.xof_measurable
          rate rewards C_star C_h q t s hs control0).aemeasurable
        (hg.indicator hB).aestronglyMeasurable).symm
    _ = ∫ x, B.indicator g x ∂nuPlus := by
      rw [ReferenceFirstLiveAllArmSourceMoments.branchSourceMeasure_map_xof
        rate rewards C_star C_h q t s hs control0]
    _ = ∫ x in B, g x ∂nuPlus := integral_indicator hB

/-- The actual raw first-arrival integral agrees on every measurable common
prefix cell with A's first coefficient under the same original source measure. -/
theorem source_firstMoment_prefixField_integral (S : Set Zplus)
    (hS : MeasurableSet[Fplus] S) (j : Fin p.K) :
    (∫ z in S,
      ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j
        ∂muPlus) =
      ∫ z in S,
        ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
  obtain ⟨B, hB, hSB⟩ := sourcePlusPrefixField_cell rate rewards C_star C_h q t s hs control0 S hS
  rw [← hSB]
  calc
    _ = ∫ x in B,
        ReferenceFirstLiveAllArmSourceMoments.xi rate rewards C_star C_h q t s hs control0 x j *
          ReferenceFirstLiveAllArmSourceMoments.v rate rewards C_star C_h q t s hs control0 x j
          ∂nuPlus :=
      ReferenceFirstLiveAllArmSourceMoments.source_firstMoment_cell_integral
        rate rewards C_star C_h q t s hs control0 B hB j
    _ = ∫ z in {z : Zplus | xof z ∈ B},
        ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
      calc
        _ = ∫ z in {z : Zplus | xof z ∈ B},
            (ReferenceFirstLiveAllArmSourceMoments.xi
              rate rewards C_star C_h q t s hs control0 (xof z) j) *
              ReferenceFirstLiveAllArmSourceMoments.v
                rate rewards C_star C_h q t s hs control0 (xof z) j ∂muPlus :=
          (branchSourceMeasure_cell_integral rate rewards C_star C_h q t s hs control0
            (fun x => ReferenceFirstLiveAllArmSourceMoments.xi
              rate rewards C_star C_h q t s hs control0 x j *
              ReferenceFirstLiveAllArmSourceMoments.v
                rate rewards C_star C_h q t s hs control0 x j)
            (ReferenceFirstLiveAllArmSourceMoments.measurable_xi_mul_v
              rate rewards C_star C_h q t s hs control0 j) B hB).symm
        _ = ∫ z in {z : Zplus | xof z ∈ B},
            ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
              rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
          apply setIntegral_congr_fun
            (hB.preimage (ReferenceFirstLiveAllArmSourceMoments.xof_measurable
              rate rewards C_star C_h q t s hs control0))
          intro z _
          rw [firstCoefficientPlus_eq_xi_mul_v]

/-- The actual square-arrival integral agrees on every measurable common
prefix cell with A's square coefficient on the same source measure. -/
theorem source_secondMoment_prefixField_integral (S : Set Zplus)
    (hS : MeasurableSet[Fplus] S) (j : Fin p.K) :
    (∫ z in S,
      (ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2
        ∂muPlus) =
      ∫ z in S,
        ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
  obtain ⟨B, hB, hSB⟩ := sourcePlusPrefixField_cell rate rewards C_star C_h q t s hs control0 S hS
  rw [← hSB]
  calc
    _ = ∫ x in B,
        ReferenceFirstLiveAllArmSourceMoments.xi rate rewards C_star C_h q t s hs control0 x j *
          (ReferenceFirstLiveAllArmSourceMoments.v
            rate rewards C_star C_h q t s hs control0 x j) ^ 2 ∂nuPlus :=
      ReferenceFirstLiveAllArmSourceMoments.source_secondMoment_cell_integral
        rate rewards C_star C_h q t s hs control0 B hB j
    _ = ∫ z in {z : Zplus | xof z ∈ B},
        ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
      calc
        _ = ∫ z in {z : Zplus | xof z ∈ B},
            (ReferenceFirstLiveAllArmSourceMoments.xi
              rate rewards C_star C_h q t s hs control0 (xof z) j) *
              (ReferenceFirstLiveAllArmSourceMoments.v
                rate rewards C_star C_h q t s hs control0 (xof z) j) ^ 2 ∂muPlus :=
          (branchSourceMeasure_cell_integral rate rewards C_star C_h q t s hs control0
            (fun x => ReferenceFirstLiveAllArmSourceMoments.xi
              rate rewards C_star C_h q t s hs control0 x j *
              (ReferenceFirstLiveAllArmSourceMoments.v
                rate rewards C_star C_h q t s hs control0 x j) ^ 2)
            (ReferenceFirstLiveAllArmSourceMoments.measurable_xi_mul_v_sq
              rate rewards C_star C_h q t s hs control0 j) B hB).symm
        _ = ∫ z in {z : Zplus | xof z ∈ B},
            ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
              rate rewards C_star C_h q t s hs control0 j z ∂muPlus := by
          apply setIntegral_congr_fun
            (hB.preimage (ReferenceFirstLiveAllArmSourceMoments.xof_measurable
              rate rewards C_star C_h q t s hs control0))
          intro z _
          rw [secondCoefficientPlus_eq_xi_mul_v_sq]

/-- A's raw first candidate is measurable in the exact common prefix field
and integrable on the inherited finite branch measure. -/
theorem firstCoefficientPlus_integrable (j : Fin p.K) :
    Integrable
      (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j) muPlus := by
  have hm := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have hmeas : Measurable
      (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j) :=
    (ReferenceFirstLiveAllArmPrefixAdaptation.measurable_firstCoefficientPlus
      rate rewards C_star C_h q t s hs control0 j).mono hm le_rfl
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro z
  have hb := ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
    rate rewards C_star C_h q t s hs control0 j z
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2.2.1.trans hb.2.2.2

/-- A's raw square candidate is measurable in the exact common prefix field
and integrable on the same finite branch measure, including when its mass is 0. -/
theorem secondCoefficientPlus_integrable (j : Fin p.K) :
    Integrable
      (ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j) muPlus := by
  have hm := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have hmeas : Measurable
      (ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j) :=
    (ReferenceFirstLiveAllArmPrefixAdaptation.measurable_secondCoefficientPlus
      rate rewards C_star C_h q t s hs control0 j).mono hm le_rfl
  have hbeta : 0 < ReferenceFirstLiveSourceSavedMoments.beta rate :=
    CanonicalRecordingRates.beta_pos p rate.eta.property
  have hB : 0 ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate :=
    (div_pos (by norm_num) hbeta).le
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (1 / ReferenceFirstLiveSourceSavedMoments.beta rate)
  apply Filter.Eventually.of_forall
  intro z
  have hb := ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus_bounds
    rate rewards C_star C_h q t s hs control0 j z
  rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2.1.trans (hb.2.2.1.trans hb.2.2.2)

/-- Raw first conditional moment of the actual all-arm arrival on A's exact
common source prefix field. -/
theorem condExp_a_firstMoment (j : Fin p.K) :
    muPlus[(fun z : Zplus =>
      ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j)
      | Fplus] =ᵐ[muPlus]
      (fun z => ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j z) := by
  have hm := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have : IsFiniteMeasure
      ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0).trim hm) :=
    ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_trim_finite
      rate rewards C_star C_h q t s hs control0
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    (ReferenceFirstLiveAllArmSourceMoments.integrable_a
      rate rewards C_star C_h q t s hs control0 j)
  · intro S _ _
    exact (firstCoefficientPlus_integrable rate rewards C_star C_h q t s hs control0 j).integrableOn
  · intro S hS _
    exact (source_firstMoment_prefixField_integral
      rate rewards C_star C_h q t s hs control0 S hS j).symm
  · exact (ReferenceFirstLiveAllArmPrefixAdaptation.measurable_firstCoefficientPlus
      rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable

/-- Raw square conditional moment of the same actual arrival. -/
theorem condExp_a_secondMoment (j : Fin p.K) :
    muPlus[(fun z : Zplus =>
      (ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2)
      | Fplus] =ᵐ[muPlus]
      (fun z => ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
        rate rewards C_star C_h q t s hs control0 j z) := by
  have hm := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have : IsFiniteMeasure
      ((ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
        rate rewards C_star C_h q t s hs control0).trim hm) :=
    ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_trim_finite
      rate rewards C_star C_h q t s hs control0
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hm
    (ReferenceFirstLiveAllArmSourceMoments.integrable_a_sq
      rate rewards C_star C_h q t s hs control0 j)
  · intro S _ _
    exact (secondCoefficientPlus_integrable rate rewards C_star C_h q t s hs control0 j).integrableOn
  · intro S hS _
    exact (source_secondMoment_prefixField_integral
      rate rewards C_star C_h q t s hs control0 S hS j).symm
  · exact (ReferenceFirstLiveAllArmPrefixAdaptation.measurable_secondCoefficientPlus
      rate rewards C_star C_h q t s hs control0 j).aestronglyMeasurable

/-- The strict-past retained arrival on the same source carrier. Its mask is
A's literal event over the first t.val - s cells of the existing n + 1
cell list. -/
def retainedA (j : Fin p.K) : Zplus → ℝ :=
  Set.indicator G (fun z =>
    ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j)

/-- Literal if/zero form of the strict-past retained arrival. -/
theorem retainedA_eq_if (j : Fin p.K) (z : Zplus) :
    retainedA rate rewards C_star C_h q t s hs control0 j z =
      if z ∈ G then
        ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j
      else 0 := by
  by_cases hz : z ∈ G <;> simp [retainedA, hz]

/-- Squaring the retained arrival is exactly the indicator of the square. -/
theorem retainedA_sq_eq_indicator_a_sq (j : Fin p.K) (z : Zplus) :
    (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2 =
      Set.indicator G (fun z : Zplus =>
        (ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2) z := by
  by_cases hz : z ∈ G <;> simp [retainedA, hz]

theorem measurable_retainedA (j : Fin p.K) :
    Measurable (retainedA rate rewards C_star C_h q t s hs control0 j) :=
  (ReferenceFirstLiveAllArmSourceMoments.measurable_a
    rate rewards C_star C_h q t s hs control0 j).indicator
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
        rate rewards C_star C_h q t s hs control0)

theorem measurable_retainedA_sq (j : Fin p.K) :
    Measurable (fun z : Zplus =>
      (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) :=
  (measurable_retainedA rate rewards C_star C_h q t s hs control0 j).pow_const 2

theorem integrable_retainedA (j : Fin p.K) :
    Integrable (retainedA rate rewards C_star C_h q t s hs control0 j) muPlus :=
  (ReferenceFirstLiveAllArmSourceMoments.integrable_a
    rate rewards C_star C_h q t s hs control0 j).indicator
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
        rate rewards C_star C_h q t s hs control0)

theorem integrable_retainedA_sq (j : Fin p.K) :
    Integrable (fun z : Zplus =>
      (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) muPlus := by
  have hpoint : (fun z : Zplus =>
      (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) =
      Set.indicator G (fun z : Zplus =>
        (ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2) := by
    funext z
    exact retainedA_sq_eq_indicator_a_sq rate rewards C_star C_h q t s hs control0 j z
  rw [hpoint]
  exact (ReferenceFirstLiveAllArmSourceMoments.integrable_a_sq
    rate rewards C_star C_h q t s hs control0 j).indicator
      (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
        rate rewards C_star C_h q t s hs control0)

/-- The retained actual arrival remains in [0, 1 / beta] on every point,
including the zero branch off the strict-past event. -/
theorem retainedA_pointwise_bounds (j : Fin p.K) (z : Zplus) :
    0 ≤ retainedA rate rewards C_star C_h q t s hs control0 j z ∧
      retainedA rate rewards C_star C_h q t s hs control0 j z ≤
        1 / CanonicalRecordingRates.beta p rate.eta.val := by
  by_cases hz : z ∈ G
  · simpa [retainedA, hz] using
      (ReferenceFirstLiveAllArmSourceMoments.a_bounds
        rate rewards C_star C_h q t s hs control0 z j)
  · have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hbound : 0 ≤ 1 / CanonicalRecordingRates.beta p rate.eta.val :=
      (div_pos (by norm_num) hbeta).le
    simp only [retainedA, Set.indicator_of_notMem hz]
    exact ⟨le_rfl, hbound⟩

/-- Strict-past first conditional moment, obtained from the raw same-source
law by Mathlib's conditional-expectation indicator theorem. -/
theorem retainedA_condExp_firstMoment (j : Fin p.K) :
    muPlus[retainedA rate rewards C_star C_h q t s hs control0 j | Fplus] =ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z) := by
  change muPlus[Set.indicator G (fun z : Zplus =>
      ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j)
      | Fplus] =ᵐ[muPlus] _
  have hmask := MeasureTheory.condExp_indicator
    (ReferenceFirstLiveAllArmSourceMoments.integrable_a
      rate rewards C_star C_h q t s hs control0 j)
    (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet
      rate rewards C_star C_h q t s hs control0)
  have hbase := condExp_a_firstMoment rate rewards C_star C_h q t s hs control0 j
  filter_upwards [hmask, hbase] with z hzMask hzBase
  rw [hzMask]
  by_cases hkeep : z ∈ G
  · simpa [hkeep] using hzBase
  · simp [hkeep]

/-- Strict-past square conditional moment; the retained square is first
rewritten as the indicator of the actual square before applying
condExp_indicator. -/
theorem retainedA_condExp_secondMoment (j : Fin p.K) :
    muPlus[(fun z : Zplus =>
      (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] =ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus
          rate rewards C_star C_h q t s hs control0 j z) := by
  have hpoint : (fun z : Zplus =>
      (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) =
      Set.indicator G (fun z : Zplus =>
        (ReferenceFirstLiveAllArmSourceMoments.a rate rewards C_star C_h q t s hs control0 z j) ^ 2) := by
    funext z
    exact retainedA_sq_eq_indicator_a_sq rate rewards C_star C_h q t s hs control0 j z
  rw [hpoint]
  have hmask := MeasureTheory.condExp_indicator
    (ReferenceFirstLiveAllArmSourceMoments.integrable_a_sq
      rate rewards C_star C_h q t s hs control0 j)
    (ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet
      rate rewards C_star C_h q t s hs control0)
  have hbase := condExp_a_secondMoment rate rewards C_star C_h q t s hs control0 j
  filter_upwards [hmask, hbase] with z hzMask hzBase
  rw [hzMask]
  by_cases hkeep : z ∈ G
  · simpa [hkeep] using hzBase
  · simp [hkeep]

/-- The retained first conditional moment is nonnegative almost everywhere. -/
theorem retainedA_condExp_first_nonneg (j : Fin p.K) :
    0 ≤ᵐ[muPlus]
      muPlus[retainedA rate rewards C_star C_h q t s hs control0 j | Fplus] := by
  have hce := retainedA_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j
  filter_upwards [hce] with z hz
  rw [hz]
  by_cases hkeep : z ∈ G
  · simpa [hkeep] using
      (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
        rate rewards C_star C_h q t s hs control0 j z).1
  · simp [hkeep]

/-- The retained first conditional moment has the literal rounded-reward
lower bound, its reward upper bound, and the unit ceiling. -/
theorem retainedA_condExp_first_bounds (j : Fin p.K) :
    Set.indicator G (fun z : Zplus =>
      ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus rewards t j -
        ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
          rate rewards C_star C_h q t s hs control0 j z /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ))) ≤ᵐ[muPlus]
        muPlus[retainedA rate rewards C_star C_h q t s hs control0 j | Fplus] ∧
    muPlus[retainedA rate rewards C_star C_h q t s hs control0 j | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun _ : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus rewards t j) ∧
    Set.indicator G (fun _ : Zplus =>
      ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus rewards t j) ≤ᵐ[muPlus]
        (fun _ : Zplus => 1) := by
  have hce := retainedA_condExp_firstMoment rate rewards C_star C_h q t s hs control0 j
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.1
    · simp [hkeep]
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.2.1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.roundedRewardPlus_bounds rewards t j).2
    · simp [hkeep]

/-- The retained square conditional moment is nonnegative and is bounded by
the masked rho-squared-over-xi, then by masked 1 / xi, then by 1 / beta. -/
theorem retainedA_condExp_second_bounds (j : Fin p.K) :
    0 ≤ᵐ[muPlus]
      muPlus[(fun z : Zplus =>
        (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] ∧
    muPlus[(fun z : Zplus =>
      (retainedA rate rewards C_star C_h q t s hs control0 j z) ^ 2) | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        ReferenceFirstLiveAllArmPrefixAdaptation.rhoSquaredDivRatePlus
          rate rewards C_star C_h q t s hs control0 j z) ∧
    Set.indicator G (fun z : Zplus =>
      ReferenceFirstLiveAllArmPrefixAdaptation.rhoSquaredDivRatePlus
        rate rewards C_star C_h q t s hs control0 j z) ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        1 / ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
          rate rewards C_star C_h q t s hs control0 j z) ∧
    Set.indicator G (fun z : Zplus =>
      1 / ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
        rate rewards C_star C_h q t s hs control0 j z) ≤ᵐ[muPlus]
      (fun _ : Zplus => 1 / ReferenceFirstLiveSourceSavedMoments.beta rate) := by
  have hce := retainedA_condExp_secondMoment rate rewards C_star C_h q t s hs control0 j
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).1
    · simp [hkeep]
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.2.1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ G
    · simpa [hkeep] using
        (ReferenceFirstLiveAllArmPrefixAdaptation.secondCoefficientPlus_bounds
          rate rewards C_star C_h q t s hs control0 j z).2.2.2
    · have hbeta : 0 ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate :=
        (div_pos (by norm_num)
          (CanonicalRecordingRates.beta_pos p rate.eta.property)).le
      simp only [Set.indicator_of_notMem hkeep]
      exact hbeta

end Bandits.Support.ReferenceFirstLiveAllArmConditionalMoments

end
