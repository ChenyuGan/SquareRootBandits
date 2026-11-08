/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveNumericalPrefixAdaptation
public import Bandits.Support.ReferenceFirstLiveSourceSavedConditionalMoments

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Strict-past retained saved-emission conditional moments

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:140-188,256-264`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`,
`sources/zip4/manuscript/07_public_setup.tex:127-164`, and
`sources/zip4/manuscript/appendix_a_local_protocol.tex:28-64`.

This module masks the actual current saved emission on the existing continuing,
actually unoccupied follower source subtype. Its one event is the literal
overflow-false result of the first `t.val - s` actual numerical cells. The
current round's update remains in the saved emission, including when that
update is the first overflow. All measures stay inherited and unnormalized;
these are internal conditional-moment results, not manuscript history or
regret closure claims.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.ContinuousLearningRows
open Bandits.Support.ReferenceActivePhysicalStep
open Bandits.Support.ReferenceFirstWindowNumericalStream
open Bandits.Support.RecordedQueueRun
open Bandits.Support.ReferenceFirstLiveNumericalPrefixTemporal
open Bandits.Support.ReferenceFirstLiveSourceSavedMoments
open Bandits.Support.ReferenceFirstLiveSourcePrefixBranchInvariance
open scoped Classical

namespace Bandits.Support.ReferenceFirstLiveRetainedConditionalMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (M p)) (t : Fin p.T) (s : ℕ)
  (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "n" => t.val - s

variable (i : Fin (p.m - 1))

local notation "Zi" => ReferenceFirstLiveSourceSavedMoments.SourceFollower
  rate rewards C_star C_h q t s hs control0 i
local notation "Fi" => ReferenceFirstLiveSourcePrefixBranchInvariance.sourceFollowerPrefixField
  rate rewards C_star C_h q t s hs control0 i
local notation "μZi" => ReferenceFirstLiveSourceSavedMoments.followerSourceMeasure
  rate rewards C_star C_h q t s hs control0 i
local notation "xof" => ReferenceFirstLiveSourcePrefixBranchInvariance.sourceFollowerRetained
  rate rewards C_star C_h q t s hs control0 i
local notation "xiZ" => ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ
  rate rewards C_star C_h q t s hs control0 i
local notation "rhoZ" => ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ
  rate rewards C_star C_h q t s hs control0 i
local notation "vZ" => ReferenceFirstLiveSourcePrefixBranchInvariance.vZ
  rate rewards C_star C_h q t s hs control0 i
local notation "saved" => ReferenceFirstLiveSourceSavedMoments.sourceSaved
  rate rewards C_star C_h q t s hs control0 i

/-- The strict-past overflow-false event on the existing source follower.
Its run is over exactly the first `t.val - s` cells, with the source-stratum
span proof used by the numerical-prefix adaptation producer. -/
def pastRetainedFollowerSet : Set Zi :=
  {z : Zi |
    (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
      ((ReferenceFirstWindowNumericalStream.actualLiveSourceCells rate z.val.val rewards C_star C_h
        (ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
          rate rewards C_star C_h q t s hs z.val).2.1
        (n + 1)
        (by
          have hz := ReferenceFirstLiveNumericalPrefixTemporal.sourceStratum_facts
            rate rewards C_star C_h q t s hs z.val
          rw [hz.2.2]
          omega)).take n)).overflow = false}

local notation "pastKeep" => pastRetainedFollowerSet
  rate rewards C_star C_h q t s hs control0 i
local notation "retainedSaved" => Set.indicator pastKeep saved

/-- The event is measurable on the exact inherited strict-prefix field. -/
theorem measurableSet_pastRetainedFollowerSet_follower :
    MeasurableSet[Fi] pastKeep := by
  exact ReferenceFirstLiveNumericalPrefixAdaptation.measurableSet_numericalCountRunOverflowFalse_follower
      rate rewards C_star C_h q t s hs control0 i

/-- The same event is ambient measurable by C's actual field inclusion. -/
theorem measurableSet_pastRetainedFollowerSet :
    MeasurableSet pastKeep := by
  have hle := ReferenceFirstLiveSourceSavedConditionalMoments.sourceFollowerPrefixField_le
    rate rewards C_star C_h q t s hs control0 i
  exact hle _ (measurableSet_pastRetainedFollowerSet_follower
    rate rewards C_star C_h q t s hs control0 i)

/-- The actual saved emission masked by the literal strict-past event is
ambient measurable. -/
theorem measurable_retainedSaved : Measurable retainedSaved :=
  (ReferenceFirstLiveSourceSavedMoments.measurable_sourceSaved
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet
        rate rewards C_star C_h q t s hs control0 i)

/-- The square of the masked actual saved emission is ambient measurable. -/
theorem measurable_retainedSaved_sq :
    Measurable (fun z : Zi => retainedSaved z ^ 2) := by
  have h := measurable_retainedSaved rate rewards C_star C_h q t s hs control0 i
  exact h.pow_const 2

/-- The masked actual saved emission is integrable on M's same unnormalized
source measure. -/
theorem integrable_retainedSaved : Integrable retainedSaved μZi :=
  (ReferenceFirstLiveSourceSavedMoments.followerSource_saved_integrable
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet
        rate rewards C_star C_h q t s hs control0 i)

/-- The square of the masked actual saved emission is integrable on the same
unnormalized source measure. -/
theorem integrable_retainedSaved_sq :
    Integrable (fun z : Zi => retainedSaved z ^ 2) μZi := by
  have hpoint : (fun z : Zi => retainedSaved z ^ 2) =
      Set.indicator pastKeep (fun z : Zi => (saved z) ^ 2) := by
    funext z
    by_cases hz : z ∈ pastKeep <;> simp [hz]
  rw [hpoint]
  exact (ReferenceFirstLiveSourceSavedMoments.followerSource_saved_sq_integrable
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet
        rate rewards C_star C_h q t s hs control0 i)

/-- The first masked candidate is measurable on exactly Fi. -/
theorem measurable_first_masked_candidate :
    Measurable[Fi] (Set.indicator pastKeep (fun z : Zi => xiZ z * vZ z)) :=
  (ReferenceFirstLiveSourceSavedConditionalMoments.first_mean_adapted
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet_follower
        rate rewards C_star C_h q t s hs control0 i)

/-- The square-moment masked candidate is measurable on exactly Fi. -/
theorem measurable_second_masked_candidate :
    Measurable[Fi]
      (Set.indicator pastKeep (fun z : Zi => xiZ z * (vZ z) ^ 2)) :=
  (ReferenceFirstLiveSourceSavedConditionalMoments.second_mean_adapted
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet_follower
        rate rewards C_star C_h q t s hs control0 i)

/-- The first masked candidate is integrable on the inherited source measure. -/
theorem integrable_first_masked_candidate :
    Integrable (Set.indicator pastKeep (fun z : Zi => xiZ z * vZ z)) μZi :=
  (ReferenceFirstLiveSourceSavedConditionalMoments.first_mean_integrable
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet
        rate rewards C_star C_h q t s hs control0 i)

/-- The square-moment masked candidate is integrable on the same measure. -/
theorem integrable_second_masked_candidate :
    Integrable (Set.indicator pastKeep (fun z : Zi => xiZ z * (vZ z) ^ 2)) μZi :=
  (ReferenceFirstLiveSourceSavedConditionalMoments.second_mean_integrable
    rate rewards C_star C_h q t s hs control0 i).indicator
      (measurableSet_pastRetainedFollowerSet
        rate rewards C_star C_h q t s hs control0 i)

/-- Pointwise, squaring the indicator-masked emission is the indicator of the
square, including on the complement of the retained event. -/
theorem retainedSaved_sq_eq_indicator_saved_sq (z : Zi) :
    retainedSaved z ^ 2 = Set.indicator pastKeep (fun z : Zi => (saved z) ^ 2) z := by
  by_cases hz : z ∈ pastKeep <;> simp [hz]

/-- The retained readout has the literal strict-past event's if/zero form. -/
theorem retainedSaved_eq_if (z : Zi) :
    retainedSaved z = if z ∈ pastKeep then saved z else 0 := by
  by_cases hz : z ∈ pastKeep <;> simp [hz]

/-- The masked emission is still the real coordinate of M's original current
`logEmission`, with its actual assigned arm and exact `eta * D` scale. -/
theorem retainedSaved_eq_masked_original_logEmission (z : Zi) :
    retainedSaved z =
      if z ∈ pastKeep then
        (ReferenceContinuingRecordingPhysicalReward.actualCurrentSavedContribution
          (ReferenceFirstLiveRecordingSourceCylinder.originalCurrentRecord
            rate rewards C_star C_h q t s hs control0 z.val)
          (ReferenceFirstLiveSourceSavedMoments.selectedBaselinePayload
            rate rewards C_star C_h q t s hs control0 i (xof z)) i : ℝ) /
          (rate.eta.val * (D p : ℝ))
      else 0 := by
  rw [retainedSaved_eq_if rate rewards C_star C_h q t s hs control0 i z]
  by_cases hz : z ∈ pastKeep
  · simp [hz]
    rw [ReferenceFirstLiveSourceSavedMoments.sourceSaved_eq_originalCurrentRecord
      rate rewards C_star C_h q t s hs control0 i z]
    rfl
  · simp [hz]

private theorem source_saved_pointwise_bounds (z : Zi) :
    0 ≤ saved z ∧ saved z ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate := by
  rcases ReferenceFirstLiveSourceSavedMoments.actual_follower_saved_moments
      rate rewards C_star C_h q t s hs control0 i (xof z) with
    ⟨_, _, _, _, _, _, _, _, _, _, hbounds⟩
  change 0 ≤ ReferenceFirstLiveSourceSavedMoments.f
      rate rewards C_star C_h q t s hs control0 i (xof z)
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val) ∧
    ReferenceFirstLiveSourceSavedMoments.f
      rate rewards C_star C_h q t s hs control0 i (xof z)
        (ReferenceFirstLiveRecordingSourceCylinder.originalControl
          rate rewards C_star C_h q t s hs z.val) ≤
      1 / ReferenceFirstLiveSourceSavedMoments.beta rate
  exact hbounds (ReferenceFirstLiveRecordingSourceCylinder.originalControl
    rate rewards C_star C_h q t s hs z.val)

/-- The retained actual emission is pointwise nonnegative and bounded by the
rate-derived `1 / beta` envelope. -/
theorem retainedSaved_pointwise_bounds (z : Zi) :
    0 ≤ retainedSaved z ∧
      retainedSaved z ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate := by
  by_cases hz : z ∈ pastKeep
  · simpa [hz] using
      source_saved_pointwise_bounds rate rewards C_star C_h q t s hs control0 i z
  · have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
    have hinv : 0 ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate := by
      exact (div_pos (by norm_num) hbeta).le
    simp only [Set.indicator_of_notMem hz]
    exact ⟨le_rfl, hinv⟩

private theorem source_first_candidate_quantization_bounds (z : Zi) :
    rhoZ z - xiZ z / (rate.eta.val * (D p : ℝ)) ≤ xiZ z * vZ z ∧
      xiZ z * vZ z ≤ rhoZ z ∧ rhoZ z ≤ 1 := by
  rcases ReferenceFirstLiveSourceSavedMoments.actual_follower_saved_moments
      rate rewards C_star C_h q t s hs control0 i (xof z) with
    ⟨⟨_, _, _, _, hrhoOne⟩, _, _, _, hfirst, _, hlower, hupper, _, _, _⟩
  have hfirst' :
      (∫ u, ReferenceFirstLiveSourceSavedMoments.f
        rate rewards C_star C_h q t s hs control0 i (xof z) u ∂
        ContinuousLearningRows.timeControlLaw p) = xiZ z * vZ z := by
    simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ,
      ReferenceFirstLiveSourcePrefixBranchInvariance.vZ] using hfirst
  refine ⟨?_, ?_, ?_⟩
  · calc
      rhoZ z - xiZ z / (rate.eta.val * (D p : ℝ)) ≤
          ∫ u, ReferenceFirstLiveSourceSavedMoments.f
            rate rewards C_star C_h q t s hs control0 i (xof z) u ∂
            ContinuousLearningRows.timeControlLaw p := by
              simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ,
                ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ] using hlower
      _ = xiZ z * vZ z := hfirst'
  · calc
      xiZ z * vZ z =
          ∫ u, ReferenceFirstLiveSourceSavedMoments.f
            rate rewards C_star C_h q t s hs control0 i (xof z) u ∂
            ContinuousLearningRows.timeControlLaw p := hfirst'.symm
      _ ≤ rhoZ z := by
          simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ] using hupper
  · simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ] using hrhoOne

private theorem source_second_candidate_quantization_bounds (z : Zi) :
    xiZ z * (vZ z) ^ 2 ≤ rhoZ z ^ 2 / xiZ z ∧
      xiZ z * (vZ z) ^ 2 ≤ 1 / xiZ z ∧
      rhoZ z ^ 2 / xiZ z ≤ 1 / xiZ z ∧
      1 / xiZ z ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate ∧
      0 < xiZ z ∧ 0 < ReferenceFirstLiveSourceSavedMoments.beta rate := by
  rcases ReferenceFirstLiveSourceSavedMoments.actual_follower_saved_moments
      rate rewards C_star C_h q t s hs control0 i (xof z) with
    ⟨⟨hxi, hbeta, hbetaXi, hrhoZero, hrhoOne⟩, _, _, _, _, hsecond, _, _, hsqRho, hsqOne, _⟩
  have hsecond' :
      (∫ u, (ReferenceFirstLiveSourceSavedMoments.f
        rate rewards C_star C_h q t s hs control0 i (xof z) u) ^ 2 ∂
        ContinuousLearningRows.timeControlLaw p) = xiZ z * (vZ z) ^ 2 := by
    simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ,
      ReferenceFirstLiveSourcePrefixBranchInvariance.vZ] using hsecond
  have hrhoSquare : rhoZ z ^ 2 ≤ 1 := by
    have hzero : 0 ≤ rhoZ z := by
      simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ] using hrhoZero
    have hone : rhoZ z ≤ 1 := by
      simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ] using hrhoOne
    nlinarith
  have hbeta' : 0 < ReferenceFirstLiveSourceSavedMoments.beta rate := by
    simpa only [ReferenceFirstLiveSourceSavedMoments.beta] using hbeta
  have hxi' : 0 < xiZ z := by
    simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ] using hxi
  have hbetaXi' : ReferenceFirstLiveSourceSavedMoments.beta rate ≤ xiZ z := by
    simpa only [ReferenceFirstLiveSourceSavedMoments.beta,
      ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ] using hbetaXi
  refine ⟨?_, ?_, ?_, ?_, hxi', hbeta'⟩
  · calc
      xiZ z * (vZ z) ^ 2 =
          ∫ u, (ReferenceFirstLiveSourceSavedMoments.f
            rate rewards C_star C_h q t s hs control0 i (xof z) u) ^ 2 ∂
            ContinuousLearningRows.timeControlLaw p := hsecond'.symm
      _ ≤ rhoZ z ^ 2 / xiZ z := by
          simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.rhoZ,
            ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ] using hsqRho
  · calc
      xiZ z * (vZ z) ^ 2 =
          ∫ u, (ReferenceFirstLiveSourceSavedMoments.f
            rate rewards C_star C_h q t s hs control0 i (xof z) u) ^ 2 ∂
            ContinuousLearningRows.timeControlLaw p := hsecond'.symm
      _ ≤ 1 / xiZ z := by
          simpa only [ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ] using hsqOne
  · exact div_le_div_of_nonneg_right hrhoSquare hxi'.le
  · exact one_div_le_one_div_of_le hbeta' hbetaXi'

/-- First conditional moment of the strict-past masked actual emission on the
same source measure and Fi, obtained by Mathlib's measurable-indicator rule
and C's unmasked source conditional expectation. -/
theorem retainedSaved_condExp_firstMoment :
    μZi[retainedSaved | Fi] =ᵐ[μZi]
      Set.indicator pastKeep (fun z : Zi => xiZ z * vZ z) := by
  have hmask := condExp_indicator
    (ReferenceFirstLiveSourceSavedMoments.followerSource_saved_integrable
      rate rewards C_star C_h q t s hs control0 i)
    (measurableSet_pastRetainedFollowerSet_follower
      rate rewards C_star C_h q t s hs control0 i)
  have hbase := ReferenceFirstLiveSourceSavedConditionalMoments.sourceSaved_condExp_firstMoment
    rate rewards C_star C_h q t s hs control0 i
  filter_upwards [hmask, hbase] with z hzMask hzBase
  rw [hzMask]
  by_cases hkeep : z ∈ pastKeep
  · simpa [hkeep] using hzBase
  · simp [hkeep]

/-- Square conditional moment of the masked emission. The pointwise square
identity handles both the strict-past event and its complement before applying
Mathlib's indicator theorem and C's same-source square conditional expectation. -/
theorem retainedSaved_condExp_secondMoment :
    μZi[(fun z : Zi => retainedSaved z ^ 2) | Fi] =ᵐ[μZi]
      Set.indicator pastKeep (fun z : Zi => xiZ z * (vZ z) ^ 2) := by
  have hpoint : (fun z : Zi => retainedSaved z ^ 2) =
      Set.indicator pastKeep (fun z : Zi => (saved z) ^ 2) := by
    funext z
    exact retainedSaved_sq_eq_indicator_saved_sq
      rate rewards C_star C_h q t s hs control0 i z
  rw [hpoint]
  have hmask := condExp_indicator
    (ReferenceFirstLiveSourceSavedMoments.followerSource_saved_sq_integrable
      rate rewards C_star C_h q t s hs control0 i)
    (measurableSet_pastRetainedFollowerSet_follower
      rate rewards C_star C_h q t s hs control0 i)
  have hbase := ReferenceFirstLiveSourceSavedConditionalMoments.sourceSaved_condExp_secondMoment
    rate rewards C_star C_h q t s hs control0 i
  filter_upwards [hmask, hbase] with z hzMask hzBase
  rw [hzMask]
  by_cases hkeep : z ∈ pastKeep
  · simpa [hkeep] using hzBase
  · simp [hkeep]

/-- The first conditional moment is nonnegative almost everywhere, with zero
on the off-event branch. -/
theorem retainedSaved_condExp_first_nonneg :
    0 ≤ᵐ[μZi] μZi[retainedSaved | Fi] := by
  have hce := retainedSaved_condExp_firstMoment
    rate rewards C_star C_h q t s hs control0 i
  filter_upwards [hce] with z hz
  rw [hz]
  by_cases hkeep : z ∈ pastKeep
  · simpa [hkeep, ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ,
      ReferenceFirstLiveSourcePrefixBranchInvariance.vZ] using
      (ReferenceFirstLiveSourceSavedConditionalMoments.follower_mean_bounds
        rate rewards C_star C_h q t s hs control0 i (xof z)).1.1
  · simp [hkeep]

/-- The first conditional moment obeys the strict-past masked quantization
lower bound, saved-reward upper bound, and unit reward ceiling. The lower bound
is zero off the event. -/
theorem retainedSaved_condExp_first_bounds :
    Set.indicator pastKeep (fun z : Zi =>
      rhoZ z - xiZ z / (rate.eta.val * (D p : ℝ))) ≤ᵐ[μZi]
        μZi[retainedSaved | Fi] ∧
    μZi[retainedSaved | Fi] ≤ᵐ[μZi]
      Set.indicator pastKeep (fun z : Zi => rhoZ z) ∧
    Set.indicator pastKeep (fun z : Zi => rhoZ z) ≤ᵐ[μZi]
      (fun _ : Zi => 1) := by
  have hce := retainedSaved_condExp_firstMoment
    rate rewards C_star C_h q t s hs control0 i
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep] using
        (source_first_candidate_quantization_bounds
          rate rewards C_star C_h q t s hs control0 i z).1
    · simp [hkeep]
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep] using
        (source_first_candidate_quantization_bounds
          rate rewards C_star C_h q t s hs control0 i z).2.1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep] using
        (source_first_candidate_quantization_bounds
          rate rewards C_star C_h q t s hs control0 i z).2.2
    · simp [hkeep]

/-- The square conditional moment has the event-masked first-moment upper
envelope, then the reciprocal-rate envelope, and finally `1 / beta`. -/
theorem retainedSaved_condExp_second_bounds :
    0 ≤ᵐ[μZi] μZi[(fun z : Zi => retainedSaved z ^ 2) | Fi] ∧
    μZi[(fun z : Zi => retainedSaved z ^ 2) | Fi] ≤ᵐ[μZi]
      Set.indicator pastKeep (fun z : Zi => rhoZ z ^ 2 / xiZ z) ∧
    Set.indicator pastKeep (fun z : Zi => rhoZ z ^ 2 / xiZ z) ≤ᵐ[μZi]
      Set.indicator pastKeep (fun z : Zi => 1 / xiZ z) ∧
    Set.indicator pastKeep (fun z : Zi => 1 / xiZ z) ≤ᵐ[μZi]
      (fun _ : Zi => 1 / ReferenceFirstLiveSourceSavedMoments.beta rate) := by
  have hce := retainedSaved_condExp_secondMoment
    rate rewards C_star C_h q t s hs control0 i
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep, ReferenceFirstLiveSourcePrefixBranchInvariance.xiZ,
        ReferenceFirstLiveSourcePrefixBranchInvariance.vZ] using
        (ReferenceFirstLiveSourceSavedConditionalMoments.follower_mean_bounds
          rate rewards C_star C_h q t s hs control0 i (xof z)).2.1
    · simp [hkeep]
  · filter_upwards [hce] with z hz
    rw [hz]
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep] using
        (source_second_candidate_quantization_bounds
          rate rewards C_star C_h q t s hs control0 i z).1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep] using
        (source_second_candidate_quantization_bounds
          rate rewards C_star C_h q t s hs control0 i z).2.2.1
    · simp [hkeep]
  · filter_upwards with z
    by_cases hkeep : z ∈ pastKeep
    · simpa [hkeep] using
        (source_second_candidate_quantization_bounds
          rate rewards C_star C_h q t s hs control0 i z).2.2.2.1
    · have hbeta := CanonicalRecordingRates.beta_pos p rate.eta.property
      have hinv : 0 ≤ 1 / ReferenceFirstLiveSourceSavedMoments.beta rate := by
        exact (div_pos (by norm_num) hbeta).le
      simp only [Set.indicator_of_notMem hkeep]
      exact hinv

end Bandits.Support.ReferenceFirstLiveRetainedConditionalMoments

end
