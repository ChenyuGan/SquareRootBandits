/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstLiveConditionalWeightedDrift

import Bandits.Support.ReferenceFirstLiveAnchorRateFeasibility
import Mathlib.Tactic

/-!
# R-bounded drift and localized backlog budget on the first-live branch

Sources: `sources/zip4/manuscript/04_slow_fast_learner.tex:84-188,245-318`,
`sources/zip4/manuscript/06_interruptions.tex:391-408,425-426`, and
`sources/zip4/manuscript/07_public_setup.tex:127-164`.

This module combines the actual anchor-rate bound with the inherited
conditional drift on the same finite, unnormalized, continuing first-live
branch. It also records the corresponding budget on each measurable prefix of
the existing field. These are one-step branch results, not an all-calendar
telescope or a queue-lemma closure.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveRateBoundedDrift

abbrev Parameters := ReferenceFirstLiveConditionalWeightedDrift.Parameters
abbrev RateInput := ReferenceFirstLiveConditionalWeightedDrift.RateInput
abbrev RewardTable := ReferenceFirstLiveConditionalWeightedDrift.RewardTable
abbrev TimeControl := ReferenceFirstLiveConditionalWeightedDrift.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T)
  (s : ℕ) (hs : s ≤ t.val) (control0 : TimeControl p)

local notation "Zplus" =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
    rate rewards C_star C_h q t s hs control0
local notation "muPlus" =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
local notation "Fplus" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
    rate rewards C_star C_h q t s hs control0
local notation "G" =>
  ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
local notation "thetaBefore" =>
  ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
    rate rewards C_star C_h q t s hs control0
local notation "weightedBacklogBefore" =>
  ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
local notation "potentialBefore" =>
  ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
    rate rewards C_star C_h q t s hs control0
local notation "potentialAfter" =>
  ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
    rate rewards C_star C_h q t s hs control0

local instance instFiniteBranchMeasure : IsFiniteMeasure muPlus :=
  ReferenceFirstLiveAllArmPrefixAdaptation.isFiniteMeasure_branchSourceMeasure
    rate rewards C_star C_h q t s hs control0

local instance instFinitePrefixTrim : IsFiniteMeasure
    ((muPlus).trim
      (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
        rate rewards C_star C_h q t s hs control0)) :=
  ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_trim_finite
    rate rewards C_star C_h q t s hs control0

/-- The literal canonical recording-rate constant on this parameter carrier. -/
def R {p : Parameters} : ℝ := CanonicalRecordingRates.R p

/-- The source drift constant, with the canonical `R` and the exact
`(33/2) * m` correction. -/
def C {p : Parameters} : ℝ := R (p := p) + (33 / 2 : ℝ) * p.m

/-- The source all-arm score weights, strict-past run, and actual marker rates
have the canonical `R` bound. The readouts unfold to the same sum proved by
the actual anchor-feasibility producer. -/
theorem markerRateWeightSum_le_R (z : Zplus) :
    ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum
      rate rewards C_star C_h q t s hs control0 z ≤
      R (p := p) := by
  change
    (∑ j : Fin p.K,
      ProductSetLaw.theta p.m
        (RecordedQueueRun.scoreWeight
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (List.take (t.val - s)
              (ReferenceFirstLiveSourceCellReadout.cells
                rate rewards C_star C_h q t s hs control0 z)))) j /
        ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
          rate rewards C_star C_h q t s hs control0 j z) ≤
      CanonicalRecordingRates.R p
  exact ReferenceFirstLiveAnchorRateFeasibility.sum_thetaBefore_div_markerRatePlus_le_R
    rate rewards C_star C_h q t s hs control0 z

/-- The unnormalized conditional expectation of the actual potential change
obeys the `R`-bounded drift inequality on the same branch. The indicator is
retained, including when the strict-past safe set is empty. -/
theorem potential_drift_conditional_R :
    muPlus[(fun z : Zplus => potentialAfter z - potentialBefore z) | Fplus] ≤ᵐ[muPlus]
      Set.indicator G (fun z : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore z +
          C (p := p)) := by
  have hD :=
    ReferenceFirstLiveConditionalWeightedDrift.potential_drift_conditional_rate_sum
      rate rewards C_star C_h q t s hs control0
  have hrate := markerRateWeightSum_le_R rate rewards C_star C_h q t s hs control0
  have hpoint :
      (fun z : Zplus => Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum
            rate rewards C_star C_h q t s hs control0 x +
          (33 / 2 : ℝ) * p.m) z) ≤ᵐ[muPlus]
      (fun z : Zplus => Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          C (p := p)) z) := by
    apply ae_of_all
    intro z
    by_cases hz : z ∈ G
    · have hrate' :
          ReferenceFirstLiveConditionalWeightedDrift.markerRateWeightSum
            rate rewards C_star C_h q t s hs control0 z ≤
            CanonicalRecordingRates.R p := by
        simpa [R] using hrate z
      simp only [Set.indicator_of_mem hz, C, R]
      linarith [hrate']
    · simp [Set.indicator, hz]
  exact hD.trans hpoint

private theorem integrable_driftRhs :
    Integrable (fun z : Zplus => Set.indicator G (fun x : Zplus =>
      -(11 / 2 : ℝ) * weightedBacklogBefore x +
        C (p := p)) z) muPlus := by
  have hG := ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
    rate rewards C_star C_h q t s hs control0
  have hbase : Integrable (fun z : Zplus =>
      -(11 / 2 : ℝ) * weightedBacklogBefore z +
        C (p := p)) muPlus :=
    (ReferenceFirstLiveQueueEnergyEnvelope.integrable_weightedBacklogBefore
      rate rewards C_star C_h q t s hs control0).const_mul (-(11 / 2 : ℝ)) |>.add
        (integrable_const _)
  exact hbase.indicator hG

/-- Every measurable prefix of the inherited field satisfies the weighted
backlog budget. Its mass is the original branch measure of `B ∩ G`; `B` is a
local analysis set and adds no physical-law premise. -/
theorem weightedBacklog_budget_on (B : Set Zplus) (hB : MeasurableSet[Fplus] B) :
    (11 / 2 : ℝ) *
        (∫ z in B, Set.indicator G (fun x : Zplus => weightedBacklogBefore x) z ∂muPlus) ≤
      C (p := p) * (muPlus).real (B ∩ G) +
        (∫ z in B, potentialBefore z ∂muPlus) -
        (∫ z in B, potentialAfter z ∂muPlus) := by
  have hfield := ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
    rate rewards C_star C_h q t s hs control0
  have hBambient : MeasurableSet B := hfield B hB
  have hG := ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
    rate rewards C_star C_h q t s hs control0
  have hdiff := ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialDifference
    rate rewards C_star C_h q t s hs control0
  have hright := integrable_driftRhs rate rewards C_star C_h q t s hs control0
  have hcond := potential_drift_conditional_R
    rate rewards C_star C_h q t s hs control0
  have hmono :
      (∫ z in B,
        muPlus[(fun x : Zplus => potentialAfter x - potentialBefore x) | Fplus] z ∂muPlus) ≤
        (∫ z in B, Set.indicator G (fun x : Zplus =>
          -(11 / 2 : ℝ) * weightedBacklogBefore x +
            C (p := p)) z ∂muPlus) :=
    setIntegral_mono_ae (integrable_condExp.integrableOn) hright.integrableOn hcond
  rw [setIntegral_condExp hfield hdiff hB] at hmono
  have hGlocalized : MeasurableSet (B ∩ G) := hBambient.inter hG
  have hbacklog := ReferenceFirstLiveQueueEnergyEnvelope.integrable_weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  have hmasked : Integrable (fun z : Zplus =>
      Set.indicator (B ∩ G) (fun x : Zplus => weightedBacklogBefore x) z) muPlus :=
    hbacklog.indicator hGlocalized
  have hmaskedOne : Integrable (fun z : Zplus =>
      Set.indicator (B ∩ G) (fun _ : Zplus => (1 : ℝ)) z) muPlus :=
    (integrable_const (1 : ℝ)).indicator hGlocalized
  have hsplit :
      (∫ z in B, Set.indicator G (fun x : Zplus =>
        -(11 / 2 : ℝ) * weightedBacklogBefore x +
          C (p := p)) z ∂muPlus) =
        -(11 / 2 : ℝ) *
            (∫ z in B, Set.indicator G
              (fun x : Zplus => weightedBacklogBefore x) z ∂muPlus) +
        C (p := p) * (muPlus).real (B ∩ G) := by
    rw [setIntegral_indicator hG, ← integral_indicator hGlocalized]
    have hfun :
        (fun z : Zplus => Set.indicator (B ∩ G) (fun x : Zplus =>
          -(11 / 2 : ℝ) * weightedBacklogBefore x +
            C (p := p)) z) =
        (fun z : Zplus =>
          -(11 / 2 : ℝ) *
              Set.indicator (B ∩ G) (fun x : Zplus => weightedBacklogBefore x) z +
            C (p := p) *
              Set.indicator (B ∩ G) (fun _ : Zplus => (1 : ℝ)) z) := by
      funext z
      by_cases hz : z ∈ B ∩ G <;> simp [Set.indicator, hz]
    rw [hfun, integral_add (hmasked.const_mul (-(11 / 2 : ℝ)))
      (hmaskedOne.const_mul (C (p := p))),
      integral_const_mul, integral_indicator hGlocalized,
      ← setIntegral_indicator hG, integral_const_mul,
      integral_indicator_const (1 : ℝ) hGlocalized, smul_eq_mul, mul_one]
  have hdiffSplit :
      (∫ z in B, potentialAfter z - potentialBefore z ∂muPlus) =
        (∫ z in B, potentialAfter z ∂muPlus) -
          (∫ z in B, potentialBefore z ∂muPlus) :=
    integral_sub (ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialAfter
      rate rewards C_star C_h q t s hs control0).integrableOn
      (ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialBefore
        rate rewards C_star C_h q t s hs control0).integrableOn
  rw [hdiffSplit, hsplit] at hmono
  linarith

/-- The unlocalized one-step weighted backlog budget on the same finite,
unnormalized first-live branch measure. -/
theorem weightedBacklog_budget :
    (11 / 2 : ℝ) *
        (∫ z : Zplus, Set.indicator G
          (fun x : Zplus => weightedBacklogBefore x) z ∂muPlus) ≤
      C (p := p) * (muPlus).real G +
        (∫ z : Zplus, potentialBefore z ∂muPlus) -
        (∫ z : Zplus, potentialAfter z ∂muPlus) := by
  simpa only [Set.univ_inter, setIntegral_univ] using
    weightedBacklog_budget_on rate rewards C_star C_h q t s hs control0
      Set.univ MeasurableSet.univ

end Bandits.Support.ReferenceFirstLiveRateBoundedDrift

end
