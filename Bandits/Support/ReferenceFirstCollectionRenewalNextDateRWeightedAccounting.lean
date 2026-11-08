/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep
public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope

import Mathlib.Tactic

/-!
# Immediate next-date R-weighted energy accounting

The actual next-date numerical weight envelope bounds the prior cost on the
same retained event. This refines the immediate-date weighted energy drift
and budget on the original unnormalized renewal source law.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalNextDateRWeightedAccounting

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)

abbrev Source :=
  _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Source
    rate rewards C_star C_h u t

local notation "Z" => Source rate rewards C_star C_h u t
local notation "ν" =>
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
local notation "Fq" =>
  ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0

local instance sourceInputMeasurableSpace :
    MeasurableSpace (BootstrapPrivateRoundStreams.SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalLawFinite : IsFiniteMeasure ν :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite
    rate rewards C_star C_h u t

/-- The prior marginal is the same product-set marginal of the same literal
current-state registers as the numerical envelope. -/
theorem preTheta_eq_numericalTheta (z : Z) (j : Fin p.K) :
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta rate rewards C_star C_h u t z j =
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.theta rate rewards C_star C_h u t z j := by
  rfl

/-- On the retained next-date event, the actual enabled prior cost is bounded
by the canonical R envelope on the original renewal law. -/
theorem ae_priorCost_le_R_on_retained (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    ∀ᵐ z : Z ∂ν,
      z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.G rate rewards C_star C_h u t hq →
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z ≤
          CanonicalRecordingRates.R p := by
  have henv := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.ae_G_actual_numerical_weight_envelope
    rate rewards C_star C_h u t control0 hq
  filter_upwards [henv] with z hz
  intro hg
  obtain ⟨view, xi, cell, selected, hview, hparameters, hcell, henabled,
    hrate, hcanonical, hselection, hwholeDown, hpayloadSame, hweights,
    hbound⟩ := hz hg
  have hsum :
      (∑ j : Fin p.K, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.theta rate rewards C_star C_h u t z j / xi j) ≤
        CanonicalRecordingRates.R p := hbound xi hparameters
  have hsum' :
      (∑ j : Fin p.K, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.preTheta rate rewards C_star C_h u t z j / xi j) ≤
        CanonicalRecordingRates.R p := by
    calc
      _ = ∑ j : Fin p.K, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.theta rate rewards C_star C_h u t z j / xi j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [preTheta_eq_numericalTheta rate rewards C_star C_h u t z j]
      _ ≤ CanonicalRecordingRates.R p := hsum
  change _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z ≤ _
  rw [_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost, hparameters]
  exact hsum'

/-- The masked actual prior cost obeys the same R bound as a constant on the
retained event, including when that event or the source law has zero mass. -/
theorem ae_indicator_priorCost_le_R (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq) ≤ᵐ[ν]
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
        (fun _ : Z => CanonicalRecordingRates.R p) := by
  filter_upwards [ae_priorCost_le_R_on_retained rate rewards C_star C_h u t
    control0 hq] with z hz
  by_cases hg : z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq
  · simp only [Set.indicator_of_mem hg]
    exact hz (by change z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.G rate rewards C_star C_h u t hq; exact hg)
  · simp only [Set.indicator_of_notMem hg]
    exact le_rfl

/-- The immediate-date conditional weighted-energy drift with its actual
numerical prior cost replaced by the canonical R envelope. -/
theorem conditionalWeightedEnergyDrift_R (hq : t.val + 1 < p.T) :
    ν[(fun z =>
      _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z -
        _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z) | Fq] ≤ᵐ[ν]
      (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
        (fun z => -(11 / 2 : ℝ) * _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t z +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) := by
  filter_upwards [
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.conditionalWeightedEnergyDrift rate rewards C_star C_h u t control0 hq,
    ae_priorCost_le_R_on_retained rate rewards C_star C_h u t control0 hq]
    with z hdrift hcost
  by_cases hg : z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq
  · have hprior := hcost (by change z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.G rate rewards C_star C_h u t hq; exact hg)
    have hg' : z ∈ Set.ofPred
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.G
          rate rewards C_star C_h u t hq) := by
      change z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
        rate rewards C_star C_h u t hq
      exact hg
    rw [Set.indicator_of_mem (s := Set.ofPred (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.G rate rewards C_star C_h u t hq)) hg']
      at hdrift
    rw [Set.indicator_of_mem hg]
    calc
      _ ≤ -(11 / 2 : ℝ) * _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t z +
          _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z + (33 / 2 : ℝ) * p.m := hdrift
      _ ≤ -(11 / 2 : ℝ) * _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t z +
          CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m := by
        linarith only [hprior]
  · have hg' : z ∉ Set.ofPred (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.G rate rewards C_star C_h u t hq) := by
      change z ∉ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq
      exact hg
    rw [Set.indicator_of_notMem (s := Set.ofPred (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.G rate rewards C_star C_h u t hq)) hg']
      at hdrift
    rw [Set.indicator_of_notMem hg]
    exact hdrift

/-- Integrability of the actual retained prior cost and backlog, together with
both actual energies, on the original renewal measure. -/
theorem actualTermIntegrability (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    Integrable
        ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hq).indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost
            rate rewards C_star C_h u t hq)) ν ∧
      Integrable
        ((_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hq).indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
            rate rewards C_star C_h u t)) ν ∧
      Integrable
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus
          rate rewards C_star C_h u t) ν ∧
      Integrable
        (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
          rate rewards C_star C_h u t hq) ν := by
  let G := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
    rate rewards C_star C_h u t hq
  have hGfield := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
    rate rewards C_star C_h u t control0 hq
  have hle := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG : MeasurableSet G := hle G hGfield
  exact ⟨
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost_integrable
      rate rewards C_star C_h u t control0 hq).indicator hG,
    (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus_integrable
      rate rewards C_star C_h u t control0).indicator hG,
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus_integrable
      rate rewards C_star C_h u t control0,
    _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_integrable
      rate rewards C_star C_h u t control0 hq⟩

/-- The R-refined integral budget keeps the actual outgoing energy on the left
and uses the original, possibly zero-mass renewal source law. -/
theorem actualRWeightedEnergyAccounting (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) *
        (∫ z, (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) +
      ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          (ν).real (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq) +
        ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
  let G := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq
  let c : ℝ := (33 / 2 : ℝ) * p.m
  have hGfield := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G rate rewards C_star C_h u t control0 hq
  have hle := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG : MeasurableSet G := by
    exact hle G hGfield
  have hterms := actualTermIntegrability rate rewards C_star C_h u t control0 hq
  have hconstant : Integrable (G.indicator (fun _ : Z => c)) ν :=
    (integrable_const c).indicator hG
  have hsplit : G.indicator
      (fun z => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z + c) =
        (fun z => G.indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq) z +
          G.indicator (fun _ : Z => c) z) := by
    funext z
    by_cases hg : z ∈ G
    · simp only [Set.indicator_of_mem hg]
    · simp only [Set.indicator_of_notMem hg, add_zero]
  have hcost : Integrable (G.indicator
      (fun z => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z + c)) ν := by
    rw [hsplit]
    exact hterms.1.add hconstant
  have hcostR : Integrable (G.indicator
      (fun _ : Z => CanonicalRecordingRates.R p + c)) ν :=
    (integrable_const (CanonicalRecordingRates.R p + c)).indicator hG
  have hcostAE : G.indicator
      (fun z => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z + c) ≤ᵐ[ν]
      G.indicator (fun _ : Z => CanonicalRecordingRates.R p + c) := by
    filter_upwards [
      ae_priorCost_le_R_on_retained rate rewards C_star C_h u t control0 hq]
      with z hz
    by_cases hg : z ∈ G
    · simp only [Set.indicator_of_mem hg]
      have hprior : _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z ≤
          CanonicalRecordingRates.R p := by
        exact hz (by change z ∈ _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateNumericalWeightEnvelope.G rate rewards C_star C_h u t hq; exact hg)
      dsimp [c]
      linarith only [hprior]
    · simp only [Set.indicator_of_notMem hg]
      exact le_rfl
  have hcostInt := integral_mono_ae hcost hcostR hcostAE
  rw [integral_indicator_const (μ := ν) (CanonicalRecordingRates.R p + c) hG,
    smul_eq_mul] at hcostInt
  have hcostInt' :
      (∫ z, G.indicator
        (fun z => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z + c) z ∂ν) ≤
        (CanonicalRecordingRates.R p + c) * (ν).real G := by
    simpa only [mul_comm] using hcostInt
  have hcostInt'' :
      (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t, G.indicator
          (fun z => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost
            rate rewards C_star C_h u t hq z + c) z ∂ν) ≤
        (CanonicalRecordingRates.R p + c) * (ν).real G := hcostInt'
  have hbase := _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.weightedEnergyAccounting rate rewards C_star C_h u t control0 hq
  change (11 / 2 : ℝ) *
      (∫ z, G.indicator (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) ≤
      (∫ z, G.indicator
        (fun z => _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.priorCost rate rewards C_star C_h u t hq z + c) z ∂ν) +
        (∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν) -
          ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν at hbase
  change (11 / 2 : ℝ) *
      (∫ z, G.indicator (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) +
        ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν ≤
      (CanonicalRecordingRates.R p + c) * (ν).real G +
        ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν
  linarith only [hbase, hcostInt'']

/-- Dropping the nonnegative outgoing energy gives the immediate retained
backlog budget. -/
theorem actualRWeightedBacklogBudget (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) *
        (∫ z, (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) *
          (ν).real (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq) +
        ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
  have hbudget := actualRWeightedEnergyAccounting rate rewards C_star C_h u t control0 hq
  have hplus : 0 ≤ ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν := by
    apply integral_nonneg
    intro z
    exact (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_bounds rate rewards C_star C_h u t hq z).1
  linarith only [hbudget, hplus]

/-- The outgoing-energy version with retained-event mass bounded by the total
mass of the same unnormalized renewal law. -/
theorem actualRWeightedEnergyAccounting_univ (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) *
        (∫ z, (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) +
      ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * (ν).real Set.univ +
        ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
  have hbudget := actualRWeightedEnergyAccounting rate rewards C_star C_h u t control0 hq
  have hR : 0 ≤ CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m := by
    have hmK : (p.m : ℝ) < (p.K : ℝ) := Nat.cast_lt.mpr p.m_lt_K
    have hmpos : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (m_pos p)
    unfold CanonicalRecordingRates.R
    nlinarith only [hmK, hmpos]
  have hmass :
      (ν).real (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq) ≤ (ν).real Set.univ :=
    measureReal_mono (Set.subset_univ _)
  exact hbudget.trans (by gcongr)

/-- The corresponding total-mass backlog estimate after dropping outgoing
energy. The coefficient is nonnegative by the actual parameter inequalities. -/
theorem actualRWeightedBacklogBudget_univ (control0 : TimeControl p) (hq : t.val + 1 < p.T) :
    (11 / 2 : ℝ) *
        (∫ z, (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate rate rewards C_star C_h u t hq).indicator
          (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus rate rewards C_star C_h u t) z ∂ν) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * p.m) * (ν).real Set.univ +
        ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus rate rewards C_star C_h u t z ∂ν := by
  have hbudget := actualRWeightedEnergyAccounting_univ rate rewards C_star C_h u t control0 hq
  have hplus : 0 ≤ ∫ z, _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus rate rewards C_star C_h u t hq z ∂ν := by
    apply integral_nonneg
    intro z
    exact (_root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus_bounds rate rewards C_star C_h u t hq z).1
  linarith only [hbudget, hplus]

end Bandits.Support.ReferenceFirstCollectionRenewalNextDateRWeightedAccounting

end
