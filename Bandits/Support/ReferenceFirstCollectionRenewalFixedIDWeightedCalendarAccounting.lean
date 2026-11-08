/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget
public import Bandits.Support.ReferenceFirstCollectionPrecallFixedIDMean

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Fixed-ID localization of first-renewal weighted calendar energy

The estimates stay on each actual unnormalized first-renewal subtype. The
fixed-ID cylinder is pulled back into the existing predictable fields before
the conditional drifts are integrated. Their finite sum is transported back
to the original source by the literal zero extensions.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support ConstructorDimensions

namespace Bandits.Support.ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (control0 : ContinuousLearningRows.TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "S" => BootstrapPrivateRoundStreams.SourceInput p
local notation "μ" => BootstrapPrivateRoundStreams.sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "c" => CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)

local instance sourceInputMeasurableSpace : MeasurableSpace S := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The fixed-ID cylinder pulled back to the actual first-renewal source. -/
private def fixedIDCellSet (ids : CompletePublicTable.IDArray p)
    (u t : Fin p.T) : Set
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t) :=
  Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids

/-- The retained next-date and strict-future gate mass inside the same fixed-ID
cylinder, measured by the original unnormalized renewal source law. -/
def fixedIDCellAfterCallGateMass
    (ids : CompletePublicTable.IDArray p) (u t : Fin p.T) : ℝ :=
  (if hnext : t.val + 1 < p.T then
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t).real
        ((Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) ∩
          ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
            rate rewards C_star C_h u t hnext)
  else 0) +
    ∑ q ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
          ((Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids) ∩
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
              rate rewards C_star C_h u t q)

/-- The exact finite sum of fixed-ID retained after-call gates over the first
renewal cells. -/
def fixedIDAfterCallGateMass (ids : CompletePublicTable.IDArray p) : ℝ :=
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t

private theorem fixedIDCellSet_measurable_next (u t : Fin p.T) :
    MeasurableSet[
      ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0]
      (fixedIDCellSet rate rewards C_star C_h ids u t) := by
  change MeasurableSet[
    MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (t.val + 2))] (Subtype.val ⁻¹' D)
  exact (MeasurableSpace.measurableSet_comap).2 ⟨D,
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids (t.val + 1), rfl⟩

private theorem fixedIDCellSet_measurable_future (u t q : Fin p.T) :
    MeasurableSet[
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q]
      (fixedIDCellSet rate rewards C_star C_h ids u t) := by
  change MeasurableSet[
    MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
        control0 (q.val + 1))] (Subtype.val ⁻¹' D)
  exact (MeasurableSpace.measurableSet_comap).2 ⟨D,
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids q.val, rfl⟩

private theorem fixedIDNextWeightedEnergyStep
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (u t : Fin p.T)
    (hnext : t.val + 1 < p.T) :
    (11 / 2 : ℝ) *
        (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t ∩
          ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
            rate rewards C_star C_h u t hnext,
          ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
            rate rewards C_star C_h u t z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
          rate rewards C_star C_h u t hnext z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t ≤
      c * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (fixedIDCellSet rate rewards C_star C_h ids u t ∩
        ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
          rate rewards C_star C_h u t hnext) +
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus
          rate rewards C_star C_h u t z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  let G := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
    rate rewards C_star C_h u t hnext
  let B := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
    rate rewards C_star C_h u t
  let Vp := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
    rate rewards C_star C_h u t hnext
  let Vm := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus
    rate rewards C_star C_h u t
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hG0 := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
    rate rewards C_star C_h u t control0 hnext
  have hG : MeasurableSet G := hfield _ hG0
  have hD := fixedIDCellSet_measurable_next rate rewards C_star C_h control0 ids u t
  have hDG : MeasurableSet (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G) :=
    (hfield _ hD).inter hG
  have hterms :=
    ReferenceFirstCollectionRenewalNextDateRWeightedAccounting.actualTermIntegrability
      rate rewards C_star C_h u t control0 hnext
  have hB : Integrable B (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus_integrable
      rate rewards C_star C_h u t control0
  have hcost : Integrable (fun z => G.indicator B z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    hB.indicator hG
  have hone : Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator
      (fun _ => (1 : ℝ)) z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    (integrable_const (1 : ℝ)).indicator hDG
  have hlocal : Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator B z)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := hB.indicator hDG
  have hdiff : Integrable (fun z => Vp z - Vm z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    hterms.2.2.2.sub hterms.2.2.1
  have hDrift :=
    ReferenceFirstCollectionRenewalNextDateRWeightedAccounting.conditionalWeightedEnergyDrift_R
      rate rewards C_star C_h u t control0 hnext
  have hcreditPoint :
      (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => G.indicator
        (fun z => -(11 / 2 : ℝ) * B z + CanonicalRecordingRates.R p +
          (33 / 2 : ℝ) * (p.m : ℝ)) z) =ᵐ[ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t]
      (fun z => G.indicator
          (fun z => c - (11 / 2 : ℝ) * B z) z) := by
    filter_upwards [] with z
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      ring
    · simp [Set.indicator_of_notMem hz]
  have hcredit : Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => G.indicator
      (fun z => c - (11 / 2 : ℝ) * B z) z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
    have hfun : (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => G.indicator
        (fun z => c - (11 / 2 : ℝ) * B z) z) =
        fun z => G.indicator (fun _ => c) z -
          (11 / 2 : ℝ) * G.indicator B z := by
      funext z
      by_cases hz : z ∈ G
      · simp [Set.indicator, hz]
      · simp [Set.indicator, hz]
    rw [hfun]
    exact ((integrable_const c).indicator hG).sub
      (hcost.const_mul (11 / 2 : ℝ))
  have hmono :
      (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t)[fun z => Vp z - Vm z |
          ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
            rate rewards C_star C_h u t control0] z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) ≤
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        G.indicator (fun z => c - (11 / 2 : ℝ) * B z) z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    have hcreditPointLe :
        (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t => G.indicator
            (fun z => -(11 / 2 : ℝ) * B z + CanonicalRecordingRates.R p +
              (33 / 2 : ℝ) * (p.m : ℝ)) z) ≤ᵐ[
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t]
          (fun z => G.indicator
            (fun z => c - (11 / 2 : ℝ) * B z) z) := by
      filter_upwards [hcreditPoint] with z hz
      exact le_of_eq hz
    have h := setIntegral_mono_ae
      (s := fixedIDCellSet rate rewards C_star C_h ids u t)
      integrable_condExp.integrableOn
      hcredit.integrableOn (hDrift.trans hcreditPointLe)
    exact h
  rw [setIntegral_condExp hfield hdiff hD] at hmono
  have hlocalized := hmono
  have hsplit :
      (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        G.indicator (fun z => c - (11 / 2 : ℝ) * B z) z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
        c * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G) -
          (11 / 2 : ℝ) * (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, G.indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
    rw [setIntegral_indicator hG, ← integral_indicator hDG]
    have hfun : (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator
        (fun x => c - (11 / 2 : ℝ) * B x) z) =
        fun z => c * (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator (fun _ => (1 : ℝ)) z +
          (-(11 / 2 : ℝ)) * (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator B z := by
      funext z
      by_cases hz : z ∈ fixedIDCellSet rate rewards C_star C_h ids u t ∩ G
      · simp only [Set.indicator_of_mem hz]
        ring
      · simp only [Set.indicator_of_notMem hz]
        ring
    have hmass :
        (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator (fun _ => (1 : ℝ)) z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G) := by
      rw [integral_indicator hDG, integral_const, smul_eq_mul]
      simp [measureReal_def]
    have hbacklog :
        (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
          ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, G.indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
      rw [integral_indicator hDG, ← setIntegral_indicator hG]
    rw [hfun, integral_add (hone.const_mul c)
      (hlocal.const_mul (-(11 / 2 : ℝ))), integral_const_mul,
      integral_const_mul, hmass, hbacklog]
    ring
  rw [hsplit] at hlocalized
  have henergy :
      (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, Vp z - Vm z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
        (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, Vp z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) -
          ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, Vm z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    rw [integral_sub (hterms.2.2.2.mono_measure Measure.restrict_le_self)
      (hterms.2.2.1.mono_measure Measure.restrict_le_self)]
  rw [henergy] at hlocalized
  have hbacklog :
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, G.indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t =
        ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t ∩ G, B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := setIntegral_indicator hG
  rw [hbacklog] at hlocalized
  dsimp [Vp, Vm, G, B] at hlocalized ⊢
  linarith only [hlocalized]

private theorem fixedIDFutureRecordingCost_le_R
    (control0 : ContinuousLearningRows.TimeControl p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    ∀ᵐ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t,
      z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture →
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
        rate rewards C_star C_h u t q hfuture z ≤ CanonicalRecordingRates.R p := by
  filter_upwards [
    ReferenceFirstCollectionRenewalFutureNumericalWeightEnvelope.ae_Gfuture_actual_numerical_weight_envelope
      rate rewards C_star C_h u t control0 q hfuture] with z hwitness
  intro hz
  obtain ⟨r, data, xi, cell, hread, _, _, _, hparameters, _, _, _, _, _, _, hsum⟩ :=
    hwitness hz
  have hsupport :=
    ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
      rate rewards C_star C_h u t q hfuture hz
  have htheta (j : Fin p.K) :
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z =
      ProductSetLaw.theta p.m
        (fun i => (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (r.1 i).1) j := by
    simp only [ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus,
      Set.indicator_of_mem hsupport, hread]
    simp only [Option.elim_some]
    simp [ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters,
      ScoreWeights.scoreWeight, ReferenceFirstLaunchNumericalCell.queueParameters]
  have hcost :
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
        rate rewards C_star C_h u t q hfuture z =
      ∑ j : Fin p.K,
        ProductSetLaw.theta p.m
          (fun i => (1 + 1 / (ConstructorDimensions.D p : ℝ)) ^ (r.1 i).1) j /
            xi j := by
    rw [ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost,
      hparameters]
    simp_rw [htheta]
  rw [hcost]
  exact hsum

private theorem fixedIDFutureWeightedEnergyStep
    (control0 : ContinuousLearningRows.TimeControl p)
    (ids : CompletePublicTable.IDArray p) (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    (11 / 2 : ℝ) *
        (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t ∩
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
            rate rewards C_star C_h u t q.val,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog
            rate rewards C_star C_h u t q hfuture z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
          rate rewards C_star C_h u t q hfuture z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t ≤
      c * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (fixedIDCellSet rate rewards C_star C_h ids u t ∩
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
          rate rewards C_star C_h u t q.val) +
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
          rate rewards C_star C_h u t q hfuture z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  let G := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let B := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog
    rate rewards C_star C_h u t q hfuture
  let C := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureRecordingCost
    rate rewards C_star C_h u t q hfuture
  let Vp := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyPlus
    rate rewards C_star C_h u t q hfuture
  let Vm := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergyMinus
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hG0 := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hG : MeasurableSet G := hfield _ hG0
  have hD := fixedIDCellSet_measurable_future
    rate rewards C_star C_h control0 ids u t q
  have hDG : MeasurableSet (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G) :=
    (hfield _ hD).inter hG
  have hB : Integrable B (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedBacklog
      rate rewards C_star C_h u t q hfuture control0
  have hC : Integrable C (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureRecordingCost
      rate rewards C_star C_h u t q hfuture control0
  have hcostBound := fixedIDFutureRecordingCost_le_R
    rate rewards C_star C_h control0 u t q hfuture
  have hcreditPoint :
      (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => G.indicator
        (fun z => -(11 / 2 : ℝ) * B z + C z + (33 / 2 : ℝ) * (p.m : ℝ)) z) ≤ᵐ[ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t]
      (fun z => G.indicator
        (fun z => c - (11 / 2 : ℝ) * B z) z) := by
    filter_upwards [hcostBound] with z hz
    by_cases hg : z ∈ G
    · have hR := hz hg
      simp only [Set.indicator_of_mem hg]
      nlinarith only [hR]
    · simp [Set.indicator_of_notMem hg]
  have hcredit : Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => G.indicator
      (fun z => c - (11 / 2 : ℝ) * B z) z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
    have hfun : (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => G.indicator
        (fun z => c - (11 / 2 : ℝ) * B z) z) =
        fun z => G.indicator (fun _ => c) z -
          (11 / 2 : ℝ) * G.indicator B z := by
      funext z
      by_cases hz : z ∈ G
      · simp [Set.indicator, hz]
      · simp [Set.indicator, hz]
    rw [hfun]
    exact ((integrable_const c).indicator hG).sub
      ((hB.indicator hG).const_mul (11 / 2 : ℝ))
  have hdiff : Integrable (fun z => Vp z - Vm z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
    (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
      rate rewards C_star C_h u t q hfuture control0).sub
    (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
      rate rewards C_star C_h u t q hfuture control0)
  have hDrift :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedEnergy_condExp
      rate rewards C_star C_h u t control0 q hfuture
  have hmono :
      (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t)[fun z => Vp z - Vm z |
          ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
            rate rewards C_star C_h u t control0 q] z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) ≤
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        G.indicator (fun z => c - (11 / 2 : ℝ) * B z) z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t :=
    setIntegral_mono_ae (s := fixedIDCellSet rate rewards C_star C_h ids u t)
      integrable_condExp.integrableOn hcredit.integrableOn
      (hDrift.trans (by
        filter_upwards [hcreditPoint] with z hz
        exact hz))
  rw [setIntegral_condExp hfield hdiff hD] at hmono
  have hlocalized := hmono
  have hsplit :
      (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t,
        G.indicator (fun z => c - (11 / 2 : ℝ) * B z) z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
        c * (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G) -
          (11 / 2 : ℝ) * (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, G.indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
    rw [setIntegral_indicator hG, ← integral_indicator hDG]
    have hone : Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator
        (fun _ => (1 : ℝ)) z) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := (integrable_const _).indicator hDG
    have hlocal : Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator B z)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := hB.indicator hDG
    have hfun : (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator
        (fun x => c - (11 / 2 : ℝ) * B x) z) =
        fun z => c * (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator (fun _ => (1 : ℝ)) z +
          (-(11 / 2 : ℝ)) * (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator B z := by
      funext z
      by_cases hz : z ∈ fixedIDCellSet rate rewards C_star C_h ids u t ∩ G
      · simp only [Set.indicator_of_mem hz]
        ring
      · simp only [Set.indicator_of_notMem hz]
        ring
    have hmass :
        (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator (fun _ => (1 : ℝ)) z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G) := by
      rw [integral_indicator hDG, integral_const, smul_eq_mul]
      simp [measureReal_def]
    have hbacklog :
        (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, (fixedIDCellSet rate rewards C_star C_h ids u t ∩ G).indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
          ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, G.indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
      rw [integral_indicator hDG, ← setIntegral_indicator hG]
    rw [hfun, integral_add (hone.const_mul c)
      (hlocal.const_mul (-(11 / 2 : ℝ))), integral_const_mul,
      integral_const_mul, hmass, hbacklog]
    ring
  rw [hsplit] at hlocalized
  have henergy :
      (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, Vp z - Vm z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
        (∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, Vp z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) -
          ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, Vm z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    rw [integral_sub
      ((ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
        rate rewards C_star C_h u t q hfuture control0).mono_measure Measure.restrict_le_self)
      ((ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
        rate rewards C_star C_h u t q hfuture control0).mono_measure Measure.restrict_le_self)]
  rw [henergy] at hlocalized
  have hbacklog :
      ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t, G.indicator B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t =
        ∫ z in fixedIDCellSet rate rewards C_star C_h ids u t ∩ G, B z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := setIntegral_indicator hG
  rw [hbacklog] at hlocalized
  have hgate :
      ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
        rate rewards C_star C_h u t q.val = G := by
    simp [G,
      ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
      q.isLt, hfuture]
  rw [hgate]
  dsimp [Vp, Vm, G, B] at hlocalized ⊢
  linarith only [hlocalized]

private theorem setIntegral_add_of_integrable {α : Type*} [MeasurableSpace α]
    (μ0 : Measure α) (s : Set α) (f g : α → ℝ)
    (hf : Integrable f μ0) (hg : Integrable g μ0) :
    (∫ x in s, f x + g x ∂μ0) =
      (∫ x in s, f x ∂μ0) + ∫ x in s, g x ∂μ0 := by
  rw [integral_add (hf.mono_measure Measure.restrict_le_self)
    (hg.mono_measure Measure.restrict_le_self)]

private theorem setIntegral_sub_of_integrable {α : Type*} [MeasurableSpace α]
    (μ0 : Measure α) (s : Set α) (f g : α → ℝ)
    (hf : Integrable f μ0) (hg : Integrable g μ0) :
    (∫ x in s, f x - g x ∂μ0) =
      (∫ x in s, f x ∂μ0) - ∫ x in s, g x ∂μ0 := by
  rw [integral_sub (hf.mono_measure Measure.restrict_le_self)
    (hg.mono_measure Measure.restrict_le_self)]

private theorem fixedID_zeroExtendCell_integral
    (E : Set S) (hE : MeasurableSet E)
    (f : {x // x ∈ E} → ℝ) (mu0 : Measure S)
    (ν0 : Measure {x // x ∈ E})
    (hmap : ν0.map Subtype.val = mu0.restrict E)
    (D0 : Set S) (hD0 : MeasurableSet D0) :
    (∫ x in D0,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x ∂mu0) =
      ∫ z in (Subtype.val ⁻¹' D0), f z ∂ν0 := by
  have hzero (x : S) :
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x =
        E.indicator
          (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f) x := by
    classical
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_mem hx]
    · have hno : ¬ ∃ y : {x // x ∈ E}, (y : S) = x := by
        rintro ⟨y, hy⟩
        exact hx (hy ▸ y.property)
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        Set.indicator_of_notMem hx, Function.extend_apply', hno]
  have hrestrict :
      (∫ x in D0 ∩ E,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x ∂mu0) =
      (∫ x in D0,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x
          ∂mu0.restrict E) := by
    rw [Measure.restrict_restrict hD0]
  calc
    _ = ∫ x in D0 ∩ E,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x ∂mu0 := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD0
        (Set.inter_subset_left)
      intro x hx
      have hxE : x ∉ E := by
        intro hmem
        exact hx.2 ⟨hx.1, hmem⟩
      rw [hzero, Set.indicator_of_notMem hxE]
    _ = ∫ x in D0,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x
            ∂mu0.restrict E := hrestrict
    _ = ∫ z in (Subtype.val ⁻¹' D0),
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f z.val ∂ν0 := by
      rw [← hmap]
      exact (MeasurableEmbedding.subtype_coe hE).setIntegral_map
        (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f) D0
    _ = ∫ z in (Subtype.val ⁻¹' D0), f z ∂ν0 := by
      apply setIntegral_congr_fun
      exact hD0.preimage measurable_subtype_coe
      intro z hz
      exact Subtype.val_injective.extend_apply f (fun _ => 0) z

private theorem fixedID_zeroExtendCell_integrable
    (E : Set S) (hE : MeasurableSet E)
    (f : {x // x ∈ E} → ℝ) (mu0 : Measure S)
    (ν0 : Measure {x // x ∈ E})
    (hcomap : ν0 = mu0.comap (Subtype.val : {x // x ∈ E} → S))
    (hf : Integrable f ν0) :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f) mu0 := by
  have hcomp : Integrable
      (fun x : {x // x ∈ E} =>
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x.val)
      ν0 := by
    have heq : (fun x : {x // x ∈ E} =>
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x.val) = f := by
      funext x
      exact Subtype.val_injective.extend_apply f (fun _ => 0) x
    rw [heq]
    exact hf
  have hOn : IntegrableOn
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f) E mu0 := by
    apply (integrableOn_iff_comap_subtypeVal hE).2
    change Integrable
      (fun x : {x // x ∈ E} =>
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f x.val)
      (mu0.comap (Subtype.val : {x // x ∈ E} → S))
    simpa [hcomap] using hcomp
  have hzero :
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f =
        E.indicator
          (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell E f) := by
    funext x
    classical
    by_cases hx : x ∈ E
    · simp only [Set.indicator_of_mem hx]
    · have hno : ¬ ∃ y : {x // x ∈ E}, (y : S) = x := by
        rintro ⟨y, hy⟩
        exact hx (hy ▸ y.property)
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        Set.indicator_of_notMem hx, Function.extend_apply', hno]
  rw [hzero]
  exact (integrable_indicator_iff hE).2 hOn

private theorem fixedID_doubleZeroExtend_integral
    (f : ∀ u t : Fin p.T,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t → ℝ)
    (hfi : ∀ u t, Integrable (f u t)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t))
    (F : S → ℝ)
    (hF : F = fun z => ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) (f u t) z) :
    (∫ z in D, F z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in (Subtype.val ⁻¹' D), f u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t := by
  classical
  have hcellInt (u t : Fin p.T) : Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) (f u t)) μ := by
    apply fixedID_zeroExtendCell_integrable
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t)
      (f u t) μ (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t)
      (by rfl)
    exact hfi u t
  have hcellIntD (u t : Fin p.T) : Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) (f u t))
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict D) :=
    (hcellInt u t).mono_measure Measure.restrict_le_self
  have hinnerInt (u : Fin p.T) : Integrable
      (fun z : S => ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t) (f u t) z)
      ((BootstrapPrivateRoundStreams.sourceInputLaw p).restrict D) :=
    integrable_finsetSum Finset.univ (fun t _ => hcellIntD u t)
  change (∫ z, F z ∂(BootstrapPrivateRoundStreams.sourceInputLaw p).restrict D) = _
  rw [hF, integral_finsetSum Finset.univ (fun u _ => hinnerInt u)]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun t _ => hcellIntD u t)]
  apply Finset.sum_congr rfl
  intro t ht
  exact fixedID_zeroExtendCell_integral
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t)
    (f u t) μ (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val
      rate rewards C_star C_h u t)
    D (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)

private theorem fixedID_originalAfterCallBacklog_integral
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
        rate rewards C_star C_h z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in (Subtype.val ⁻¹' D),
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
  simpa only [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog] using
    fixedID_doubleZeroExtend_integral rate rewards C_star C_h ids
      (fun (u : Fin p.T) (t : Fin p.T) => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t)
      (fun (u : Fin p.T) (t : Fin p.T) => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog_integrable
        rate rewards C_star C_h u t control0)
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
        rate rewards C_star C_h)
      rfl

private theorem fixedID_originalTerminalEnergy_integral
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
        rate rewards C_star C_h z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in (Subtype.val ⁻¹' D),
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
  simpa only [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy] using
    fixedID_doubleZeroExtend_integral rate rewards C_star C_h ids
      (fun (u : Fin p.T) (t : Fin p.T) => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
        rate rewards C_star C_h u t)
      (fun (u : Fin p.T) (t : Fin p.T) => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy_integrable
        rate rewards C_star C_h u t control0)
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
        rate rewards C_star C_h)
      rfl

private theorem fixedID_originalSupportLoss_integral
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
        rate rewards C_star C_h z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in (Subtype.val ⁻¹' D),
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
  simpa only [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss] using
    fixedID_doubleZeroExtend_integral rate rewards C_star C_h ids
      (fun (u : Fin p.T) (t : Fin p.T) => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
        rate rewards C_star C_h u t)
      (fun (u : Fin p.T) (t : Fin p.T) => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_integrable
        rate rewards C_star C_h u t control0)
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
        rate rewards C_star C_h)
      rfl

private theorem fixedID_wholeEnergy_local_transport
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z in (Subtype.val ⁻¹' D),
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t) =
      ∫ z in D ∩
        ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
          rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ := by
  classical
  let E : Fin p.T × Fin p.T → Set S := fun a =>
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h a.1 a.2
  have hcell (u t : Fin p.T) :
      (∫ z in (Subtype.val ⁻¹' D),
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t) =
      ∫ z in D ∩ E (u, t),
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ := by
    let C := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h u t
    have hC : MeasurableSet C :=
      ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t
    have hmap := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val
      rate rewards C_star C_h u t
    have hmapInt :
        (∫ z in (Subtype.val ⁻¹' D),
          ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z.val ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t) =
        ∫ z in D ∩ C,
          ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ := by
      calc
        _ = ∫ z in D,
              ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
                rate rewards C_star C_h z ∂
                  (BootstrapPrivateRoundStreams.sourceInputLaw p).restrict C := by
          rw [← hmap]
          exact ((MeasurableEmbedding.subtype_coe hC).setIntegral_map
            (ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
              rate rewards C_star C_h) D).symm
        _ = _ := by
          rw [Measure.restrict_restrict
            (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)]
    calc
      _ = ∫ z in (Subtype.val ⁻¹' D),
            ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
              rate rewards C_star C_h z.val ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t := by
          apply setIntegral_congr_fun
            ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
              measurable_subtype_coe)
          intro z hz
          exact (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.wholeEnergyObservations_eq_callObservations
            rate rewards C_star C_h u t z).2.1
      _ = _ := hmapInt
  have hpair : Pairwise (fun a b => Disjoint (D ∩ E a) (D ∩ E b)) := by
    intro a b hab
    apply (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEvents_disjoint
      rate rewards C_star C_h a.1 a.2 b.1 b.2 hab).mono
    · intro z hz
      exact hz.2
    · intro z hz
      exact hz.2
  have hmeas (a : Fin p.T × Fin p.T) : MeasurableSet (D ∩ E a) :=
    (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).inter
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h a.1 a.2)
  have hInt (a : Fin p.T × Fin p.T) : IntegrableOn
      (ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus rate rewards C_star C_h)
      (D ∩ E a) μ :=
    (ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_integrable
      rate rewards C_star C_h control0).integrableOn.mono_set
        (fun z hz => hz.1)
  have hUnion : (⋃ a : Fin p.T × Fin p.T, D ∩ E a) =
      D ∩ ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
        rate rewards C_star C_h := by
    ext z
    simp [E, ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion]
  calc
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z in (Subtype.val ⁻¹' D),
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t) =
      ∑ a : Fin p.T × Fin p.T,
        ∫ z in (Subtype.val ⁻¹' D),
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
            rate rewards C_star C_h a.1 a.2 z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h a.1 a.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ a : Fin p.T × Fin p.T,
        ∫ z in D ∩ E a,
          ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hcell a.1 a.2
    _ = ∫ z in (⋃ a : Fin p.T × Fin p.T, D ∩ E a),
          ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
            rate rewards C_star C_h z ∂μ :=
      (integral_iUnion_fintype hmeas hpair hInt).symm
    _ = _ := by rw [hUnion]

/-- The actual first-renewal weighted energy bound, transported to the same
original fixed-ID cylinder. -/
theorem fixedIDAfterCallCellEnergyBudget (control0 : ContinuousLearningRows.TimeControl p)
    (u t : Fin p.T) :
    (11 / 2 : ℝ) *
        (∫ z in (Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids),
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t) +
      ∫ z in (Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids),
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
          rate rewards C_star C_h u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t +
      ∫ z in (Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids),
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
          rate rewards C_star C_h u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t ≤
      c * fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t +
      ∫ z in (Subtype.val ⁻¹' ReferenceFixedIDSourceSection.fixedIDSourceSection ids),
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t := by
  let E := fixedIDCellSet rate rewards C_star C_h ids u t
  let ν := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
  let dates := ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t
  change (11 / 2 : ℝ) *
        (∫ z in E, ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
          rate rewards C_star C_h u t z ∂ν) +
      ∫ z in E, ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
        rate rewards C_star C_h u t z ∂ν +
      ∫ z in E, ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
        rate rewards C_star C_h u t z ∂ν ≤
    c * fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t +
      ∫ z in E, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
        rate rewards C_star C_h u t z ∂ν
  by_cases hnext : t.val + 1 < p.T
  · by_cases hfuture : t.val + 2 < p.T
    · let qfirst : Fin p.T := ⟨t.val + 2, hfuture⟩
      have hqfirst : qfirst.val = t.val + 2 := rfl
      have hnextBudget := fixedIDNextWeightedEnergyStep rate rewards C_star C_h
        control0 ids u t hnext
      let nG := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
        rate rewards C_star C_h u t hnext
      let nB := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
        rate rewards C_star C_h u t
      let nVp := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vplus
        rate rewards C_star C_h u t hnext
      let nVm := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus
        rate rewards C_star C_h u t
      let qEnergyMinus := fun n : ℕ => ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt
        rate rewards C_star C_h u t n
      let qEnergyPlus := fun n : ℕ => ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt
        rate rewards C_star C_h u t n
      let qBacklog := fun n : ℕ => ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt
        rate rewards C_star C_h u t n
      let qMass := fun n : ℕ => ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt
        rate rewards C_star C_h u t n
      have hsteps : ∀ n ∈ dates,
          (11 / 2 : ℝ) *
              (∫ z in E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n,
                (if hn : n < p.T then
                  if hf : t.val + 1 < n then
                    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog rate rewards C_star C_h u t
                      ⟨n, hn⟩ hf
                  else 0
                else 0) z ∂ν) +
            ∫ z in E, qEnergyPlus n z ∂ν ≤
            c * ν.real (E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n) +
              ∫ z in E, qEnergyMinus n z ∂ν := by
        intro n hn
        have hn' := Finset.mem_Ico.mp hn
        have hqn : n < p.T := hn'.2
        have hq : t.val + 1 < n := by omega
        let q : Fin p.T := ⟨n, hqn⟩
        have hqv : q.val = n := rfl
        have hstep := fixedIDFutureWeightedEnergyStep rate rewards C_star C_h
          control0 ids u t q (by simpa [q] using hq)
        simpa [q, qEnergyMinus, qEnergyPlus,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
          hqn, hq, hqv] using hstep
      have hsumSteps :
          (11 / 2 : ℝ) *
              (∑ n ∈ dates,
                ∫ z in E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n,
                  (if hn : n < p.T then
                    if hf : t.val + 1 < n then
                      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog rate rewards C_star C_h u t
                        ⟨n, hn⟩ hf
                    else 0
                  else 0) z ∂ν) +
            ∑ n ∈ dates, ∫ z in E, qEnergyPlus n z ∂ν ≤
            c * (∑ n ∈ dates, ν.real
              (E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n)) +
              ∑ n ∈ dates, ∫ z in E, qEnergyMinus n z ∂ν := by
        calc
          _ = ∑ n ∈ dates,
                ((11 / 2 : ℝ) *
                    (∫ z in E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n,
                      (if hn : n < p.T then
                        if hf : t.val + 1 < n then
                          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog rate rewards C_star C_h u t
                            ⟨n, hn⟩ hf
                        else 0
                      else 0) z ∂ν) +
                  ∫ z in E, qEnergyPlus n z ∂ν) := by
            simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          _ ≤ ∑ n ∈ dates,
                (c * ν.real (E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n) +
                  ∫ z in E, qEnergyMinus n z ∂ν) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hsteps n hn
          _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      have hqEnergyDiffInt (n : ℕ) (hn : n ∈ dates) :
          Integrable (fun z => qEnergyMinus n z - qEnergyPlus n z)
            (ν.restrict E) := by
        have hn' := Finset.mem_Ico.mp hn
        have hqn : n < p.T := hn'.2
        have hq : t.val + 1 < n := by omega
        let q : Fin p.T := ⟨n, hqn⟩
        have hminus := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
          rate rewards C_star C_h u t q (by simpa [q] using hq) control0
        have hplus := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
          rate rewards C_star C_h u t q (by simpa [q] using hq) control0
        have hminus' : Integrable (qEnergyMinus n) ν := by
          simpa [qEnergyMinus,
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt,
            hqn, hq, q] using hminus
        have hplus' : Integrable (qEnergyPlus n) ν := by
          simpa [qEnergyPlus,
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt,
            hqn, hq, q] using hplus
        exact (hminus'.mono_measure Measure.restrict_le_self).sub
          (hplus'.mono_measure Measure.restrict_le_self)
      have hadjEq : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
          rate rewards C_star C_h u t =
            fun z => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
                rate rewards C_star C_h u t z -
              ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss
                rate rewards C_star C_h u t qfirst hqfirst z := by
        funext z
        simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss, hfuture,
          qfirst, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss]
      have henergySum :
          (∑ n ∈ dates,
            ∫ z in E, qEnergyMinus n z - qEnergyPlus n z ∂ν) =
          (∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
            ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z ∂ν -
              ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
        have hsumInt :
            (∑ n ∈ dates,
              ∫ z in E, qEnergyMinus n z - qEnergyPlus n z ∂ν) =
            ∫ z in E, ∑ n ∈ dates, (qEnergyMinus n z - qEnergyPlus n z) ∂ν := by
          rw [← integral_finsetSum dates (fun n hn => hqEnergyDiffInt n hn)]
        have hinitial : Integrable (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t) ν := by
          have hminus := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus rate rewards C_star C_h u t
            qfirst (by simp [qfirst]) control0
          simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy, qfirst, hfuture,
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt, qfirst] using hminus
        have hterminal : Integrable (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t) ν := by
          have hT := p.one_le_T
          let qlast : Fin p.T := ⟨p.T - 1, by omega⟩
          have hq : t.val + 1 < qlast.val := by
            change t.val + 1 < p.T - 1
            omega
          have hplus := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
            rate rewards C_star C_h u t qlast hq control0
          simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy,
            hfuture, qlast] using hplus
        have hboundary : Integrable (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t
            qfirst hqfirst) ν :=
          ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integrable_boundaryLoss rate rewards C_star C_h u t control0 qfirst hqfirst
        have hsupport : Integrable (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss rate rewards C_star C_h u t) ν :=
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_integrable rate rewards C_star C_h u t control0
        have hadjEq : ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t =
            fun z => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss rate rewards C_star C_h u t z -
              ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst z := by
          funext z
          simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss, hfuture,
            qfirst, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss]
        have hadj : Integrable (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t) ν := by
          rw [hadjEq]
          exact hsupport.sub hboundary
        have htermEq :
            ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z ∂ν =
              ∫ z in E, ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy rate rewards C_star C_h u t z ∂ν := by
          apply setIntegral_congr_fun
            ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
              measurable_subtype_coe)
          intro z hz
          simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy, hfuture]
        have hpathInt :
            (∫ z in E,
              (∑ n ∈ dates, (qEnergyMinus n z - qEnergyPlus n z)) ∂ν) =
            ∫ z in E,
              (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t z -
                ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z -
                  ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z) ∂ν := by
          apply integral_congr_ae
          filter_upwards [] with z
          exact ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergy_boundary_loss_identity rate rewards C_star C_h u t z
        have hlinear :
            (∫ z in E,
              (∑ n ∈ dates, (qEnergyMinus n z - qEnergyPlus n z)) ∂ν) =
              (∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t z ∂ν) -
                ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z ∂ν -
                  ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
          rw [hpathInt]
          rw [setIntegral_sub_of_integrable ν E
              (fun z => ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy
                rate rewards C_star C_h u t z -
                  ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy
                    rate rewards C_star C_h u t z)
              (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss
                rate rewards C_star C_h u t)
              (hinitial.sub hterminal) hadj]
          rw [setIntegral_sub_of_integrable ν E
            (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy
              rate rewards C_star C_h u t)
            (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy
              rate rewards C_star C_h u t)
            hinitial hterminal]
        exact hsumInt.trans hlinear
      have hfutureBudget :
          (11 / 2 : ℝ) *
              (∑ n ∈ dates,
                ∫ z in E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n,
                  (if hn : n < p.T then
                    if hf : t.val + 1 < n then
                      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog rate rewards C_star C_h u t
                        ⟨n, hn⟩ hf
                    else 0
                  else 0) z ∂ν) +
            ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z ∂ν +
              ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z ∂ν ≤
            c * (∑ n ∈ dates, ν.real
              (E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n)) +
              ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t z ∂ν := by
        have hsumSwap :
            (∑ n ∈ dates, ∫ z in E, qEnergyMinus n z ∂ν) -
              ∑ n ∈ dates, ∫ z in E, qEnergyPlus n z ∂ν =
                (∑ n ∈ dates,
                  ∫ z in E, qEnergyMinus n z - qEnergyPlus n z ∂ν) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro n hn
          have hn' := Finset.mem_Ico.mp hn
          have hq : t.val + 1 < n := by omega
          let q : Fin p.T := ⟨n, hn'.2⟩
          have hm := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
            rate rewards C_star C_h u t q (by simpa [q] using hq) control0
          have hp := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyPlus
            rate rewards C_star C_h u t q (by simpa [q] using hq) control0
          have hm0 : Integrable (qEnergyMinus n) ν := by
            simpa [qEnergyMinus,
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyMinusAt,
              hn'.2, hq, q] using hm
          have hp0 : Integrable (qEnergyPlus n) ν := by
            simpa [qEnergyPlus,
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureEnergyPlusAt,
              hn'.2, hq, q] using hp
          exact (setIntegral_sub_of_integrable ν E (qEnergyMinus n) (qEnergyPlus n) hm0 hp0).symm
        have hdiff := hsumSwap.trans henergySum
        linarith only [hsumSteps, hdiff]
      have hbacklogTerm (n : ℕ) (hn : n ∈ dates) :
          (∫ z in E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n,
            (if hn' : n < p.T then
              if hf : t.val + 1 < n then
                ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog rate rewards C_star C_h u t
                  ⟨n, hn'⟩ hf
              else 0
            else 0) z ∂ν) =
          ∫ z in E, qBacklog n z ∂ν := by
        have hn' := Finset.mem_Ico.mp hn
        have hqn : n < p.T := hn'.2
        have hq : t.val + 1 < n := by omega
        have hGfield := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
          rate rewards C_star C_h u t ⟨n, hqn⟩ hq control0
        have htq : t.val < (⟨n, hqn⟩ : Fin p.T).val := by
          change t.val < n
          omega
        have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
          rate rewards C_star C_h u t control0 ⟨n, hqn⟩ htq
        have hG : MeasurableSet
            (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
              rate rewards C_star C_h u t ⟨n, hqn⟩ hq) := hfield _ hGfield
        simp [qBacklog,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
          hqn, hq]
        exact (setIntegral_indicator hG).symm
      have hqBacklogInt (n : ℕ) (hn : n ∈ dates) : Integrable (qBacklog n) ν := by
        have hn' := Finset.mem_Ico.mp hn
        have hqn : n < p.T := hn'.2
        have hq : t.val + 1 < n := by omega
        let q : Fin p.T := ⟨n, hqn⟩
        have hqInt := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedBacklog
          rate rewards C_star C_h u t q (by simpa [q] using hq) control0
        have htq : t.val < q.val := by
          change t.val < n
          omega
        have hGfield := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
          rate rewards C_star C_h u t q hq control0
        have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
          rate rewards C_star C_h u t control0 q htq
        have hG : MeasurableSet
            (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
              rate rewards C_star C_h u t q hq) := hfield _ hGfield
        simpa [qBacklog,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureBacklogAt,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
          hqn, hq, q] using hqInt.indicator hG
      have hbacklogSum :
          (∑ n ∈ dates,
            ∫ z in E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n,
              (if hn : n < p.T then
                if hf : t.val + 1 < n then
                  ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureWeightedBacklog rate rewards C_star C_h u t
                    ⟨n, hn⟩ hf
                else 0
              else 0) z ∂ν) =
            ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z ∂ν := by
        calc
          _ = ∑ n ∈ dates, ∫ z in E, qBacklog n z ∂ν := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hbacklogTerm n hn
          _ = ∫ z in E, ∑ n ∈ dates, qBacklog n z ∂ν := by
            rw [← integral_finsetSum dates (fun n hn =>
              (hqBacklogInt n hn).mono_measure Measure.restrict_le_self)]
          _ = ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z ∂ν := by
            apply setIntegral_congr_fun
              ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
                measurable_subtype_coe)
            intro z hz
            simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog,
              dates, qBacklog]
      have hbacklogCell :
          (∫ z in E,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog rate rewards C_star C_h u t z ∂ν) =
            (∫ z in E ∩ nG, nB z ∂ν) +
              ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z ∂ν := by
        have hnextInt :=
          ReferenceFirstCollectionRenewalNextDateRWeightedAccounting.actualTermIntegrability
            rate rewards C_star C_h u t control0 hnext
        have hnextPoint :
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog rate rewards C_star C_h u t = fun z =>
              nG.indicator nB z + ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t z := by
          funext z
          simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog, hnext, nG, nB]
        have hbacklogRemainder : Integrable
            (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
              rate rewards C_star C_h u t) ν := by
          have hsub :=
            (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog_integrable
              rate rewards C_star C_h u t control0).sub hnextInt.2.1
          have hpoint :
              ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
                  rate rewards C_star C_h u t - (nG.indicator nB) =
                ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
                  rate rewards C_star C_h u t := by
            funext z
            simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog,
              hnext, nG, nB]
          rw [← hpoint]
          exact hsub
        have hGfield := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
          rate rewards C_star C_h u t control0 hnext
        have hG := (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
          rate rewards C_star C_h u t control0) _ hGfield
        have hG' : MeasurableSet nG := by
          simpa [nG, ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.G] using hG
        rw [hnextPoint, setIntegral_add_of_integrable ν E
          (fun z => nG.indicator nB z)
          (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog rate rewards C_star C_h u t)
          hnextInt.2.1
          hbacklogRemainder]
        rw [setIntegral_indicator hG']
      rw [← hbacklogSum] at hbacklogCell
      have hterminal :
          ∫ z in E, ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy rate rewards C_star C_h u t z ∂ν =
            ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureTerminalEnergy rate rewards C_star C_h u t z ∂ν := by
        apply setIntegral_congr_fun
          ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
            measurable_subtype_coe)
        intro z hz
        simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy, hfuture]
      have hadjAndBoundary :
          ∫ z in E, ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss rate rewards C_star C_h u t z ∂ν =
            ∫ z in E, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst z ∂ν +
              ∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z ∂ν := by
        have hpoint : ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss rate rewards C_star C_h u t = fun z =>
            ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst z +
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t z := by
          funext z
          simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss, hfuture,
            qfirst, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss]
        rw [hpoint, setIntegral_add_of_integrable ν E
          (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst)
          (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureAdjacentLoss rate rewards C_star C_h u t)
          (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integrable_boundaryLoss rate rewards C_star C_h u t control0 qfirst hqfirst)
          (by
            rw [hadjEq]
            exact (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_integrable rate rewards C_star C_h u t control0).sub
              (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integrable_boundaryLoss rate rewards C_star C_h u t control0 qfirst hqfirst))]
      have hboundaryLocal :
          (∫ z in E, nVp z ∂ν) =
            (∫ z in E, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t z ∂ν) +
              ∫ z in E, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst z ∂ν := by
        have hpoint : nVp = fun z =>
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t z +
              ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst z := by
          funext z
          have hread := ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integral_next_outgoing_eq_future_plus_loss
            rate rewards C_star C_h u t control0 qfirst hqfirst
          -- The public pointwise identity is the exposed definition of boundaryLoss.
          simp [nVp,
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy,
            hfuture, qfirst, ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss]
        have hinitialInt : Integrable
            (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy
              rate rewards C_star C_h u t) ν := by
          simpa [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy,
            hfuture, qfirst] using
            (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.integrable_futureWeightedEnergyMinus
              rate rewards C_star C_h u t qfirst (by simp [qfirst]) control0)
        rw [hpoint, setIntegral_add_of_integrable ν E
          (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureInitialEnergy rate rewards C_star C_h u t)
          (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.boundaryLoss rate rewards C_star C_h u t qfirst hqfirst)
          hinitialInt
          (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.integrable_boundaryLoss rate rewards C_star C_h u t control0 qfirst hqfirst)]
      have hwholeJoin :
          ∫ z in E, nVm z ∂ν =
            ∫ z in E, ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus rate rewards C_star C_h u t z ∂ν := by
        apply setIntegral_congr_fun
          ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
            measurable_subtype_coe)
        intro z hz
        exact (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.whole_next_energy_join rate rewards C_star C_h u t z).symm
      have hmass : fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t =
          ν.real (E ∩ nG) +
            ∑ n ∈ dates, ν.real (E ∩ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt rate rewards C_star C_h u t n) := by
        simp [fixedIDCellAfterCallGateMass, fixedIDCellSet, hnext, dates, E, nG]; rfl
      rw [hbacklogCell, hterminal, hadjAndBoundary, ← hwholeJoin, hmass]
      have hsumCombined := add_le_add hnextBudget hfutureBudget
      rw [hboundaryLocal] at hsumCombined
      dsimp [nG, nB, nVp, nVm] at hsumCombined ⊢
      linarith only [hsumCombined]
    · have hlast : t.val + 2 = p.T := by omega
      have hdates : dates = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hn' := Finset.mem_Ico.mp hn
        omega
      have hfutureEmpty :
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t = ∅ := by
        simpa [dates] using hdates
      have hbacklogPoint :
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
            rate rewards C_star C_h u t = fun z =>
              (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
                rate rewards C_star C_h u t hnext).indicator
                (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Bminus
                  rate rewards C_star C_h u t) z := by
        funext z
        simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog,
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog,
          hfutureEmpty, hnext]
      have hmass : fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t =
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real
              (fixedIDCellSet rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
                  rate rewards C_star C_h u t hnext) := by
        simp [fixedIDCellAfterCallGateMass, fixedIDCellSet, hnext, hfutureEmpty]
      have hbacklog := fixedIDNextWeightedEnergyStep rate rewards C_star C_h
        control0 ids u t hnext
      have hGfield := ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.measurableSet_G
        rate rewards C_star C_h u t control0 hnext
      have hG := (ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
        rate rewards C_star C_h u t control0) _ hGfield
      have hG' : MeasurableSet
          (ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate
            rate rewards C_star C_h u t hnext) := by
        simpa [ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.G] using hG
      rw [hbacklogPoint, setIntegral_indicator hG', hmass]
      have hwholeJoin :
          (∫ z in E,
            ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.Vminus
              rate rewards C_star C_h u t z ∂ν) =
          (∫ z in E,
            ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
              rate rewards C_star C_h u t z ∂ν) := by
        apply setIntegral_congr_fun
          ((ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
            measurable_subtype_coe)
        intro z hz
        exact (ReferenceFirstCollectionRenewalEnergyBoundaryJoins.whole_next_energy_join
          rate rewards C_star C_h u t z).symm
      rw [← hwholeJoin]
      simpa [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy,
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss,
        hfuture, hnext] using hbacklog
  · have hlast : t.val + 1 = p.T := by omega
    have hdates : dates = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      omega
    have hfuture : ¬ t.val + 2 < p.T := by omega
    have hfutureEmpty :
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t = ∅ := by
      simpa [dates] using hdates
    have hfutureBacklogZero :
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog
            rate rewards C_star C_h u t = fun _ => 0 := by
      funext z
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.supportedFutureBacklog,
        hfutureEmpty]
    have hmass : fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t = 0 := by
      simp [fixedIDCellAfterCallGateMass, hnext, hfutureEmpty]
    have hbacklog :
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
          rate rewards C_star C_h u t = fun _ => 0 := by
      funext z
      simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog,
        hnext, hfutureBacklogZero]
    have hloss :
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
          rate rewards C_star C_h u t = fun _ => 0 := by
      funext z
      simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss, hfuture]
    rw [hmass, hbacklog, hloss]
    simp [ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy,
      hnext, hfuture]

theorem fixedIDAfterCallOriginalEnergyBudget
    (control0 : ContinuousLearningRows.TimeControl p) :
    (11 / 2 : ℝ) *
        (∫ z in D,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
            rate rewards C_star C_h z ∂μ) +
      ∫ z in D,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
          rate rewards C_star C_h z ∂μ +
      ∫ z in D,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
          rate rewards C_star C_h z ∂μ ≤
      c * fixedIDAfterCallGateMass rate rewards C_star C_h ids +
      ∫ z in D,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ := by
  have hbacklog := fixedID_originalAfterCallBacklog_integral
    rate rewards C_star C_h ids control0
  have hterminal := fixedID_originalTerminalEnergy_integral
    rate rewards C_star C_h ids control0
  have hloss := fixedID_originalSupportLoss_integral
    rate rewards C_star C_h ids control0
  have henergy := fixedID_wholeEnergy_local_transport
    rate rewards C_star C_h ids control0
  rw [hbacklog, hterminal, hloss]
  rw [fixedIDAfterCallGateMass]
  have hsum :
      (11 / 2 : ℝ) *
          (∑ u : Fin p.T, ∑ t : Fin p.T,
            ∫ z in (Subtype.val ⁻¹' D),
              ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
                rate rewards C_star C_h u t z ∂
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                    rate rewards C_star C_h u t) +
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in (Subtype.val ⁻¹' D),
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t) +
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in (Subtype.val ⁻¹' D),
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t) ≤
      c * (∑ u : Fin p.T, ∑ t : Fin p.T,
        fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in (Subtype.val ⁻¹' D),
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
    calc
      _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
            ((11 / 2 : ℝ) *
              ∫ z in (Subtype.val ⁻¹' D),
                ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
                  rate rewards C_star C_h u t z ∂
                    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                      rate rewards C_star C_h u t +
             ∫ z in (Subtype.val ⁻¹' D),
                ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
                  rate rewards C_star C_h u t z ∂
                    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                      rate rewards C_star C_h u t +
             ∫ z in (Subtype.val ⁻¹' D),
                ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
                  rate rewards C_star C_h u t z ∂
                    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                      rate rewards C_star C_h u t) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
            (c * fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t +
             ∫ z in (Subtype.val ⁻¹' D),
               ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
                 rate rewards C_star C_h u t z ∂
                   ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                     rate rewards C_star C_h u t) := by
          exact Finset.sum_le_sum fun u hu => Finset.sum_le_sum fun t ht =>
            fixedIDAfterCallCellEnergyBudget rate rewards C_star C_h ids control0 u t
      _ = _ := by simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hunionBound :
      (∫ z in D ∩
          ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
            rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ) ≤
      ∫ z in D, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ := by
    apply setIntegral_mono_set
      (ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_integrable
        rate rewards C_star C_h control0).integrableOn
      (Filter.Eventually.of_forall fun z =>
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_nonneg
          rate rewards C_star C_h z)
      (Filter.Eventually.of_forall fun z hz => hz.1)
  rw [henergy] at hsum
  have hfinal := add_le_add_left hunionBound
    (c * (∑ u : Fin p.T, ∑ t : Fin p.T,
      fixedIDCellAfterCallGateMass rate rewards C_star C_h ids u t))
  exact le_trans hsum (by simpa [add_comm] using hfinal)
