/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalNextLearningMoments
public import Bandits.Support.ReferenceFirstCollectionRenewalFutureLearningMoments
public import Bandits.Support.ReferenceFirstCollectionPrecallFixedIDMean

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-!
# Fixed-ID first-renewal learning moments

These estimates localize the existing next-date and strict-future observations
on the original fixed-ID cylinder inside the unnormalized first-renewal source.
Every date keeps its own actual retained-gate mass.
-/

@[expose] public section
noncomputable section

open MeasureTheory
open Bandits.Support ConstructorDimensions
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalFixedIDLearningMoments

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl
variable {p : Parameters}
variable (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)
  (S : ProductSetLaw.ProductSet p.K p.m)

abbrev Source (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalNextLearningMoments.Source
    rate rewards C_star C_h u t

local notation "Z" => Source rate rewards C_star C_h u t
local notation "ν" => ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
local notation "Dids" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids

/-- The literal fixed-ID section pulled back to the existing renewal subtype. -/
def fixedIDRenewalSection (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (ids : CompletePublicTable.IDArray p) :
    Set (Source rate rewards C_star C_h u t) :=
  (ReferenceFixedIDSourceSection.fixedIDSourceSection ids).preimage Subtype.val

local notation "Dut" => fixedIDRenewalSection rate rewards C_star C_h u t ids

/-- The immediate next-date retained-gate mass on the original ID section.
The natural selector returns zero at the horizon boundary. -/
def fixedIDNextGateMass (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (ids : CompletePublicTable.IDArray p) : ℝ :=
  if hq : t.val + 1 < p.T then
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t).real
      (fixedIDRenewalSection rate rewards C_star C_h u t ids ∩
        ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
          rate rewards C_star C_h u t hq)
  else 0

/-- The exact date-local fixed-ID mass for one strict-future calendar date. -/
def fixedIDFutureGateMassAt (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (ids : CompletePublicTable.IDArray p)
    (n : ℕ) : ℝ :=
  if hn : n < p.T then
    if hfuture : t.val + 1 < n then
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (fixedIDRenewalSection rate rewards C_star C_h u t ids ∩
          ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t ⟨n, hn⟩ hfuture)
    else 0
  else 0

/-- Sum of the exact fixed-ID gate masses over the existing clipped strict-future
calendar. -/
def fixedIDFutureGateMass (rate : RateInput p) (rewards : RewardTable p)
    (C_star C_h : ℝ) (u t : Fin p.T) (ids : CompletePublicTable.IDArray p) : ℝ :=
  ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
    fixedIDFutureGateMassAt rate rewards C_star C_h u t ids n

private theorem integrable_of_indicator_const (c : ℝ) {A : Set Z}
    (hA : MeasurableSet A) : Integrable (A.indicator (fun _ : Z => c)) ν :=
  (integrable_const c).indicator hA

private theorem setIntegral_indicator_inter (A B : Set Z) (c : ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    (∫ z in A, B.indicator (fun _ : Z => c) z ∂ν) = c * (ν).real (A ∩ B) := by
  rw [← integral_indicator hA]
  have hpoint : A.indicator (fun z => B.indicator (fun _ : Z => c) z) =
      (A ∩ B).indicator (fun _ : Z => c) := by
    funext z
    by_cases hzA : z ∈ A <;> by_cases hzB : z ∈ B <;>
      simp [Set.indicator, hzA, hzB]
  rw [hpoint, integral_indicator_const _ (hA.inter hB), smul_eq_mul, mul_comm]

include control0 ids

/-- The original fixed-ID cylinder is measurable in the actual next prior
field. Its source offset is `t + 2`, so the next control remains excluded. -/
theorem measurableSet_fixedIDRenewalSection_nextPriorField :
    MeasurableSet[ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
      rate rewards C_star C_h u t control0] Dut := by
  have hprefix :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids (t.val + 1)
  have hsource : MeasurableSet[MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2))]
      Dut := by
    change MeasurableSet[MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 2))]
      ((ReferenceFixedIDSourceSection.fixedIDSourceSection ids).preimage Subtype.val)
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨Dids, hprefix, rfl⟩
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_eq_comap
    rate rewards C_star C_h u t control0
  have hcanonical : MeasurableSet[
      ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
        rate rewards C_star C_h u t control0] Dut := hsource
  rw [hfield] at hcanonical ⊢
  exact hcanonical

/-- The same original fixed-ID cylinder is measurable in each actual strict-
future prior field, at offset `q + 1`. -/
theorem measurableSet_fixedIDRenewalSection_futurePriorField (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] Dut := by
  have hprefix :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids q.val
  have hsource : MeasurableSet[MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1))]
      Dut := by
    change MeasurableSet[MeasurableSpace.comap Subtype.val
      (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (q.val + 1))]
      ((ReferenceFixedIDSourceSection.fixedIDSourceSection ids).preimage Subtype.val)
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨Dids, hprefix, rfl⟩
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_eq_comap
    rate rewards C_star C_h u t control0 q (by omega)
  have hcanonical : MeasurableSet[
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] Dut := hsource
  rw [hfield] at hcanonical ⊢
  exact hcanonical

omit control0 in
private theorem fixedIDRenewalSection_measurable_ambient : MeasurableSet Dut := by
  exact (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids).preimage
    measurable_subtype_coe

omit ids in
private theorem nextGate_measurable (hq : t.val + 1 < p.T) :
    MeasurableSet (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
      rate rewards C_star C_h u t hq) :=
  ReferenceFirstCollectionRenewalNextDateExponentialStep.measurableSet_retainedNextDate_ambient
    rate rewards C_star C_h u t control0 hq

omit ids in
private theorem futureGate_measurable (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    MeasurableSet (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
      rate rewards C_star C_h u t q hfuture) :=
  (ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)) _
    (ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
      rate rewards C_star C_h u t q hfuture control0)

/-- Restricted next-date arrival moment, retaining exactly the same ID and
next-date gate intersection in its mass. -/
theorem integral_nextArrivalObservation_fixedID (hq : t.val + 1 < p.T) :
    0 ≤ ∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation
          rate rewards C_star C_h u t hq z ∂ν ∧
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation
          rate rewards C_star C_h u t hq z ∂ν) ≤
        (p.m : ℝ) * (ν).real (Dut ∩
          ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
            rate rewards C_star C_h u t hq) := by
  let Fq := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
  let Gq := ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
    rate rewards C_star C_h u t hq
  let cexp := ν[ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation
    rate rewards C_star C_h u t hq | Fq]
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hDfield := measurableSet_fixedIDRenewalSection_nextPriorField
    rate rewards C_star C_h u t control0 ids
  have hDambient := fixedIDRenewalSection_measurable_ambient
    rate rewards C_star C_h u t ids
  have hInt := ReferenceFirstCollectionRenewalNextLearningMoments.integrable_arrivalObservation
    rate rewards C_star C_h u t control0 hq
  have hceInt : Integrable cexp ν := integrable_condExp
  have hbounds :=
    ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation_condExp_ae_bounds
      rate rewards C_star C_h u t control0 hq
  have hceEq : (∫ z in Dut, cexp z ∂ν) =
      ∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation
          rate rewards C_star C_h u t hq z ∂ν :=
    setIntegral_condExp hfield hInt hDfield
  have hzeroOn : IntegrableOn (fun _ : Z => (0 : ℝ)) Dut ν :=
    (integrable_const (0 : ℝ)).integrableOn (s := Dut)
  have hceOn : IntegrableOn cexp Dut ν := hceInt.integrableOn (s := Dut)
  have hzero := setIntegral_mono_ae hzeroOn hceOn
    (hbounds.mono fun z hz => hz.1)
  have hupperInt := integrable_of_indicator_const rate rewards C_star C_h u t (p.m : ℝ)
    (nextGate_measurable rate rewards C_star C_h u t control0 hq)
  have hupperOn : IntegrableOn (Gq.indicator (fun _ : Z => (p.m : ℝ))) Dut ν :=
    hupperInt.integrableOn (s := Dut)
  have hupper := setIntegral_mono_ae hceOn hupperOn
    (hbounds.mono fun z hz => hz.2)
  have hgate := setIntegral_indicator_inter rate rewards C_star C_h u t
    Dut Gq (p.m : ℝ) hDambient
    (nextGate_measurable rate rewards C_star C_h u t control0 hq)
  refine ⟨?_, ?_⟩
  · rw [← hceEq]
    simpa using hzero
  · calc
      (∫ z in Dut,
          ReferenceFirstCollectionRenewalNextLearningMoments.arrivalObservation
            rate rewards C_star C_h u t hq z ∂ν) = ∫ z in Dut, cexp z ∂ν := hceEq.symm
      _ ≤ ∫ z in Dut, Gq.indicator (fun _ : Z => (p.m : ℝ)) z ∂ν := by
        simpa [cexp, Gq] using hupper
      _ = (p.m : ℝ) * (ν).real (Dut ∩ Gq) := hgate

/-- Restricted next-date rounded reward-gap transfer on the original fixed-ID
section, including its same-date comparator and exact gate mass. -/
theorem integral_nextRoundedRewardGap_fixedID (hq : t.val + 1 < p.T) :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalNextLearningMoments.roundedRewardGap
        rate rewards C_star C_h u t hq S z ∂ν) ≤
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.comparatorObservation
          rate rewards C_star C_h u t hq S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (Dut ∩
          ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
            rate rewards C_star C_h u t hq) := by
  let Fq := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField
    rate rewards C_star C_h u t control0
  let Gq := ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
    rate rewards C_star C_h u t hq
  let obs := ReferenceFirstCollectionRenewalNextLearningMoments.comparatorObservation
    rate rewards C_star C_h u t hq S
  let gap := ReferenceFirstCollectionRenewalNextLearningMoments.roundedRewardGap
    rate rewards C_star C_h u t hq S
  let cexp := ν[obs | Fq]
  have hfield := ReferenceFirstCollectionRenewalNextControlLaw.nextPriorField_le
    rate rewards C_star C_h u t control0
  have hDfield := measurableSet_fixedIDRenewalSection_nextPriorField
    rate rewards C_star C_h u t control0 ids
  have hDambient := fixedIDRenewalSection_measurable_ambient
    rate rewards C_star C_h u t ids
  have hgateMeas := nextGate_measurable rate rewards C_star C_h u t control0 hq
  have hgapInt := ReferenceFirstCollectionRenewalNextLearningMoments.integrable_roundedRewardGap
    rate rewards C_star C_h u t control0 hq S
  have hobsInt := ReferenceFirstCollectionRenewalNextLearningMoments.integrable_comparatorObservation
    rate rewards C_star C_h u t control0 hq S
  have hceInt : Integrable cexp ν := integrable_condExp
  have hfloorInt := integrable_of_indicator_const rate rewards C_star C_h u t
    ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) hgateMeas
  have hgapOn : IntegrableOn gap Dut ν := hgapInt.integrableOn (s := Dut)
  have hceOn : IntegrableOn cexp Dut ν := hceInt.integrableOn (s := Dut)
  have hfloorOn : IntegrableOn
      (Gq.indicator (fun _ : Z => (p.m : ℝ) / (rate.eta.val * (D p : ℝ)))) Dut ν :=
    hfloorInt.integrableOn (s := Dut)
  have hbound :=
    ReferenceFirstCollectionRenewalNextLearningMoments.roundedRewardGap_le_condExp_add_floor
      rate rewards C_star C_h u t control0 hq S
  have hmono := setIntegral_mono_ae hgapOn (hceOn.add hfloorOn) hbound
  have hceEq : (∫ z in Dut, cexp z ∂ν) = ∫ z in Dut, obs z ∂ν :=
    setIntegral_condExp hfield hobsInt hDfield
  have hfloorEq := setIntegral_indicator_inter rate rewards C_star C_h u t Dut Gq
    ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) hDambient hgateMeas
  calc
    (∫ z in Dut, gap z ∂ν) ≤ ∫ z in Dut, (cexp z +
        Gq.indicator (fun _ : Z => (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ))) z) ∂ν := by
      simpa [gap, cexp, obs, Fq, Gq] using hmono
    _ = (∫ z in Dut, cexp z ∂ν) +
        ∫ z in Dut, Gq.indicator (fun _ : Z => (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ))) z ∂ν :=
      integral_add hceOn hfloorOn
    _ = (∫ z in Dut, obs z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (Dut ∩ Gq) := by
      rw [hceEq, hfloorEq]
    _ = _ := by rfl

/-- The natural next-date arrival selector has literal zero terminal mass. -/
theorem integral_naturalNextArrivalObservation_fixedID :
    0 ≤ ∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
          rate rewards C_star C_h u t z ∂ν ∧
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
          rate rewards C_star C_h u t z ∂ν) ≤
        (p.m : ℝ) * fixedIDNextGateMass rate rewards C_star C_h u t ids := by
  by_cases hq : t.val + 1 < p.T
  · simp only [fixedIDNextGateMass, dite_eq_left hq]
    have hlocal := integral_nextArrivalObservation_fixedID
      rate rewards C_star C_h u t control0 ids hq
    simpa [ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation, hq]
      using hlocal
  · simp only [fixedIDNextGateMass, dite_eq_right hq]
    rw [show ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
        rate rewards C_star C_h u t = fun _ => 0 by
      funext z
      simp [ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation, hq]]
    simp

/-- The natural next-date rounded-gap selector has zero terminal mass and
retains the exact same ID/gate intersection whenever that date exists. -/
theorem integral_naturalNextRoundedRewardGap_fixedID :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
        rate rewards C_star C_h u t S z ∂ν) ≤
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
          rate rewards C_star C_h u t S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
        fixedIDNextGateMass rate rewards C_star C_h u t ids := by
  by_cases hq : t.val + 1 < p.T
  · simp only [fixedIDNextGateMass, dite_eq_left hq]
    have hlocal := integral_nextRoundedRewardGap_fixedID
      rate rewards C_star C_h u t control0 ids S hq
    simpa [ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap,
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation, hq]
      using hlocal
  · simp only [fixedIDNextGateMass, dite_eq_right hq]
    rw [show ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
        rate rewards C_star C_h u t S = fun _ => 0 by
      funext z
      simp [ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap, hq],
      show ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
        rate rewards C_star C_h u t S = fun _ => 0 by
      funext z
      simp [ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation, hq]]
    simp

private theorem futureObservation_integrableOn (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    IntegrableOn
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservation
        rate rewards C_star C_h u t q hfuture) Dut ν :=
  (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservation
    rate rewards C_star C_h u t control0 q hfuture).integrableOn

private theorem futureComparator_integrableOn (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    IntegrableOn
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGap
        rate rewards C_star C_h u t q hfuture S) Dut ν :=
  (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGap
    rate rewards C_star C_h u t control0 q hfuture S).integrableOn

private theorem futureReward_integrableOn (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    IntegrableOn
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGap
        rate rewards C_star C_h u t q hfuture S) Dut ν :=
  (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureRewardComparatorGap
    rate rewards C_star C_h u t control0 q hfuture S).integrableOn

/-- A strict-future arrival integral localized before averaging IDs is
nonnegative and paid by the exact fixed-ID intersection with that date's
enabled prior-clear gate. -/
theorem integral_futureArrivalObservation_fixedID (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    0 ≤ ∫ z in Dut,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservation
          rate rewards C_star C_h u t q hfuture z ∂ν ∧
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservation
          rate rewards C_star C_h u t q hfuture z ∂ν) ≤
        (p.m : ℝ) * (ν).real (Dut ∩
          ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t q hfuture) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let obs := ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservation
    rate rewards C_star C_h u t q hfuture
  let cexp := ν[obs | Fq]
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hDfield := measurableSet_fixedIDRenewalSection_futurePriorField
    rate rewards C_star C_h u t control0 ids q hfuture
  have hDambient := fixedIDRenewalSection_measurable_ambient
    rate rewards C_star C_h u t ids
  have hG := futureGate_measurable rate rewards C_star C_h u t control0 q hfuture
  have hInt := ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservation
    rate rewards C_star C_h u t control0 q hfuture
  have hceInt : Integrable cexp ν := integrable_condExp
  have hbounds := ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservation_condExp_bounds
    rate rewards C_star C_h u t control0 q hfuture
  have hceEq : (∫ z in Dut, cexp z ∂ν) = ∫ z in Dut, obs z ∂ν :=
    setIntegral_condExp hfield hInt hDfield
  have hzeroOn : IntegrableOn (fun _ : Z => (0 : ℝ)) Dut ν :=
    (integrable_const (0 : ℝ)).integrableOn (s := Dut)
  have hceOn : IntegrableOn cexp Dut ν := hceInt.integrableOn (s := Dut)
  have hzero := setIntegral_mono_ae hzeroOn hceOn hbounds.1
  have hupperInt := integrable_of_indicator_const rate rewards C_star C_h u t
    (p.m : ℝ) hG
  have hupperOn : IntegrableOn (Gq.indicator (fun _ : Z => (p.m : ℝ))) Dut ν :=
    hupperInt.integrableOn (s := Dut)
  have hupperBound : cexp ≤ᵐ[ν] Gq.indicator (fun _ : Z => (p.m : ℝ)) := by
    filter_upwards [hbounds.2] with z hz
    by_cases hzG : z ∈ Gq
    · simpa [cexp, obs, Fq, Gq, Set.indicator, hzG] using hz
    · simpa [cexp, obs, Fq, Gq, Set.indicator, hzG] using hz
  have hupper := setIntegral_mono_ae hceOn hupperOn hupperBound
  have hgate := setIntegral_indicator_inter rate rewards C_star C_h u t Dut Gq
    (p.m : ℝ) hDambient hG
  refine ⟨?_, ?_⟩
  · rw [← hceEq]
    simpa using hzero
  · calc
      (∫ z in Dut, obs z ∂ν) = ∫ z in Dut, cexp z ∂ν := hceEq.symm
      _ ≤ ∫ z in Dut, Gq.indicator (fun _ : Z => (p.m : ℝ)) z ∂ν := by
        simpa [cexp, obs, Fq, Gq] using hupper
      _ = (p.m : ℝ) * (ν).real (Dut ∩ Gq) := hgate

/-- Strict-future reward-to-raw comparison localized on the same fixed-ID
section and the same date's retained gate. -/
theorem integral_futureRewardComparatorGap_fixedID (q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGap
        rate rewards C_star C_h u t q hfuture S z ∂ν) ≤
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGap
          rate rewards C_star C_h u t q hfuture S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (Dut ∩
          ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t q hfuture) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let obs := ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGap
    rate rewards C_star C_h u t q hfuture S
  let gap := ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGap
    rate rewards C_star C_h u t q hfuture S
  let cexp := ν[obs | Fq]
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hDfield := measurableSet_fixedIDRenewalSection_futurePriorField
    rate rewards C_star C_h u t control0 ids q hfuture
  have hDambient := fixedIDRenewalSection_measurable_ambient
    rate rewards C_star C_h u t ids
  have hGateAmbient := futureGate_measurable rate rewards C_star C_h u t control0 q hfuture
  have hgapInt := futureReward_integrableOn rate rewards C_star C_h u t control0 ids S q hfuture
  have hobsInt := ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGap
    rate rewards C_star C_h u t control0 q hfuture S
  have hceInt : Integrable cexp ν := integrable_condExp
  have hfloorInt := integrable_of_indicator_const rate rewards C_star C_h u t
    ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) hGateAmbient
  have hbound := ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGap_ae_le_condExp
    rate rewards C_star C_h u t control0 q hfuture S
  have hceOn : IntegrableOn cexp Dut ν := hceInt.integrableOn (s := Dut)
  have hfloorOn : IntegrableOn
      (Gq.indicator (fun _ : Z => (p.m : ℝ) / (rate.eta.val * (D p : ℝ)))) Dut ν :=
    hfloorInt.integrableOn (s := Dut)
  have hmono := setIntegral_mono_ae hgapInt (hceOn.add hfloorOn) hbound
  have hceEq : (∫ z in Dut, cexp z ∂ν) = ∫ z in Dut, obs z ∂ν :=
    setIntegral_condExp hfield hobsInt hDfield
  have hfloorEq := setIntegral_indicator_inter rate rewards C_star C_h u t Dut Gq
    ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) hDambient hGateAmbient
  calc
    (∫ z in Dut, gap z ∂ν) ≤ ∫ z in Dut, (cexp z +
        Gq.indicator (fun _ : Z => (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ))) z) ∂ν := by
      simpa [gap, cexp, obs, Fq, Gq] using hmono
    _ = (∫ z in Dut, cexp z ∂ν) +
        ∫ z in Dut, Gq.indicator (fun _ : Z => (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ))) z ∂ν :=
      integral_add hceOn hfloorOn
    _ = (∫ z in Dut, obs z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) * (ν).real (Dut ∩ Gq) := by
      rw [hceEq, hfloorEq]
    _ = _ := by rfl

omit ids in
private theorem futureArrivalObservationAt_integrable (n : ℕ) :
    Integrable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt
        rate rewards C_star C_h u t n) ν := by
  by_cases hn : n < p.T
  · by_cases hfuture : t.val + 1 < n
    · simpa [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
        hn, hfuture] using
        (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservation
          rate rewards C_star C_h u t control0 ⟨n, hn⟩ hfuture)
    · simp [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
        hn, hfuture]
  · simp [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt, hn]

omit ids in
private theorem futureArrivalComparatorGapAt_integrable (n : ℕ) :
    Integrable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt
        rate rewards C_star C_h u t n S) ν := by
  by_cases hn : n < p.T
  · by_cases hfuture : t.val + 1 < n
    · simpa [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt,
        hn, hfuture] using
        (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGap
          rate rewards C_star C_h u t control0 ⟨n, hn⟩ hfuture S)
    · simp [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt,
        hn, hfuture]
  · simp [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt, hn]

omit ids in
private theorem futureRewardComparatorGapAt_integrable (n : ℕ) :
    Integrable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt
        rate rewards C_star C_h u t n S) ν := by
  by_cases hn : n < p.T
  · by_cases hfuture : t.val + 1 < n
    · simpa [ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt,
        hn, hfuture] using
        (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureRewardComparatorGap
          rate rewards C_star C_h u t control0 ⟨n, hn⟩ hfuture S)
    · simp [ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt,
        hn, hfuture]
  · simp [ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt, hn]

private theorem integral_futureArrivalObservationTotal_fixedID_eq_sum :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
        rate rewards C_star C_h u t z ∂ν) =
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ∫ z in Dut,
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt
            rate rewards C_star C_h u t n z ∂ν := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
  simpa only [← Finset.sum_apply] using
    (integral_finsetSum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z =>
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt
          rate rewards C_star C_h u t n z)
      (fun n hn => (futureArrivalObservationAt_integrable
        rate rewards C_star C_h u t control0 n).integrableOn))

private theorem integral_futureArrivalComparatorGapTotal_fixedID_eq_sum :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
        rate rewards C_star C_h u t S z ∂ν) =
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ∫ z in Dut,
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt
            rate rewards C_star C_h u t n S z ∂ν := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
  simpa only [← Finset.sum_apply] using
    (integral_finsetSum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z =>
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt
          rate rewards C_star C_h u t n S z)
      (fun n hn => (futureArrivalComparatorGapAt_integrable
        rate rewards C_star C_h u t control0 S n).integrableOn))

private theorem integral_futureRewardComparatorGapTotal_fixedID_eq_sum :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
        rate rewards C_star C_h u t S z ∂ν) =
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ∫ z in Dut,
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt
            rate rewards C_star C_h u t n S z ∂ν := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
  simpa only [← Finset.sum_apply] using
    (integral_finsetSum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z =>
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt
          rate rewards C_star C_h u t n S z)
      (fun n hn => (futureRewardComparatorGapAt_integrable
        rate rewards C_star C_h u t control0 S n).integrableOn))

/-- The actual existing future-arrival total localizes over the exact sum of
its per-date fixed-ID prior-clear gate masses. -/
theorem integral_futureArrivalObservationTotal_fixedID :
    0 ≤ ∫ z in Dut,
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
        rate rewards C_star C_h u t z ∂ν ∧
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
          rate rewards C_star C_h u t z ∂ν) ≤
        (p.m : ℝ) * fixedIDFutureGateMass rate rewards C_star C_h u t ids := by
  rw [integral_futureArrivalObservationTotal_fixedID_eq_sum
    rate rewards C_star C_h u t control0 ids]
  refine ⟨?_, ?_⟩
  · apply Finset.sum_nonneg
    intro n hn
    rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
    have hfuture : t.val + 1 < n := by omega
    have hq : n < p.T := hhi
    simpa [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
      hhi, hfuture] using
      (integral_futureArrivalObservation_fixedID rate rewards C_star C_h u t control0 ids
        ⟨n, hhi⟩ hfuture).1
  · calc
      _ ≤ ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
          (p.m : ℝ) * fixedIDFutureGateMassAt rate rewards C_star C_h u t ids n := by
        apply Finset.sum_le_sum
        intro n hn
        rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
        have hfuture : t.val + 1 < n := by omega
        have hq : n < p.T := hhi
        simpa [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
          fixedIDFutureGateMassAt, hhi, hfuture] using
          (integral_futureArrivalObservation_fixedID rate rewards C_star C_h u t control0 ids
            ⟨n, hhi⟩ hfuture).2
      _ = (p.m : ℝ) * fixedIDFutureGateMass rate rewards C_star C_h u t ids := by
        simp only [fixedIDFutureGateMass]
        rw [Finset.mul_sum]

/-- The existing total strict-future reward comparison retains each date's
same-ID gate mass through finite summation. -/
theorem integral_futureRewardComparatorGapTotal_fixedID :
    (∫ z in Dut,
      ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
        rate rewards C_star C_h u t S z ∂ν) ≤
      (∫ z in Dut,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
          rate rewards C_star C_h u t S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          fixedIDFutureGateMass rate rewards C_star C_h u t ids := by
  rw [integral_futureRewardComparatorGapTotal_fixedID_eq_sum
      rate rewards C_star C_h u t control0 ids S,
    integral_futureArrivalComparatorGapTotal_fixedID_eq_sum
      rate rewards C_star C_h u t control0 ids S]
  calc
    _ ≤ ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ((∫ z in Dut,
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt
              rate rewards C_star C_h u t n S z ∂ν) +
          ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
            fixedIDFutureGateMassAt rate rewards C_star C_h u t ids n) := by
      apply Finset.sum_le_sum
      intro n hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hfuture : t.val + 1 < n := by omega
      have hq : n < p.T := hhi
      simpa [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt,
        fixedIDFutureGateMassAt, hhi, hfuture] using
        (integral_futureRewardComparatorGap_fixedID rate rewards C_star C_h u t control0 ids S
          ⟨n, hhi⟩ hfuture)
    _ = (∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
          ∫ z in Dut,
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt
              rate rewards C_star C_h u t n S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          fixedIDFutureGateMass rate rewards C_star C_h u t ids := by
      simp only [fixedIDFutureGateMass]
      rw [Finset.sum_add_distrib, Finset.mul_sum]

end Bandits.Support.ReferenceFirstCollectionRenewalFixedIDLearningMoments
