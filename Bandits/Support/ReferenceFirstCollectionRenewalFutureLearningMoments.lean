/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Bandits.Support.ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic
/-! # Actual strict-future first-renewal learning moments. Selectors use the actual enabled prior-clear cell on the original source law and retain every clipped strict-future date. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators Classical MeasureTheory
open Bandits.Support ConstructorDimensions
namespace Bandits.Support.ReferenceFirstCollectionRenewalFutureLearningMoments
open ReferenceFirstCollectionRenewalAuxiliaryLaw
open ReferenceFirstCollectionRenewalFutureControlLaw
open ReferenceFirstCollectionRenewalFutureExponentialIncrement
open ReferenceFirstCollectionRenewalFutureRetainedMoments
open ReferenceFirstCollectionRenewalFutureWeightedEnergyStep
open ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget
variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
  (C_star C_h : ℝ) (u t : Fin p.T)
local notation "Z" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalFutureControlLaw.Source
  rate rewards C_star C_h u t
local notation "ν" => _root_.Bandits.Support.ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
  rate rewards C_star C_h u t
/-- The actual supported sum of inclusion weight times raw future arrival. -/
def futureArrivalObservation (q : Fin p.T) (hfuture : t.val + 1 < q.val) : Z → ℝ :=
  (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture).indicator (fun z =>
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z)
/-- The actual supported raw-arrival comparator gap on the same future cell. -/
def futureArrivalComparatorGap (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) : Z → ℝ :=
  (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture).indicator (fun z =>
      (∑ j ∈ S.1, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) -
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z)
/-- The actual supported reward-to-raw comparator gap on the same calendar. -/
def futureRewardComparatorGap (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) : Z → ℝ :=
  (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture).indicator (fun z =>
      (∑ j ∈ S.1, ((rewards q j).val : ℝ) / (D p : ℝ)) -
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        (((rewards q j).val : ℝ) / (D p : ℝ)))
/-- The scalar natural-date arrival selector, zero outside the actual
strict-future calendar range. -/
def futureArrivalObservationAt (n : ℕ) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      futureArrivalObservation rate rewards C_star C_h u t ⟨n, hn⟩ hf
    else 0
  else 0
/-- The scalar natural-date raw comparator selector on the original calendar. -/
def futureArrivalComparatorGapAt (n : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      futureArrivalComparatorGap rate rewards C_star C_h u t ⟨n, hn⟩ hf S
    else 0
  else 0
/-- The scalar natural-date reward comparator selector on the same calendar. -/
def futureRewardComparatorGapAt (n : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) : Z → ℝ :=
  if hn : n < p.T then
    if hf : t.val + 1 < n then
      futureRewardComparatorGap rate rewards C_star C_h u t ⟨n, hn⟩ hf S
    else 0
  else 0
/-- The complete strict-future raw-arrival sum over the predecessor's literal
calendar interval. -/
def futureArrivalObservationTotal : Z → ℝ := fun z =>
  ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
    futureArrivalObservationAt rate rewards C_star C_h u t n z
/-- The complete strict-future raw comparator sum over the same interval. -/
def futureArrivalComparatorGapTotal (S : ProductSetLaw.ProductSet p.K p.m) : Z → ℝ :=
  fun z =>
    ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
      futureArrivalComparatorGapAt rate rewards C_star C_h u t n S z
/-- The complete strict-future reward comparator sum over the same interval. -/
def futureRewardComparatorGapTotal (S : ProductSetLaw.ProductSet p.K p.m) : Z → ℝ :=
  fun z =>
    ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
      futureRewardComparatorGapAt rate rewards C_star C_h u t n S z
private theorem integrable_of_measurable_norm_le_const {X : Type*}
    [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (c : ℝ)
    (hb : ∀ x, ‖f x‖ ≤ c) : Integrable f μ :=
  (integrable_const c).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
private theorem futureThetaMinus_integrable (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) (j : Fin p.K) :
    Integrable (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
      rate rewards C_star C_h u t q hfuture j) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hmeas := (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
    rate rewards C_star C_h u t control0 q hfuture j).mono hfield le_rfl
  exact integrable_of_measurable_norm_le_const _ hmeas 1 (by
    intro z
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
        rate rewards C_star C_h u t q hfuture j z).1]
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
      rate rewards C_star C_h u t q hfuture j z).2)
private theorem integrable_theta_mul_futureScalar (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) (j : Fin p.K) :
    Integrable (fun z =>
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) ν := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have htheta := (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
    rate rewards C_star C_h u t control0 q hfuture j).mono hfield le_rfl
  have hb (z : Z) : ‖ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
      rate rewards C_star C_h u t q hfuture j z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
        rate rewards C_star C_h u t q hfuture j z).1]
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
      rate rewards C_star C_h u t q hfuture j z).2
  exact (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
    rate rewards C_star C_h u t q hfuture control0 j).bdd_mul
      htheta.aestronglyMeasurable (Filter.Eventually.of_forall hb)
private theorem integrable_futureWeightedScalarSum
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Integrable (fun z => ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) ν := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum Finset.univ
      (f := fun j z =>
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z)
      (fun j hj => integrable_theta_mul_futureScalar
        rate rewards C_star C_h u t control0 q hfuture j))
private theorem integrable_futureScalarSetSum
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (fun z => ∑ j ∈ S.1,
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) ν := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum S.1
      (f := fun j z => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z)
      (fun j hj => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
        rate rewards C_star C_h u t q hfuture control0 j))
private theorem integrable_futureThetaRewardSum
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Integrable (fun z => ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      (((rewards q j).val : ℝ) / (D p : ℝ))) ν := by
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum Finset.univ
      (f := fun j z =>
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        (((rewards q j).val : ℝ) / (D p : ℝ)))
      (fun j hj => (futureThetaMinus_integrable rate rewards C_star C_h u t
        control0 q hfuture j).mul_const
          ((((rewards q j).val : ℝ) / (D p : ℝ)))))
private theorem measurable_futureLocalizedScalarLinear
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (c : Fin p.K → Z → ℝ)
    (hc : ∀ j, Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (c j)) :
    Measurable
      (fun z => ∑ j : Fin p.K, c j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) := by
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  apply Finset.measurable_sum
  intro j hj
  exact ((hc j).mono hfield le_rfl).mul
    (ReferenceFirstCollectionRenewalFutureRetainedMoments.measurable_futureScalar
      rate rewards C_star C_h u t q hfuture control0 j)
private theorem integrable_futureLocalizedScalarLinear
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (c : Fin p.K → Z → ℝ)
    (hc : ∀ j, Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (c j))
    (hcb : ∀ j z, ‖c j z‖ ≤ 1) :
    Integrable (fun z =>
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun z => ∑ j : Fin p.K, c j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z) ν := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hGq : MeasurableSet[Fq] Gq :=
    ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
      rate rewards C_star C_h u t q hfuture control0
  have hsum := measurable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture c hc
  have hGAmbient := hfield Gq hGq
  have hsumInt : Integrable (fun z => ∑ j : Fin p.K, c j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) ν := by
    simpa only [← Finset.sum_apply] using
      (integrable_finsetSum Finset.univ
        (f := fun j z => c j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z)
        (fun j hj => by
          have hcmeas := (hc j).mono hfield le_rfl
          exact (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
            rate rewards C_star C_h u t q hfuture control0 j).bdd_mul
              hcmeas.aestronglyMeasurable
              (Filter.Eventually.of_forall (hcb j))))
  change Integrable (Gq.indicator _) ν
  exact hsumInt.indicator hGAmbient
private theorem localizedScalarLinear_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (c : Fin p.K → Z → ℝ)
    (hc : ∀ j, Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q] (c j))
    (hcb : ∀ j z, ‖c j z‖ ≤ 1) :
    ν[(fun z =>
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun z => ∑ j : Fin p.K, c j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z =>
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (fun z => ∑ j : Fin p.K, c j z *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture j z) z := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let phi := fun j : Fin p.K => Gq.indicator (c j)
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hGq : MeasurableSet[Fq] Gq :=
    ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
      rate rewards C_star C_h u t q hfuture control0
  have hphi (j : Fin p.K) : Measurable[Fq] (phi j) :=
    (hc j).indicator hGq
  have hphiAmbient (j : Fin p.K) :
      Measurable[Subtype.instMeasurableSpace] (phi j) :=
    (hphi j).mono hfield le_rfl
  have hphiBound (j : Fin p.K) : ∀ᵐ z ∂ν, ‖phi j z‖ ≤ 1 :=
    Filter.Eventually.of_forall fun z => by
      by_cases hz : z ∈ Gq
      · simpa [phi, Set.indicator_of_mem hz] using hcb j z
      · simp [phi, Set.indicator_of_notMem hz]
  have htermInt (j : Fin p.K) : Integrable (fun z => phi j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) ν :=
    (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
      rate rewards C_star C_h u t q hfuture control0 j).bdd_mul
      (hphiAmbient j).stronglyMeasurable.aestronglyMeasurable (hphiBound j)
  have hsumInt : Integrable (fun z => ∑ j : Fin p.K, phi j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) ν := by
    simpa only [← Finset.sum_apply] using
      (integrable_finsetSum Finset.univ
        (f := fun j z => phi j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z)
        (fun j hj => htermInt j))
  have hshape : (fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
        c j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) z) =
      fun z => ∑ j : Fin p.K, phi j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z := by
    funext z
    by_cases hz : z ∈ Gq
    · simp [phi, Set.indicator_of_mem hz]
    · simp [phi, Set.indicator_of_notMem hz]
  have hsumCE := condExp_finsetSum
    (μ := ν) (s := Finset.univ)
    (f := fun j z => phi j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z)
    (fun j hj => htermInt j) Fq
  have hce (j : Fin p.K) :
      ν[(fun z => phi j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) | Fq] =ᵐ[ν]
      fun z => phi j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z := by
    have hpull := condExp_mul_of_stronglyMeasurable_left
      (hphi j).stronglyMeasurable (htermInt j)
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_integrable
        rate rewards C_star C_h u t q hfuture control0 j)
    have hmoment := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_condExp
      rate rewards C_star C_h u t q hfuture control0 j
    filter_upwards [hpull, hmoment] with z h₁ h₂
    change ν[phi j * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture j | Fq] z =
      phi j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z
    rw [h₁]
    change phi j z * ν[(fun w => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture j w) | Fq] z =
      phi j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z
    have h₂' := h₂
    change ν[(fun w => ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
      rate rewards C_star C_h u t q hfuture j w) | Fq] z =
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z at h₂'
    rw [h₂']
  have hall : ∀ᵐ z ∂ν, ∀ j : Fin p.K,
      ν[(fun w => phi j w * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j w) | Fq] z =
      phi j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z :=
    ae_all_iff.2 hce
  have htarget : (fun z => ∑ j : Fin p.K, phi j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z) =
      fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
        c j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
          rate rewards C_star C_h u t q hfuture j z) z := by
    funext z
    by_cases hz : z ∈ Gq
    · simp [phi, Set.indicator_of_mem hz]
    · simp [phi, Set.indicator_of_notMem hz]
  have hsumCE' : ν[(fun z => ∑ j : Fin p.K, phi j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) | Fq] =ᵐ[ν]
      fun z => ∑ j : Fin p.K,
        ν[(fun w => phi j w * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j w) | Fq] z := by
    calc
      _ =ᵐ[ν] ν[(∑ j : Fin p.K, fun z => phi j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) | Fq] := by
            apply condExp_congr_ae
            filter_upwards [] with z
            simp only [Finset.sum_apply]
      _ =ᵐ[ν] fun z => ∑ j : Fin p.K,
          ν[(fun w => phi j w * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j w) | Fq] z := by
            filter_upwards [hsumCE] with z hz
            simpa only [Finset.sum_apply] using hz
  calc
    _ =ᵐ[ν] ν[(fun z => ∑ j : Fin p.K, phi j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) | Fq] := by
          exact condExp_congr_ae (Filter.Eventually.of_forall fun z => congrFun hshape z)
    _ =ᵐ[ν] fun z => ∑ j : Fin p.K,
        ν[(fun w => phi j w * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j w) | Fq] z := by
          exact hsumCE'
    _ =ᵐ[ν] fun z => ∑ j : Fin p.K, phi j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
          rate rewards C_star C_h u t q hfuture j z := by
          filter_upwards [hall] with z hz
          exact Finset.sum_congr rfl (fun j hj => hz j)
    _ =ᵐ[ν] fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
        c j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
          rate rewards C_star C_h u t q hfuture j z) z :=
          Filter.Eventually.of_forall fun z => congrFun htarget z
private theorem measurableSet_futureGate_field
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    MeasurableSet[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q]
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture) :=
  ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
private theorem futureGate_subset_support
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
      rate rewards C_star C_h u t q hfuture ⊆
    ReferenceFirstCollectionRenewalFutureExponentialQueueStep.futureQueueSupport
      rate rewards C_star C_h u t q hfuture :=
  ReferenceFirstCollectionRenewalFutureExponentialQueueStep.Gfuture_subset_futureQueueSupport
    rate rewards C_star C_h u t q hfuture
/-- On the actual gate, the whole-prefix run and future cell coexist; the scalar is its accepted raw estimate and the successor keeps the first detecting update and record. -/
theorem future_learning_moment_present_run
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) (z : Z)
    (hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
      rate rewards C_star C_h u t q hfuture) :
    ∃ inputs : List (RecordedQueueRun.RoundInput p.K),
    ∃ c : RecordedQueueRun.RoundInput p.K,
      ReferenceFirstCollectionRenewalFutureRetainedMoments.prefixInputs
        rate rewards C_star C_h u t q z = some inputs ∧
      ReferenceFirstCollectionRenewalFutureFirstReplacementView.futureCell
        rate rewards C_star C_h u t z q hfuture = some c ∧
      ReferenceFirstCollectionRenewalFutureRetainedMoments.priorReadout
        rate rewards C_star C_h u t q z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs)) ∧
      ReferenceFirstCollectionRenewalFutureNumericalPrefix.futurePrefixReadout
        rate rewards C_star C_h u t (q.val + 1) z =
        some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) c)) ∧
      (∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z =
        RecordedRoundMoments.rawEstimate
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) c j) ∧
      (∀ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z =
            ((RecordedQueueRun.acceptedArrival
              (RecordedQueueRun.acceptedRecord
                (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (RecordedQueueRun.run
                  (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) c j) : ℝ) /
              ((ReferenceFirstLaunchNumericalCell.queueParameters rate).n : ℝ)) ∧
        (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) c).records j =
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs).records j ++
            [RecordedQueueRun.acceptedRecord
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (RecordedQueueRun.run
                (ReferenceFirstLaunchNumericalCell.queueParameters rate) inputs) c j]) := by
  have hs := futureGate_subset_support rate rewards C_star C_h u t q hfuture hz
  obtain ⟨inputs, c, hinputs, hcell, hprior, hnext, _, _, _, _, _⟩ :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureReadouts_same_run_step
      rate rewards C_star C_h u t q hfuture z hs
  refine ⟨inputs, c, hinputs, hcell, hprior, hnext, ?_, ?_⟩
  · intro j
    exact ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_run
      rate rewards C_star C_h u t q hfuture j z inputs c hinputs hcell
  · intro j
    have ha := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_present_acceptance
      rate rewards C_star C_h u t q hfuture j z inputs c hinputs hcell
    exact ⟨ha.1, ha.2.2⟩
private theorem futureMomentOne_nonneg_le_one
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (control0 : ContinuousLearningRows.TimeControl p) (j : Fin p.K) (z : Z) :
    0 ≤ ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
      rate rewards C_star C_h u t q hfuture j z ∧
    ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
      rate rewards C_star C_h u t q hfuture j z ≤ 1 := by
  exact ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne_bounds
    rate rewards C_star C_h u t q hfuture control0 j z
/-- Borel measurability of the actual localized weighted arrival scalar. -/
theorem measurable_futureArrivalObservation
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (futureArrivalObservation rate rewards C_star C_h u t q hfuture) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hsum := measurable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
      rate rewards C_star C_h u t q hfuture j)
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j)
  have hG := hfield _ (measurableSet_futureGate_field rate rewards C_star C_h u t
    control0 q hfuture)
  exact hsum.indicator hG
/-- Borel measurability of the actual localized raw comparator scalar. -/
theorem measurable_futureArrivalComparatorGap
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  let c := fun j : Fin p.K => fun _ : Z => if j ∈ S.1 then (1 : ℝ) else 0
  have hc (j : Fin p.K) : Measurable[Fq] (c j) := measurable_const
  have hsel := measurable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture c hc
  have htheta := measurable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
      rate rewards C_star C_h u t q hfuture j)
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j)
  have hG := hfield _ (measurableSet_futureGate_field rate rewards C_star C_h u t
    control0 q hfuture)
  have hselEq : (fun z => ∑ j : Fin p.K, c j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) =
      fun z => ∑ j ∈ S.1, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z := by
    funext z
    simp [c, Finset.sum_ite_mem]
  have hdiff := hsel.sub htheta
  convert hdiff.indicator hG using 1
  funext z
  by_cases hz : z ∈ Gq
  · have hz' : z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture := hz
    simp only [futureArrivalComparatorGap, Set.indicator_of_mem hz']
    rw [← congrFun hselEq z]
    rfl
  · have hz' : z ∉ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture := hz
    simp only [futureArrivalComparatorGap, Set.indicator_of_notMem hz']
/-- Borel measurability of the actual localized reward comparator scalar. -/
theorem measurable_futureRewardComparatorGap
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Measurable (futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have htheta := measurable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
      rate rewards C_star C_h u t q hfuture j)
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j)
  have hthetaReward : Measurable[Fq] (fun z => ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      (((rewards q j).val : ℝ) / (D p : ℝ))) := by
    apply Finset.measurable_sum
    intro j hj
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j).mul measurable_const
  have hselReward : Measurable[Fq] (fun _ : Z =>
      ∑ j ∈ S.1, ((rewards q j).val : ℝ) / (D p : ℝ)) := measurable_const
  have hG := hfield _ (measurableSet_futureGate_field rate rewards C_star C_h u t
    control0 q hfuture)
  have hdiff := (hselReward.mono hfield le_rfl).sub (hthetaReward.mono hfield le_rfl)
  exact hdiff.indicator hG
/-- Integrability of the supported weighted arrival observation. -/
theorem integrable_futureArrivalObservation
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Integrable (futureArrivalObservation rate rewards C_star C_h u t q hfuture) ν := by
  have hsum := integrable_futureWeightedScalarSum rate rewards C_star C_h u t
    control0 q hfuture
  have hG := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  change Integrable ((ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture).indicator _) ν
  exact hsum.indicator (hfield _ hG)
/-- Integrability of the supported raw comparator gap. -/
theorem integrable_futureArrivalComparatorGap
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) ν := by
  let c := fun j : Fin p.K => fun _ : Z => if j ∈ S.1 then (1 : ℝ) else 0
  have hc (j : Fin p.K) : Measurable[
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] (c j) := measurable_const
  have hsel := integrable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture c hc (fun j z => by
      simp [c]
      split_ifs <;> norm_num)
  have htheta := integrable_futureWeightedScalarSum rate rewards C_star C_h u t
    control0 q hfuture
  have hshape : futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S =
      fun z =>
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (fun z => ∑ j : Fin p.K, c j z *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
              rate rewards C_star C_h u t q hfuture j z) z -
        futureArrivalObservation rate rewards C_star C_h u t q hfuture z := by
    funext z
    by_cases hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture
    · simp [futureArrivalComparatorGap, futureArrivalObservation, c, hz,
        Finset.sum_ite_mem]
    · simp [futureArrivalComparatorGap, futureArrivalObservation, c, hz]
  rw [hshape]
  exact hsel.sub (integrable_futureArrivalObservation rate rewards C_star C_h u t
    control0 q hfuture)
/-- Integrability of the supported reward comparator gap. -/
theorem integrable_futureRewardComparatorGap
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S) ν := by
  have hsel : Integrable (fun _ : Z => ∑ j ∈ S.1,
      ((rewards q j).val : ℝ) / (D p : ℝ)) ν := integrable_const _
  have htheta := integrable_futureThetaRewardSum rate rewards C_star C_h u t
    control0 q hfuture
  have hG := ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
    rate rewards C_star C_h u t q hfuture control0
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hselG : Integrable (fun z =>
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun _ : Z => ∑ j ∈ S.1, ((rewards q j).val : ℝ) / (D p : ℝ)) z) ν :=
    hsel.indicator (hfield _ hG)
  have hthetaG : Integrable (fun z =>
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          (((rewards q j).val : ℝ) / (D p : ℝ))) z) ν :=
    htheta.indicator (hfield _ hG)
  have hshape : futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S =
      fun z =>
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (fun _ : Z => ∑ j ∈ S.1, ((rewards q j).val : ℝ) / (D p : ℝ)) z -
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (fun z => ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
              rate rewards C_star C_h u t q hfuture j z *
            (((rewards q j).val : ℝ) / (D p : ℝ))) z := by
    funext z
    by_cases hz : z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture <;>
      simp [futureRewardComparatorGap, hz]
  rw [hshape]
  exact hselG.sub hthetaG
/-- Borel measurability of the conditional first-moment expression. -/
theorem measurable_futureArrivalConditionalMoment
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Measurable (fun z =>
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
            rate rewards C_star C_h u t q hfuture j z) z) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hsum : Measurable[Fq] (fun z => ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z) := by
    apply Finset.measurable_sum
    intro j hj
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j).mul
        (ReferenceFirstCollectionRenewalFutureRetainedMoments.measurable_futureMomentOne
          rate rewards C_star C_h u t q hfuture control0 j)
  have hG := hfield _ (measurableSet_futureGate_field rate rewards C_star C_h u t
    control0 q hfuture)
  have hsumAmbient := hsum.mono hfield le_rfl
  exact hsumAmbient.indicator hG
/-- The exact conditional first-moment identity for the actual supported
weighted arrival. -/
theorem futureArrivalObservation_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    ν[(futureArrivalObservation rate rewards C_star C_h u t q hfuture) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z =>
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (fun z => ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
              rate rewards C_star C_h u t q hfuture j z *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture j z) z := by
  have htheta (j : Fin p.K) :
      Measurable[ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q]
        (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j) :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j
  have hthetaBound (j : Fin p.K) (z : Z) :
      ‖ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
        rate rewards C_star C_h u t q hfuture j z).1]
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
      rate rewards C_star C_h u t q hfuture j z).2
  simpa only [futureArrivalObservation] using
    (localizedScalarLinear_condExp rate rewards C_star C_h u t control0 q hfuture
      (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j) htheta hthetaBound)
/-- The actual conditional first-moment expression is integrable under the
original finite, possibly-zero source law. -/
theorem integrable_futureArrivalConditionalMoment
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    Integrable (fun z =>
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
            rate rewards C_star C_h u t q hfuture j z) z) ν := by
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hmeas := measurable_futureArrivalConditionalMoment rate rewards C_star C_h u t
    control0 q hfuture
  have hbound (z : Z) : ‖Gq.indicator (fun z => ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z) z‖ ≤ (p.K : ℝ) := by
    by_cases hz : z ∈ Gq
    · simp only [Set.indicator_of_mem hz, Real.norm_eq_abs]
      have hsumabs : |∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
            rate rewards C_star C_h u t q hfuture j z| ≤
          ∑ _j : Fin p.K, (1 : ℝ) := by
        calc
          _ ≤ ∑ j : Fin p.K,
              |ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
                rate rewards C_star C_h u t q hfuture j z *
              ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
                rate rewards C_star C_h u t q hfuture j z| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin p.K, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul]
            have hθ := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
              rate rewards C_star C_h u t q hfuture j z
            have hm := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne_bounds
              rate rewards C_star C_h u t q hfuture control0 j z
            have hθabs : |ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
                rate rewards C_star C_h u t q hfuture j z| ≤ 1 := by
              rw [abs_of_nonneg hθ.1]
              exact hθ.2
            have hmabs : |ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
                rate rewards C_star C_h u t q hfuture j z| ≤ 1 := by
              rw [abs_of_nonneg hm.1]
              exact hm.2
            exact (mul_le_of_le_one_right (abs_nonneg _) hmabs).trans hθabs
      simpa using hsumabs
    · simp [Gq, hz]
  exact integrable_of_measurable_norm_le_const _ hmeas (p.K : ℝ) hbound
/-- The conditional arrival expression has the actual gatewise mass `m`,
proved from the retained run's register marginals. -/
theorem futureArrivalObservation_condExp_bounds
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    0 ≤ᵐ[ν] ν[(futureArrivalObservation rate rewards C_star C_h u t q hfuture) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] ∧
    ν[(futureArrivalObservation rate rewards C_star C_h u t q hfuture) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] ≤ᵐ[ν]
      fun z => (p.m : ℝ) *
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator (fun _ => 1) z := by
  have hid := futureArrivalObservation_condExp rate rewards C_star C_h u t
    control0 q hfuture
  have hpoint (z : Z) : 0 ≤
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
          (fun z => ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
              rate rewards C_star C_h u t q hfuture j z *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture j z) z ∧
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
          (fun z => ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
              rate rewards C_star C_h u t q hfuture j z *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture j z) z ≤
        (p.m : ℝ) *
          (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t q hfuture).indicator (fun _ => 1) z := by
    let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
      rate rewards C_star C_h u t q hfuture
    by_cases hz : z ∈ Gq
    · have hsupp := futureGate_subset_support rate rewards C_star C_h u t q hfuture hz
      have htheta := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_sum_eq_m
        rate rewards C_star C_h u t q hfuture z hsupp
      change 0 ≤ Gq.indicator (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
            rate rewards C_star C_h u t q hfuture j z) z ∧
        Gq.indicator (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
            rate rewards C_star C_h u t q hfuture j z) z ≤
          (p.m : ℝ) * Gq.indicator (fun _ => 1) z
      simp only [Set.indicator_of_mem hz]
      constructor
      · exact Finset.sum_nonneg fun j hj => mul_nonneg
          (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
            rate rewards C_star C_h u t q hfuture j z).1
          (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne_bounds
            rate rewards C_star C_h u t q hfuture control0 j z).1
      · calc
          _ ≤ ∑ j : Fin p.K,
              ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
                rate rewards C_star C_h u t q hfuture j z := by
              apply Finset.sum_le_sum
              intro j hj
              exact mul_le_of_le_one_right
                (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
                  rate rewards C_star C_h u t q hfuture j z).1
                (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne_bounds
                  rate rewards C_star C_h u t q hfuture control0 j z).2
          _ = (p.m : ℝ) := htheta
          _ = (p.m : ℝ) * 1 := by ring
    · change 0 ≤ Gq.indicator _ z ∧ Gq.indicator _ z ≤ (p.m : ℝ) * Gq.indicator _ z
      simp [Set.indicator_of_notMem hz]
  constructor
  · filter_upwards [hid] with z hz
    rw [hz]
    exact (hpoint z).1
  · filter_upwards [hid] with z hz
    rw [hz]
    exact (hpoint z).2
/-- The integrated actual-arrival budget for one strict-future date. -/
theorem integral_futureArrivalObservation_le
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    (∫ z, futureArrivalObservation rate rewards C_star C_h u t q hfuture z ∂ν) ≤
      (p.m : ℝ) * ((ν).real
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture)) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  have hG := hfield _ (measurableSet_futureGate_field rate rewards C_star C_h u t
    control0 q hfuture)
  have hb := futureArrivalObservation_condExp_bounds rate rewards C_star C_h u t
    control0 q hfuture
  have hleft := integrable_condExp
    (f := futureArrivalObservation rate rewards C_star C_h u t q hfuture)
    (μ := ν) (m := Fq)
  have hright : Integrable (fun z => (p.m : ℝ) * Gq.indicator (fun _ => 1) z) ν := by
    exact (integrable_const (p.m : ℝ)).mul_bdd (c := 1)
      (by fun_prop)
      (Filter.Eventually.of_forall fun z => by
        by_cases hz : z ∈ Gq
        · simp [Set.indicator_of_mem hz]
        · simp [Set.indicator_of_notMem hz])
  have hmono := integral_mono_ae hleft hright hb.2
  rw [integral_condExp hfield] at hmono
  rw [integral_const_mul, integral_indicator_const _ hG, smul_eq_mul] at hmono
  simpa [Gq, mul_comm] using hmono
/-- The actual one-date weighted arrival has nonnegative integral, including
null and absent supported branches. -/
theorem integral_futureArrivalObservation_nonneg
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val) :
    0 ≤ ∫ z, futureArrivalObservation rate rewards C_star C_h u t q hfuture z ∂ν := by
  apply integral_nonneg
  intro z
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  by_cases hz : z ∈ Gq
  · change 0 ≤ Gq.indicator (fun z => ∑ j : Fin p.K,
      ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z *
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) z
    rw [Set.indicator_of_mem hz]
    exact Finset.sum_nonneg fun j hj => mul_nonneg
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
        rate rewards C_star C_h u t q hfuture j z).1
      (ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar_bounds
        rate rewards C_star C_h u t q hfuture control0 j z).1
  · change 0 ≤ Gq.indicator _ z
    rw [Set.indicator_of_notMem hz]
/-- The conditional expectation of the comparator's actual raw-arrival gap
uses the retained first moments on this same supported cell. -/
theorem futureArrivalComparatorGap_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    ν[(futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] =ᵐ[ν]
      fun z =>
        (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
          rate rewards C_star C_h u t q hfuture).indicator
          (fun z =>
            (∑ j ∈ S.1, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture j z) -
            ∑ j : Fin p.K,
              ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
                rate rewards C_star C_h u t q hfuture j z *
              ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
                rate rewards C_star C_h u t q hfuture j z) z := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let cS := fun j : Fin p.K => fun _ : Z => if j ∈ S.1 then (1 : ℝ) else 0
  have hcS (j : Fin p.K) : Measurable[Fq] (cS j) := measurable_const
  have hcSbound (j : Fin p.K) (z : Z) : ‖cS j z‖ ≤ 1 := by
    simp [cS]
    split_ifs <;> norm_num
  have hsel := localizedScalarLinear_condExp rate rewards C_star C_h u t
    control0 q hfuture cS hcS hcSbound
  have htheta (j : Fin p.K) : Measurable[Fq]
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j) :=
    ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.measurable_futureThetaMinus
      rate rewards C_star C_h u t control0 q hfuture j
  have hthetaBound (j : Fin p.K) (z : Z) :
      ‖ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
        rate rewards C_star C_h u t q hfuture j z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
        rate rewards C_star C_h u t q hfuture j z).1]
    exact (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
      rate rewards C_star C_h u t q hfuture j z).2
  have hthetaCE := localizedScalarLinear_condExp rate rewards C_star C_h u t
    control0 q hfuture
    (fun j => ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
      rate rewards C_star C_h u t q hfuture j) htheta hthetaBound
  have hselInt := integrable_futureLocalizedScalarLinear rate rewards C_star C_h u t
    control0 q hfuture cS hcS hcSbound
  have hthetaInt := integrable_futureArrivalObservation rate rewards C_star C_h u t
    control0 q hfuture
  have hselShape : Gq.indicator (fun z => ∑ j ∈ S.1,
      ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) =
      fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
        cS j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) z := by
    funext z
    by_cases hz : z ∈ Gq
    · simp [cS, Set.indicator_of_mem hz, Finset.sum_ite_mem]
    · simp [cS, Set.indicator_of_notMem hz]
  have hDshape : futureArrivalComparatorGap rate rewards C_star C_h u t
      q hfuture S = fun z =>
        Gq.indicator (fun z => ∑ j ∈ S.1,
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z -
        futureArrivalObservation rate rewards C_star C_h u t q hfuture z := by
    funext z
    change Gq.indicator (fun z =>
      (∑ j ∈ S.1, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) -
      ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) z =
      Gq.indicator (fun z => ∑ j ∈ S.1,
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) z -
      Gq.indicator (fun z => ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) z
    by_cases hz : z ∈ Gq
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz]
      ring
  have hsubCE := condExp_sub hselInt hthetaInt Fq
  have hselShape' : (fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
      cS j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
        rate rewards C_star C_h u t q hfuture j z) z) =
      Gq.indicator (fun z => ∑ j ∈ S.1,
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) := by
    funext z
    by_cases hz : z ∈ Gq
    · simp [cS, Set.indicator_of_mem hz, Finset.sum_ite_mem]
    · simp [cS, Set.indicator_of_notMem hz]
  have hselMomentShape : (fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
      cS j z * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
        rate rewards C_star C_h u t q hfuture j z) z) =
      fun z => Gq.indicator (fun z => ∑ j ∈ S.1,
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
          rate rewards C_star C_h u t q hfuture j z) z := by
    funext z
    by_cases hz : z ∈ Gq
    · simp [cS, Set.indicator_of_mem hz, Finset.sum_ite_mem]
    · simp [cS, Set.indicator_of_notMem hz]
  have hthetaScalarShape : futureArrivalObservation rate rewards C_star C_h u t
      q hfuture = fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
        ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
          rate rewards C_star C_h u t q hfuture j z *
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
          rate rewards C_star C_h u t q hfuture j z) z := rfl
  calc
    _ =ᵐ[ν] ν[(fun z =>
        Gq.indicator (fun z => ∑ j : Fin p.K, cS j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z -
        Gq.indicator (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z) | Fq] := by
          exact condExp_congr_ae (Filter.Eventually.of_forall fun z => by
            rw [hDshape, hselShape, hthetaScalarShape])
    _ =ᵐ[ν] ν[(fun z => Gq.indicator (fun z => ∑ j : Fin p.K, cS j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z) | Fq] -
          ν[(fun z => Gq.indicator (fun z => ∑ j : Fin p.K,
          ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
            rate rewards C_star C_h u t q hfuture j z *
          ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
            rate rewards C_star C_h u t q hfuture j z) z) | Fq] := hsubCE
    _ =ᵐ[ν] fun z => Gq.indicator (fun z =>
          (∑ j ∈ S.1, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
            rate rewards C_star C_h u t q hfuture j z) -
          ∑ j : Fin p.K,
            ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
              rate rewards C_star C_h u t q hfuture j z *
            ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
              rate rewards C_star C_h u t q hfuture j z) z := by
          filter_upwards [hsel, hthetaCE] with z hsel' htheta'
          change (ν[fun w => Gq.indicator (fun w => ∑ j : Fin p.K,
              cS j w * ReferenceFirstCollectionRenewalFutureRetainedMoments.futureScalar
                rate rewards C_star C_h u t q hfuture j w) w | Fq] z) -
              ν[futureArrivalObservation rate rewards C_star C_h u t q hfuture | Fq] z =
            (Gq.indicator (fun w =>
              (∑ j ∈ S.1, ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
                rate rewards C_star C_h u t q hfuture j w) -
              ∑ j : Fin p.K,
                ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
                  rate rewards C_star C_h u t q hfuture j w *
                ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
                  rate rewards C_star C_h u t q hfuture j w) z)
          rw [hsel', hthetaScalarShape, htheta']
          by_cases hz : z ∈ Gq
          · have hzG : z ∈ ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
                rate rewards C_star C_h u t q hfuture := hz
            have hselM := congrFun hselMomentShape z
            simp only [Set.indicator_of_mem hz] at hselM
            simp only [Set.indicator_of_mem hzG]
            rw [hselM]
            simp [Gq, hz]
          · simp [Gq, hz]
/-- The rounded comparator transfer holds on the supported cell with the floor loss for the comparator's actual finite set of `m` arms. -/
theorem futureRewardComparatorGap_ae_le_condExp
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S ≤ᵐ[ν]
      ν[(futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) |
        ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
          rate rewards C_star C_h u t control0 q] +
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture).indicator
        (fun _ => (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ))) := by
  let Fq := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
    rate rewards C_star C_h u t control0 q
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  let theta := ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus
    rate rewards C_star C_h u t q hfuture
  let moment := ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMomentOne
    rate rewards C_star C_h u t q hfuture
  let reward := fun j : Fin p.K => ((rewards q j).val : ℝ) / (D p : ℝ)
  have hCE := futureArrivalComparatorGap_condExp rate rewards C_star C_h u t
    control0 q hfuture S
  have hden : 0 < rate.eta.val * (D p : ℝ) := by
    exact mul_pos rate.eta.property (by exact_mod_cast D_pos p)
  have hcard : S.1.card = p.m := (Finset.mem_powersetCard.mp S.2).2
  have hpoint : futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S ≤ᵐ[ν]
      ν[(futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) | Fq] +
        (fun z => Gq.indicator (fun _ => (p.m : ℝ) /
          (rate.eta.val * (D p : ℝ))) z) := by
    filter_upwards [hCE] with z hce
    by_cases hz : z ∈ Gq
    · have hzGate : z ∈ Gq := hz
      rcases hz with ⟨xi, hparams, hclear⟩
      have hxi_one (j : Fin p.K) : xi j ≤ 1 := by
        have hbound := ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient_bounds
          rate rewards C_star C_h u t (some (some j)) z q hfuture
        simpa [ReferenceFirstCollectionRenewalFutureRecordingLaw.futureCoefficient,
          hparams, ReferenceFirstCollectionRenewalNextRecordingLaw.coefficientOfParameters] using
          hbound.2
      have hsumxi : (∑ j ∈ S.1, xi j) ≤ (p.m : ℝ) := by
        calc
          (∑ j ∈ S.1, xi j) ≤ ∑ j ∈ S.1, (1 : ℝ) :=
            Finset.sum_le_sum fun j hj => hxi_one j
          _ = (p.m : ℝ) := by simp [hcard]
      have hret (j : Fin p.K) :=
        ReferenceFirstCollectionRenewalFutureRetainedMoments.futureMoments_retained_bounds
          rate rewards C_star C_h u t q hfuture control0 j z xi hparams hclear
      have hdelta (j : Fin p.K) :
          0 ≤ reward j - moment j z ∧
          reward j - moment j z ≤ xi j /
            (rate.eta.val * (D p : ℝ)) := by
        constructor
        · exact sub_nonneg.mpr (hret j).2.1
        · have hretlow : reward j - xi j /
              (rate.eta.val * (D p : ℝ)) ≤ moment j z := by
            have hQeta : (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta =
                rate.eta.val := rfl
            have hQD : (ReferenceFirstLaunchNumericalCell.queueParameters rate).D = D p := rfl
            simpa [hQeta, hQD, reward, moment] using (hret j).1
          linarith [hretlow]
      have hthetaNonneg (j : Fin p.K) : 0 ≤ theta j z :=
        (ReferenceFirstCollectionRenewalFutureWeightedEnergyStep.futureThetaMinus_bounds
          rate rewards C_star C_h u t q hfuture j z).1
      have hthetaDelta : 0 ≤ ∑ j : Fin p.K, theta j z * (reward j - moment j z) :=
        Finset.sum_nonneg fun j hj => mul_nonneg (hthetaNonneg j) (hdelta j).1
      have hround : (∑ j ∈ S.1, (reward j - moment j z)) ≤
          (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
        calc
          (∑ j ∈ S.1, (reward j - moment j z)) ≤
              ∑ j ∈ S.1, (xi j / (rate.eta.val * (D p : ℝ))) :=
            Finset.sum_le_sum fun j hj => hdelta j |>.2
          _ = (∑ j ∈ S.1, xi j) / (rate.eta.val * (D p : ℝ)) := by
            rw [Finset.sum_div]
          _ ≤ _ := (div_le_div_of_nonneg_right hsumxi hden.le)
      have hSdecomp : (∑ j ∈ S.1, reward j) =
          (∑ j ∈ S.1, moment j z) + ∑ j ∈ S.1, (reward j - moment j z) := by
        calc
          _ = ∑ j ∈ S.1, (moment j z + (reward j - moment j z)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by rw [Finset.sum_add_distrib]
      have hthetaDecomp : (∑ j : Fin p.K, theta j z * reward j) =
          (∑ j : Fin p.K, theta j z * moment j z) +
            ∑ j : Fin p.K, theta j z * (reward j - moment j z) := by
        calc
          _ = ∑ j : Fin p.K,
              (theta j z * moment j z + theta j z * (reward j - moment j z)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by rw [Finset.sum_add_distrib]
      have hgap : (∑ j ∈ S.1, reward j) - ∑ j : Fin p.K, theta j z * reward j =
          ((∑ j ∈ S.1, moment j z) - ∑ j : Fin p.K, theta j z * moment j z) +
            ((∑ j ∈ S.1, (reward j - moment j z)) -
              ∑ j : Fin p.K, theta j z * (reward j - moment j z)) := by
        rw [hSdecomp, hthetaDecomp]
        ring_nf
      have hlocal :
          (∑ j ∈ S.1, reward j) - ∑ j : Fin p.K, theta j z * reward j ≤
            ((∑ j ∈ S.1, moment j z) -
              ∑ j : Fin p.K, theta j z * moment j z) +
              (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
        rw [hgap]
        linarith
      have hCEval : ν[(futureArrivalComparatorGap rate rewards C_star C_h u t
          q hfuture S) | Fq] z =
          (∑ j ∈ S.1, moment j z) -
            ∑ j : Fin p.K, theta j z * moment j z := by
        rw [hce]
        simp [Gq, hzGate, theta, moment]
      change Gq.indicator (fun z =>
        (∑ j ∈ S.1, reward j) - ∑ j : Fin p.K, theta j z * reward j) z ≤
        ν[(futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) | Fq] z +
          Gq.indicator (fun _ => (p.m : ℝ) /
            (rate.eta.val * (D p : ℝ))) z
      rw [Set.indicator_of_mem hzGate, Set.indicator_of_mem hzGate, hCEval]
      exact hlocal
    · change Gq.indicator _ z ≤
        ν[(futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) | Fq] z +
          Gq.indicator (fun _ => (p.m : ℝ) /
            (rate.eta.val * (D p : ℝ))) z
      rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
      have hce0 : ν[(futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S) | Fq] z = 0 := by
        rw [hce]
        simp [Gq, hz]
      rw [hce0]
      simp
  exact hpoint
/-- The one-date integrated reward-to-raw comparator transfer on the same
actual source slice. -/
theorem integral_futureRewardComparatorGap_le
    (control0 : ContinuousLearningRows.TimeControl p)
    (q : Fin p.T) (hfuture : t.val + 1 < q.val)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S z ∂ν) ≤
      (∫ z, futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          ((ν).real (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
            rate rewards C_star C_h u t q hfuture)) := by
  have hL := integrable_futureRewardComparatorGap rate rewards C_star C_h u t
    control0 q hfuture S
  have hD := integrable_futureArrivalComparatorGap rate rewards C_star C_h u t
    control0 q hfuture S
  have hF := integrable_condExp
    (f := futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S)
    (μ := ν)
    (m := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
      rate rewards C_star C_h u t control0 q)
  let Gq := ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
    rate rewards C_star C_h u t q hfuture
  have hG := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega) _
      (ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
        rate rewards C_star C_h u t q hfuture control0)
  have hc : Integrable (fun z => Gq.indicator
      (fun _ => (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) z) ν :=
    (integrable_const ((p.m : ℝ) / (rate.eta.val * (D p : ℝ)))).indicator hG
  have hpoint := futureRewardComparatorGap_ae_le_condExp rate rewards C_star C_h u t
    control0 q hfuture S
  have hmono := integral_mono_ae hL (hF.add hc) hpoint
  have hfield := ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
    rate rewards C_star C_h u t control0 q (by omega)
  change (∫ z, futureRewardComparatorGap rate rewards C_star C_h u t q hfuture S z ∂ν) ≤
    ∫ z, ν[futureArrivalComparatorGap rate rewards C_star C_h u t q hfuture S |
      ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField
        rate rewards C_star C_h u t control0 q] z +
      Gq.indicator (fun x => (p.m : ℝ) / (rate.eta.val * (D p : ℝ))) z ∂ν at hmono
  rw [integral_add hF hc, integral_condExp hfield,
    integral_indicator_const _ hG, smul_eq_mul] at hmono
  simpa [Gq, mul_comm] using hmono
private theorem integrable_futureArrivalObservationAt
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ) :
    Integrable (futureArrivalObservationAt rate rewards C_star C_h u t n) ν := by
  by_cases hn : n < p.T
  · by_cases hf : t.val + 1 < n
    · simpa [futureArrivalObservationAt, hn, hf] using
        (integrable_futureArrivalObservation rate rewards C_star C_h u t control0
          ⟨n, hn⟩ hf)
    · simp [futureArrivalObservationAt, hn, hf]
  · simp [futureArrivalObservationAt, hn]
private theorem integrable_futureArrivalComparatorGapAt
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (futureArrivalComparatorGapAt rate rewards C_star C_h u t n S) ν := by
  by_cases hn : n < p.T
  · by_cases hf : t.val + 1 < n
    · simpa [futureArrivalComparatorGapAt, hn, hf] using
        (integrable_futureArrivalComparatorGap rate rewards C_star C_h u t control0
          ⟨n, hn⟩ hf S)
    · simp [futureArrivalComparatorGapAt, hn, hf]
  · simp [futureArrivalComparatorGapAt, hn]
private theorem integrable_futureRewardComparatorGapAt
    (control0 : ContinuousLearningRows.TimeControl p) (n : ℕ)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (futureRewardComparatorGapAt rate rewards C_star C_h u t n S) ν := by
  by_cases hn : n < p.T
  · by_cases hf : t.val + 1 < n
    · simpa [futureRewardComparatorGapAt, hn, hf] using
        (integrable_futureRewardComparatorGap rate rewards C_star C_h u t control0
          ⟨n, hn⟩ hf S)
    · simp [futureRewardComparatorGapAt, hn, hf]
  · simp [futureRewardComparatorGapAt, hn]
/-- The entire literal strict-future arrival selector is integrable, including
the empty-tail and all actual absent/disabled/overflow branches. -/
theorem integrable_futureArrivalObservationTotal
    (control0 : ContinuousLearningRows.TimeControl p) :
    Integrable (futureArrivalObservationTotal rate rewards C_star C_h u t) ν := by
  unfold futureArrivalObservationTotal
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z => futureArrivalObservationAt rate rewards C_star C_h u t n z)
      (fun n hn => integrable_futureArrivalObservationAt rate rewards C_star C_h u t
        control0 n))
/-- The complete same-calendar raw comparator selector is integrable. -/
theorem integrable_futureArrivalComparatorGapTotal
    (control0 : ContinuousLearningRows.TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (futureArrivalComparatorGapTotal rate rewards C_star C_h u t S) ν := by
  unfold futureArrivalComparatorGapTotal
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z => futureArrivalComparatorGapAt rate rewards C_star C_h u t n S z)
      (fun n hn => integrable_futureArrivalComparatorGapAt rate rewards C_star C_h u t
        control0 n S))
/-- The complete same-calendar reward comparator selector is integrable. -/
theorem integrable_futureRewardComparatorGapTotal
    (control0 : ContinuousLearningRows.TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (futureRewardComparatorGapTotal rate rewards C_star C_h u t S) ν := by
  unfold futureRewardComparatorGapTotal
  simpa only [← Finset.sum_apply] using
    (integrable_finsetSum
      (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
      (f := fun n z => futureRewardComparatorGapAt rate rewards C_star C_h u t n S z)
      (fun n hn => integrable_futureRewardComparatorGapAt rate rewards C_star C_h u t
        control0 n S))
private theorem integral_futureArrivalObservationTotal_eq_sum
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z, futureArrivalObservationTotal rate rewards C_star C_h u t z ∂ν) =
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ∫ z, futureArrivalObservationAt rate rewards C_star C_h u t n z ∂ν := by
  unfold futureArrivalObservationTotal
  exact integral_finsetSum
    (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
    (fun n hn => integrable_futureArrivalObservationAt rate rewards C_star C_h u t
      control0 n)
private theorem integral_futureArrivalComparatorGapTotal_eq_sum
    (control0 : ContinuousLearningRows.TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, futureArrivalComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) =
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ∫ z, futureArrivalComparatorGapAt rate rewards C_star C_h u t n S z ∂ν := by
  unfold futureArrivalComparatorGapTotal
  exact integral_finsetSum
    (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
    (fun n hn => integrable_futureArrivalComparatorGapAt rate rewards C_star C_h u t
      control0 n S)
private theorem integral_futureRewardComparatorGapTotal_eq_sum
    (control0 : ContinuousLearningRows.TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, futureRewardComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) =
      ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ∫ z, futureRewardComparatorGapAt rate rewards C_star C_h u t n S z ∂ν := by
  unfold futureRewardComparatorGapTotal
  exact integral_finsetSum
    (ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t)
    (fun n hn => integrable_futureRewardComparatorGapAt rate rewards C_star C_h u t
      control0 n S)
private theorem futureGateMassAt_eq_actual
    (n : ℕ) (hn : n < p.T) (hfuture : t.val + 1 < n) :
    ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt
        rate rewards C_star C_h u t n =
      (ν).real (ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t ⟨n, hn⟩ hfuture) := by
  simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt,
    hn, hfuture]
/-- Summing the one-date first-moment budget over every retained strict-future
date charges the original gate mass only once per actual date. -/
theorem integral_futureArrivalObservationTotal_le
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z, futureArrivalObservationTotal rate rewards C_star C_h u t z ∂ν) ≤
      (p.m : ℝ) *
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t := by
  rw [integral_futureArrivalObservationTotal_eq_sum rate rewards C_star C_h u t
    control0]
  calc
    _ ≤ ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        (p.m : ℝ) *
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt
            rate rewards C_star C_h u t n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hq : n < p.T := hn'.2
      have hf : t.val + 1 < n := by omega
      rw [futureGateMassAt_eq_actual rate rewards C_star C_h u t n hq hf]
      simpa [futureArrivalObservationAt, hq, hf] using
        (integral_futureArrivalObservation_le rate rewards C_star C_h u t
          control0 ⟨n, hq⟩ hf)
    _ = (p.m : ℝ) *
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t := by
      rw [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass,
        Finset.mul_sum]
/-- Summing the same-slice comparator transfers preserves every date and
charges only its actual future gate mass. -/
theorem integral_futureRewardComparatorGapTotal_le
    (control0 : ContinuousLearningRows.TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, futureRewardComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) ≤
      (∫ z, futureArrivalComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t := by
  rw [integral_futureRewardComparatorGapTotal_eq_sum rate rewards C_star C_h u t
    control0 S,
    integral_futureArrivalComparatorGapTotal_eq_sum rate rewards C_star C_h u t
    control0 S]
  calc
    _ ≤ ∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
        ((∫ z, futureArrivalComparatorGapAt rate rewards C_star C_h u t n S z ∂ν) +
          ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt
              rate rewards C_star C_h u t n) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      have hq : n < p.T := hn'.2
      have hf : t.val + 1 < n := by omega
      rw [futureGateMassAt_eq_actual rate rewards C_star C_h u t n hq hf]
      simpa [futureArrivalComparatorGapAt, futureRewardComparatorGapAt, hq, hf] using
        (integral_futureRewardComparatorGap_le rate rewards C_star C_h u t
          control0 ⟨n, hq⟩ hf S)
    _ = (∑ n ∈ ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates t,
          ∫ z, futureArrivalComparatorGapAt rate rewards C_star C_h u t n S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t := by
      rw [Finset.sum_add_distrib, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass,
        Finset.mul_sum]
/-- The clipped remaining-horizon consequence for the total weighted raw
arrival budget. -/
theorem integral_futureArrivalObservationTotal_le_horizon
    (control0 : ContinuousLearningRows.TimeControl p) :
    (∫ z, futureArrivalObservationTotal rate rewards C_star C_h u t z ∂ν) ≤
      (p.m : ℝ) * ((p.T - (t.val + 2) : ℕ) : ℝ) * (ν).real Set.univ := by
  have htotal := integral_futureArrivalObservationTotal_le rate rewards C_star C_h u t
    control0
  have hmass := ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass_le_horizon
    rate rewards C_star C_h u t
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (p.m : ℝ) *
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t := htotal
    _ ≤ (p.m : ℝ) * ((p.T - (t.val + 2) : ℕ) : ℝ) * (ν).real Set.univ := by
      calc
        (p.m : ℝ) * ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t ≤
          (p.m : ℝ) * (((p.T - (t.val + 2) : ℕ) : ℝ) * (ν).real Set.univ) :=
          mul_le_mul_of_nonneg_left hmass hm
        _ = (p.m : ℝ) * ((p.T - (t.val + 2) : ℕ) : ℝ) * (ν).real Set.univ := by ring
/-- The clipped remaining-horizon consequence for the actual reward
comparator transfer, with one shared date-count factor. -/
theorem integral_futureRewardComparatorGapTotal_le_horizon
    (control0 : ContinuousLearningRows.TimeControl p)
    (S : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z, futureRewardComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) ≤
      (∫ z, futureArrivalComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          ((p.T - (t.val + 2) : ℕ) : ℝ) * (ν).real Set.univ := by
  have htotal := integral_futureRewardComparatorGapTotal_le rate rewards C_star C_h u t
    control0 S
  have hmass := ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass_le_horizon
    rate rewards C_star C_h u t
  have hcoef : 0 ≤ (p.m : ℝ) / (rate.eta.val * (D p : ℝ)) := by
    apply div_nonneg (Nat.cast_nonneg _)
    exact (mul_pos rate.eta.property (by exact_mod_cast D_pos p)).le
  have h := mul_le_mul_of_nonneg_left hmass hcoef
  calc
    _ ≤ (∫ z, futureArrivalComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) +
        ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t := htotal
    _ ≤ _ := by
      calc
        (∫ z, futureArrivalComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) +
            ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
                rate rewards C_star C_h u t ≤
          (∫ z, futureArrivalComparatorGapTotal rate rewards C_star C_h u t S z ∂ν) +
            ((p.m : ℝ) / (rate.eta.val * (D p : ℝ))) *
              (((p.T - (t.val + 2) : ℕ) : ℝ) * (ν).real Set.univ) :=
            by linarith [h]
        _ = _ := by ring
end Bandits.Support.ReferenceFirstCollectionRenewalFutureLearningMoments
end
