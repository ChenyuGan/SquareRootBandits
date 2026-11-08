/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionFixedIDWeightedArrivalBudget
public import Bandits.Support.ReferenceFirstCollectionOriginalCalendarRoundingJoin

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# Fixed-ID localization of the first-LIVE calendar rounding comparison

The argument keeps the original source law and localizes each actual birth,
nonempty, and empty-pending branch before assembling the source integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstLiveFixedIDCalendarRoundedComparison

open ConstructorDimensions
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open ReferenceFirstLiveOriginalCalendarRoundedComparison
open ContinuousLearningRows (TimeControl)

abbrev Parameters := ConstructorDimensions.Parameters
abbrev RateInput := ReferenceActivePhysicalStep.RateInput
abbrev RewardTable := ActualInitializationPhysicalStep.GridRewardTable
abbrev TimeControl := ContinuousLearningRows.TimeControl

variable {p : Parameters} (rate : RateInput p) (rewards : RewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "Dset" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "scale" => rate.eta.val * (D p : ℝ)

private theorem localized_condExp_rounding
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : MeasurableSpace Ω}
    {nu : @Measure Ω mΩ}
    (hF : F ≤ mΩ)
    [SigmaFinite (nu.trim hF)]
    (D G : Set Ω) (hD : MeasurableSet[F] D)
    (theta A c xi : Fin p.K → Ω → ℝ) (rho : Fin p.K → ℝ)
    (S₀ : Finset (Fin p.K)) (denom : ℝ)
    (hAint : ∀ j, Integrable (A j) nu)
    (hthetaMeas : ∀ j, Measurable[F] (theta j))
    (hthetaBound : ∀ j z, 0 ≤ theta j z ∧ theta j z ≤ 1)
    (hCE : ∀ j, nu[(A j) | F] =ᵐ[nu] G.indicator (c j))
    (hCoeff : ∀ j z, z ∈ G → rho j - xi j z / denom ≤ c j z ∧ c j z ≤ rho j)
    (hRoundInt : Integrable (G.indicator (fun z =>
      (∑ j ∈ S₀, rho j) - ∑ j, theta j z * rho j)) nu)
    (hFloorInt : Integrable (G.indicator (fun z => ∑ j ∈ S₀, xi j z / denom)) nu) :
    (∫ z in D, G.indicator (fun z =>
      (∑ j ∈ S₀, rho j) - ∑ j, theta j z * rho j) z ∂nu) ≤
      (∫ z in D, (∑ j ∈ S₀, A j z) - ∑ j, theta j z * A j z ∂nu) +
      ∫ z in D, G.indicator (fun z => ∑ j ∈ S₀, xi j z / denom) z ∂nu := by
  have hDambient : MeasurableSet[mΩ] D := hF D hD
  let w : Fin p.K → Ω → ℝ := fun j => D.indicator (theta j)
  have hwMeas (j : Fin p.K) : Measurable[F] (w j) :=
    (hthetaMeas j).indicator hD
  have hwBound (j : Fin p.K) (z : Ω) : ‖w j z‖ ≤ 1 := by
    by_cases hz : z ∈ D
    · simp [w, Set.indicator_of_mem hz, Real.norm_eq_abs,
        abs_of_nonneg (hthetaBound j z).1, (hthetaBound j z).2]
    · simp [w, Set.indicator_of_notMem hz]
  have hWAint (j : Fin p.K) : Integrable (fun z => w j z * A j z) nu :=
    (hAint j).bdd_mul ((hwMeas j).mono hF le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall (hwBound j))
  have hThetaAInt (j : Fin p.K) : Integrable (fun z => theta j z * A j z) nu :=
    (hAint j).bdd_mul ((hthetaMeas j).mono hF le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hthetaBound j z).1] using
          (hthetaBound j z).2)
  have hMean (j : Fin p.K) :
      (∫ z in D, A j z ∂nu) = ∫ z in D, G.indicator (c j) z ∂nu := by
    calc
      _ = ∫ z in D, nu[(A j) | F] z ∂nu :=
        (setIntegral_condExp hF (hAint j) hD).symm
      _ = _ := setIntegral_congr_ae hDambient ((hCE j).mono fun z hz _ => hz)
  have hWeightedCE (j : Fin p.K) :
      nu[(fun z => w j z * A j z) | F] =ᵐ[nu]
        fun z => w j z * G.indicator (c j) z := by
    have hpull := condExp_mul_of_aestronglyMeasurable_left
      (hwMeas j).aestronglyMeasurable (hWAint j) (hAint j)
    filter_upwards [hpull, hCE j] with z hp hz
    calc
      _ = w j z * nu[(A j) | F] z := hp
      _ = w j z * G.indicator (c j) z := congrArg (fun x : ℝ => w j z * x) hz
  have hWeighted (j : Fin p.K) :
      (∫ z in D, theta j z * A j z ∂nu) =
        ∫ z in D, theta j z * G.indicator (c j) z ∂nu := by
    calc
      _ = ∫ z, D.indicator (fun z => theta j z * A j z) z ∂nu :=
        (integral_indicator hDambient).symm
      _ = ∫ z, w j z * A j z ∂nu := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ D <;> simp [w, Set.indicator, hz]
      _ = ∫ z, w j z * G.indicator (c j) z ∂nu := by
        calc
          _ = ∫ z, nu[(fun z => w j z * A j z) | F] z ∂nu :=
            (integral_condExp (f := fun z => w j z * A j z) hF).symm
          _ = _ := integral_congr_ae (hWeightedCE j)
      _ = ∫ z, D.indicator (fun z => theta j z * G.indicator (c j) z) z ∂nu := by
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ D <;> simp [w, Set.indicator, hz]
      _ = ∫ z in D, theta j z * G.indicator (c j) z ∂nu := integral_indicator hDambient
  have hCoeffInt (j : Fin p.K) : Integrable (G.indicator (c j)) nu :=
    (integrable_condExp (f := A j)).congr (hCE j)
  have hWeightedCoeffInt (j : Fin p.K) :
      Integrable (fun z => theta j z * G.indicator (c j) z) nu := by
    exact (hCoeffInt j).bdd_mul
      ((hthetaMeas j).mono hF le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (hthetaBound j z).1] using
          (hthetaBound j z).2)
  have hRawEq :
      (∫ z in D, (∑ j ∈ S₀, A j z) - ∑ j, theta j z * A j z ∂nu) =
        ∫ z in D, (∑ j ∈ S₀, G.indicator (c j) z) -
          ∑ j, theta j z * G.indicator (c j) z ∂nu := by
    have hsumA : (∫ z, ∑ j ∈ S₀, A j z ∂nu.restrict D) =
        ∑ j ∈ S₀, ∫ z, A j z ∂nu.restrict D :=
      integral_finsetSum _ (fun j hj => (hAint j).integrableOn.integrable)
    have hsumC : (∫ z, ∑ j ∈ S₀, G.indicator (c j) z ∂nu.restrict D) =
        ∑ j ∈ S₀, ∫ z, G.indicator (c j) z ∂nu.restrict D :=
      integral_finsetSum _ (fun j hj => (hCoeffInt j).integrableOn.integrable)
    have hsumWA : (∫ z, ∑ j, theta j z * A j z ∂nu.restrict D) =
        ∑ j, ∫ z, theta j z * A j z ∂nu.restrict D :=
      integral_finsetSum _ (fun j hj => (hThetaAInt j).integrableOn.integrable)
    have hsumWC : (∫ z, ∑ j, theta j z * G.indicator (c j) z ∂nu.restrict D) =
        ∑ j, ∫ z, theta j z * G.indicator (c j) z ∂nu.restrict D :=
      integral_finsetSum _ (fun j hj => (hWeightedCoeffInt j).integrableOn.integrable)
    rw [integral_sub
        (integrable_finsetSum _ (fun j hj => (hAint j).integrableOn.integrable))
        (integrable_finsetSum _ (fun j hj => (hThetaAInt j).integrableOn.integrable)),
      integral_sub
        (integrable_finsetSum _ (fun j hj => (hCoeffInt j).integrableOn.integrable))
        (integrable_finsetSum _ (fun j hj => (hWeightedCoeffInt j).integrableOn.integrable)),
      hsumA, hsumC, hsumWA, hsumWC]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      exact hMean j
    · apply Finset.sum_congr rfl
      intro j hj
      exact hWeighted j
  have hCoeffSumInt : Integrable (fun z =>
      (∑ j ∈ S₀, G.indicator (c j) z) -
        ∑ j, theta j z * G.indicator (c j) z) nu :=
    (integrable_finsetSum _ (fun j hj => hCoeffInt j)).sub
      (integrable_finsetSum _ (fun j hj => hWeightedCoeffInt j))
  have hPoint (z : Ω) :
      G.indicator (fun z => (∑ j ∈ S₀, rho j) - ∑ j, theta j z * rho j) z ≤
        ((∑ j ∈ S₀, G.indicator (c j) z) -
          ∑ j, theta j z * G.indicator (c j) z) +
      G.indicator (fun z => ∑ j ∈ S₀, xi j z / denom) z := by
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      have hlower :
          (∑ j ∈ S₀, (rho j - xi j z / denom)) ≤ ∑ j ∈ S₀, c j z := by
        apply Finset.sum_le_sum
        intro j hj
        exact (hCoeff j z hz).1
      have hupper :
          (∑ j, theta j z * c j z) ≤ ∑ j, theta j z * rho j := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left (hCoeff j z hz).2 (hthetaBound j z).1
      rw [Finset.sum_sub_distrib] at hlower
      linarith
    · simp [Set.indicator_of_notMem hz]
  have hRightInt := hCoeffSumInt.add hFloorInt
  have hmono := setIntegral_mono_ae (s := D)
    hRoundInt.integrableOn hRightInt.integrableOn (Filter.Eventually.of_forall hPoint)
  have hsplit :
      (∫ z in D,
        ((∑ j ∈ S₀, G.indicator (c j) z) -
          ∑ j, theta j z * G.indicator (c j) z) +
        G.indicator (fun z => ∑ j ∈ S₀, xi j z / denom) z ∂nu) =
      (∫ z in D, (∑ j ∈ S₀, G.indicator (c j) z) -
        ∑ j, theta j z * G.indicator (c j) z ∂nu) +
      ∫ z in D, G.indicator (fun z => ∑ j ∈ S₀, xi j z / denom) z ∂nu := by
    exact integral_add hCoeffSumInt.integrableOn.integrable
      hFloorInt.integrableOn.integrable
  have hmono' := hmono.trans_eq hsplit
  rw [← hRawEq] at hmono'
  exact hmono'

section ContinuingBranches

variable (q : Fin (M p)) (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val)

local notation "PlusZ" => ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
  rate rewards C_star C_h q t s hs control0
local notation "muPlus" => ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
  rate rewards C_star C_h q t s hs control0
local notation "Fplus" => ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
  rate rewards C_star C_h q t s hs control0
local notation "Gplus" => ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
  rate rewards C_star C_h q t s hs control0
local notation "thetaPlus" => ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore
  rate rewards C_star C_h q t s hs control0
local notation "Aplus" => ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA
  rate rewards C_star C_h q t s hs control0
local notation "cPlus" => ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus
  rate rewards C_star C_h q t s hs control0
local notation "xiPlus" => ReferenceFirstLiveAllArmPrefixAdaptation.markerRatePlus
  rate rewards C_star C_h q t s hs control0
private theorem fixedID_nonempty_local (comparator : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in {z : PlusZ | z.val.val.1.1 = ids},
      calendarRoundedGap rate rewards C_star C_h t comparator z.val.val ∂muPlus) ≤
      (∫ z in {z : PlusZ | z.val.val.1.1 = ids},
        calendarRawGap rate rewards C_star C_h t comparator z.val.val ∂muPlus) +
      ∫ z in {z : PlusZ | z.val.val.1.1 = ids},
        calendarFloorLoss rate rewards C_star C_h t comparator z.val.val ∂muPlus := by
  let I := ({ids} : Set (CompletePublicTable.IDArray p))
  let rho : Fin p.K → ℝ := fun j =>
    ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j
  have hDfield : MeasurableSet[Fplus] {z : PlusZ | z.val.val.1.1 = ids} := by
    simpa [I] using
      ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_nonempty
        rate rewards C_star C_h q t s hs control0 I (measurableSet_singleton ids)
  have hthetaMeas (j : Fin p.K) : Measurable[Fplus] (thetaPlus j) :=
    ReferenceFirstLiveQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j
  have hthetaBound (j : Fin p.K) (z : PlusZ) :
      0 ≤ thetaPlus j z ∧ thetaPlus j z ≤ 1 :=
    ReferenceFirstLiveQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z
  have hAint (j : Fin p.K) : Integrable (Aplus j) muPlus :=
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j
  have hCE (j : Fin p.K) :
      muPlus[(Aplus j) | Fplus] =ᵐ[muPlus] (Gplus).indicator (cPlus j) :=
    ReferenceFirstLiveAllArmAcceptedConditionalMoments.acceptedA_condExp_firstMoment
      rate rewards C_star C_h q t s hs control0 j
  have hCoeff (j : Fin p.K) (z : PlusZ) (hz : z ∈ Gplus) :
      rho j - xiPlus j z / scale ≤ cPlus j z ∧ cPlus j z ≤ rho j := by
    have hc := ReferenceFirstLiveAllArmPrefixAdaptation.firstCoefficientPlus_bounds
      rate rewards C_star C_h q t s hs control0 j z
    exact ⟨hc.2.1, hc.2.2.1⟩
  have hRoundInt : Integrable ((Gplus).indicator (fun z =>
      (∑ j ∈ comparator.val, rho j) - ∑ j, thetaPlus j z * rho j)) muPlus := by
    simpa [rho] using
      ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_nonemptyRoundedGap
        rate rewards C_star C_h q t s hs control0 comparator
  have hFloorInt : Integrable ((Gplus).indicator (fun z =>
      ∑ j ∈ comparator.val, xiPlus j z / scale)) muPlus := by
    simpa using ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_nonemptyFloorLoss
      rate rewards C_star C_h q t s hs control0 comparator
  let : IsFiniteMeasure muPlus :=
    ReferenceFirstLiveAllArmPrefixAdaptation.isFiniteMeasure_branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
  have hcore := localized_condExp_rounding (Ω := PlusZ) (F := Fplus) (nu := muPlus)
    (ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField_le
      rate rewards C_star C_h q t s hs control0)
    {z : PlusZ | z.val.val.1.1 = ids} Gplus hDfield
    thetaPlus Aplus cPlus xiPlus rho comparator.val scale
    hAint hthetaMeas hthetaBound hCE hCoeff hRoundInt hFloorInt
  simpa only [calendarRoundedGap, calendarRawGap, calendarFloorLoss,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_nonempty
      rate rewards C_star C_h q t s hs control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_nonempty
      rate rewards C_star C_h q t s hs control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_nonempty
      rate rewards C_star C_h q t s hs control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_nonempty
      rate rewards C_star C_h q t s hs control0, Set.indicator] using hcore

local notation "EmptyZ" => ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
  rate rewards C_star C_h q t s hs control0
local notation "muEmpty" => ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
  rate rewards C_star C_h q t s hs control0
local notation "Fempty" => ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
  rate rewards C_star C_h q t s hs control0
local notation "Gempty" => ReferenceFirstLiveEmptyPendingAcceptedMoments.G
  rate rewards C_star C_h q t s hs control0
local notation "thetaEmpty" => ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore
  rate rewards C_star C_h q t s hs control0
local notation "Aempty" => ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA
  rate rewards C_star C_h q t s hs control0
local notation "cEmpty" => ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient
  rate rewards C_star C_h q t s hs control0
local notation "xiEmpty" => fun j z =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.xiEmpty rate rewards C_star C_h q t s hs control0
    (ReferenceFirstLiveEmptyPendingMarkerLaw.xofEmpty rate rewards C_star C_h q t s hs control0 z) j
private theorem fixedID_empty_local (comparator : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in {z : EmptyZ | z.val.val.1.1 = ids},
      calendarRoundedGap rate rewards C_star C_h t comparator z.val.val ∂muEmpty) ≤
      (∫ z in {z : EmptyZ | z.val.val.1.1 = ids},
        calendarRawGap rate rewards C_star C_h t comparator z.val.val ∂muEmpty) +
      ∫ z in {z : EmptyZ | z.val.val.1.1 = ids},
        calendarFloorLoss rate rewards C_star C_h t comparator z.val.val ∂muEmpty := by
  let I := ({ids} : Set (CompletePublicTable.IDArray p))
  let rho : Fin p.K → ℝ := fun j =>
    ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j
  have hDfield : MeasurableSet[Fempty] {z : EmptyZ | z.val.val.1.1 = ids} := by
    simpa [I] using
      ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_empty
        rate rewards C_star C_h q t s hs control0 I (measurableSet_singleton ids)
  have hthetaMeas (j : Fin p.K) : Measurable[Fempty] (thetaEmpty j) :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.measurable_thetaBefore_field
      rate rewards C_star C_h q t s hs control0 j
  have hthetaBound (j : Fin p.K) (z : EmptyZ) :
      0 ≤ thetaEmpty j z ∧ thetaEmpty j z ≤ 1 :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.thetaBefore_bounds
      rate rewards C_star C_h q t s hs control0 j z
  have hAint (j : Fin p.K) : Integrable (Aempty j) muEmpty :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.integrable_acceptedA
      rate rewards C_star C_h q t s hs control0 j
  have hCE (j : Fin p.K) :
      muEmpty[(Aempty j) | Fempty] =ᵐ[muEmpty] (Gempty).indicator (cEmpty j) :=
    ReferenceFirstLiveEmptyPendingAcceptedMoments.acceptedA_condExp_firstMoment
      rate rewards C_star C_h q t s hs control0 j
  have hCoeff (j : Fin p.K) (z : EmptyZ) (hz : z ∈ Gempty) :
      rho j - xiEmpty j z / scale ≤ cEmpty j z ∧ cEmpty j z ≤ rho j := by
    have hc := ReferenceFirstLiveEmptyPendingAcceptedMoments.firstCoefficient_bounds
      rate rewards C_star C_h q t s hs control0 j z
    exact ⟨hc.1, hc.2.2.1⟩
  have hRoundInt : Integrable ((Gempty).indicator (fun z =>
      (∑ j ∈ comparator.val, rho j) - ∑ j, thetaEmpty j z * rho j)) muEmpty := by
    simpa [rho] using ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_emptyRoundedGap
      rate rewards C_star C_h q t s hs control0 comparator
  have hFloorInt : Integrable ((Gempty).indicator (fun z =>
      ∑ j ∈ comparator.val, xiEmpty j z / scale)) muEmpty := by
    simpa using ReferenceFirstLiveOriginalCalendarArrivalMoments.integrable_emptyFloorLoss
      rate rewards C_star C_h q t s hs control0 comparator
  let : IsFiniteMeasure muEmpty :=
    ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty_finite
      rate rewards C_star C_h q t s hs control0
  have hcore := localized_condExp_rounding (Ω := EmptyZ) (F := Fempty) (nu := muEmpty)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0)
    {z : EmptyZ | z.val.val.1.1 = ids} Gempty hDfield
    thetaEmpty Aempty cEmpty xiEmpty rho comparator.val scale
    hAint hthetaMeas hthetaBound hCE hCoeff hRoundInt hFloorInt
  simpa only [calendarRoundedGap, calendarRawGap, calendarFloorLoss,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_empty
      rate rewards C_star C_h q t s hs control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_empty
      rate rewards C_star C_h q t s hs control0,
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_empty
      rate rewards C_star C_h q t s hs control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_empty
      rate rewards C_star C_h q t s hs control0, Set.indicator] using hcore

end ContinuingBranches

section Birth

variable (q : Fin (M p)) (t : Fin p.T)

local notation "BirthZ" => ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h
  t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "muBirth" => ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h
  t (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
local notation "X" => ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
  rate rewards C_star C_h q t control0
local notation "muC" => ReferenceRetainedSourceCoupling.retainedRemainderMeasure
  rate rewards C_star C_h q t t.val le_rfl control0
local notation "coords" => ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
  rate rewards C_star C_h q t control0
local notation "birthY" => ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
  rate rewards C_star C_h q t control0

include control0 in
private theorem fixedID_birth_mass :
    muBirth {z : BirthZ | z.val.1.1 = ids} =
      muC {x : X | x.val.1.1 = ids} := by
  let B : Set X := {x | x.val.1.1 = ids}
  have hB : MeasurableSet B := (measurableSet_singleton ids).preimage
    ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hm := congrArg (fun ν => ν (B ×ˢ Set.univ))
    (ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
      rate rewards C_star C_h q t control0)
  rw [Measure.map_apply
      (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
        rate rewards C_star C_h q t control0) (hB.prod MeasurableSet.univ),
    Measure.prod_prod] at hm
  have heq : (coords ⁻¹' (B ×ˢ Set.univ)) = {z : BirthZ | z.val.1.1 = ids} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, B,
      Set.mem_ofPred_eq]
    rw [ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
      rate rewards C_star C_h q t control0 z]
  rw [heq] at hm
  simpa only [measure_univ, mul_one] using hm

include control0 in
private theorem fixedID_birth_firstMoment (j : Fin p.K) :
    (muBirth).real {z : BirthZ | z.val.1.1 = ids} *
        (ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j -
          CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j / scale) ≤
      (∫ z in {z : BirthZ | z.val.1.1 = ids}, birthY z j ∂muBirth) ∧
    (∫ z in {z : BirthZ | z.val.1.1 = ids}, birthY z j ∂muBirth) ≤
      (muBirth).real {z : BirthZ | z.val.1.1 = ids} *
        ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j := by
  let B : Set X := {x | x.val.1.1 = ids}
  let Db : Set BirthZ := {z | z.val.1.1 = ids}
  have hB : MeasurableSet B :=
    (measurableSet_singleton ids).preimage
      ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
    rate rewards C_star C_h q t control0 j B Set.univ hB MeasurableSet.univ
  have heq : {z : BirthZ | (coords z).1 ∈ B ∧ (coords z).2.1 ∈ Set.univ} = Db := by
    ext z
    simp only [B, Db, Set.mem_ofPred_eq, Set.mem_univ, and_true]
    rw [ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
      rate rewards C_star C_h q t control0 z]
  have hfirst := hmom.2.2.2.2.1
  rw [heq] at hfirst
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at hfirst
  have hmass := congrArg ENNReal.toReal
    (fixedID_birth_mass (rate := rate) (rewards := rewards) (C_star := C_star)
      (C_h := C_h) (control0 := control0) (ids := ids) (q := q) (t := t))
  have hcoeff := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
    rate rewards t j
  have hquant := hcoeff
  dsimp only [ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds] at hquant
  have hlow :
      (muBirth).real Db * (ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j -
        CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j / scale) ≤
        ∫ z in Db, birthY z j ∂muBirth := by
    rw [hfirst]
    rw [show (muC B).toReal = (muBirth).real Db from hmass.symm]
    have hmnonneg : 0 ≤ (muBirth).real Db := measureReal_nonneg
    have hc := hquant.1
    change ((rewards t j).val : ℝ) / (D p : ℝ) -
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j /
        (rate.eta.val * (D p : ℝ)) ≤
      CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
        QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
          (((rewards t j).val : ℝ) / (D p : ℝ)) at hc
    change (muBirth).real Db *
      (((rewards t j).val : ℝ) / (D p : ℝ) -
        CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j /
          (rate.eta.val * (D p : ℝ))) ≤
      (muBirth).real Db * CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
        QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
          (((rewards t j).val : ℝ) / (D p : ℝ))
    nlinarith [mul_le_mul_of_nonneg_left hc hmnonneg]
  have hupp :
      (∫ z in Db, birthY z j ∂muBirth) ≤
        (muBirth).real Db * ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j := by
    rw [hfirst]
    rw [show (muC B).toReal = (muBirth).real Db from hmass.symm]
    have hmnonneg : 0 ≤ (muBirth).real Db := measureReal_nonneg
    have hc := hquant.2.1
    change CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
      QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
        (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
        (((rewards t j).val : ℝ) / (D p : ℝ)) ≤
      ((rewards t j).val : ℝ) / (D p : ℝ) at hc
    change (muBirth).real Db * CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
        QuantizedRecordingMoments.quantizedValue (D p) rate.eta.val
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
          (((rewards t j).val : ℝ) / (D p : ℝ)) ≤
      (muBirth).real Db * (((rewards t j).val : ℝ) / (D p : ℝ))
    nlinarith [mul_le_mul_of_nonneg_left hc hmnonneg]
  exact ⟨by simpa only [Db] using hlow, by simpa only [Db] using hupp⟩

include control0 in
private theorem fixedID_birth_local (comparator : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z in {z : BirthZ | z.val.1.1 = ids},
      calendarRoundedGap rate rewards C_star C_h t comparator z.val ∂muBirth) ≤
      (∫ z in {z : BirthZ | z.val.1.1 = ids},
        calendarRawGap rate rewards C_star C_h t comparator z.val ∂muBirth) +
      ∫ z in {z : BirthZ | z.val.1.1 = ids},
        calendarFloorLoss rate rewards C_star C_h t comparator z.val ∂muBirth := by
  let Db : Set BirthZ := {z | z.val.1.1 = ids}
  let theta0 : Fin p.K → ℝ := ProductSetLaw.theta p.m (fun _ => (1 : ℝ))
  let rho : Fin p.K → ℝ := fun j =>
    ReferenceFirstLiveOriginalCalendarArrivalMoments.roundedReward rewards t j
  let xi : Fin p.K → ℝ := fun j => CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
  have hYint (j : Fin p.K) : Integrable (fun z : BirthZ => birthY z j) muBirth :=
    (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ).2.2.1
  have htheta (j : Fin p.K) : 0 ≤ theta0 j :=
    (ProductSetLaw.theta_pos (fun _ : Fin p.K => (1 : ℝ)) j
      (ConstructorDimensions.m_pos p) p.m_lt_K (fun _ => by norm_num)).le
  have hroundedFun :
      (fun z : BirthZ => calendarRoundedGap rate rewards C_star C_h t comparator z.val) =
      fun _ => (∑ j ∈ comparator.val, rho j) - ∑ j, theta0 j * rho j := by
    funext z
    simp [calendarRoundedGap,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
        rate rewards C_star C_h q t control0 z,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
        rate rewards C_star C_h q t, theta0, rho]
  have hroundInt :
      (∫ z in Db, calendarRoundedGap rate rewards C_star C_h t comparator z.val ∂muBirth) =
        (muBirth).real Db * ((∑ j ∈ comparator.val, rho j) - ∑ j, theta0 j * rho j) := by
    rw [show (fun z : BirthZ => calendarRoundedGap rate rewards C_star C_h t comparator z.val) =
      fun _ => (∑ j ∈ comparator.val, rho j) - ∑ j, theta0 j * rho j from hroundedFun]
    simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hrawFun :
      (fun z : BirthZ => calendarRawGap rate rewards C_star C_h t comparator z.val) =
      fun z => (∑ j ∈ comparator.val, birthY z j) - ∑ j, theta0 j * birthY z j := by
    funext z
    simp [calendarRawGap,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival_birth
        rate rewards C_star C_h q t control0,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta_birth
        rate rewards C_star C_h q t, theta0]
  have hrawInt :
      (∫ z in Db, calendarRawGap rate rewards C_star C_h t comparator z.val ∂muBirth) =
        (∑ j ∈ comparator.val, ∫ z in Db, birthY z j ∂muBirth) -
          ∑ j, theta0 j * ∫ z in Db, birthY z j ∂muBirth := by
    rw [show (fun z : BirthZ => calendarRawGap rate rewards C_star C_h t comparator z.val) =
      fun z => (∑ j ∈ comparator.val, birthY z j) - ∑ j, theta0 j * birthY z j from hrawFun]
    rw [integral_sub]
    · rw [integral_finsetSum _ (fun j hj => (hYint j).integrableOn.integrable),
        integral_finsetSum _ (fun j hj => ((hYint j).const_mul (theta0 j)).integrableOn.integrable)]
      simp only [integral_const_mul]
    · exact (integrable_finsetSum _ (fun j hj => hYint j)).integrableOn
    · exact (integrable_finsetSum _ (fun j hj => (hYint j).const_mul (theta0 j))).integrableOn
  have hfloorFun :
      (fun z : BirthZ => calendarFloorLoss rate rewards C_star C_h t comparator z.val) =
      fun _ => ∑ j ∈ comparator.val, xi j / scale := by
    funext z
    simp [calendarFloorLoss,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRetained_birth
        rate rewards C_star C_h q t control0 z,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarRate_birth
        rate rewards C_star C_h q t control0, xi]
  have hfloorInt :
      (∫ z in Db, calendarFloorLoss rate rewards C_star C_h t comparator z.val ∂muBirth) =
        (muBirth).real Db * (∑ j ∈ comparator.val, xi j / scale) := by
    rw [show (fun z : BirthZ => calendarFloorLoss rate rewards C_star C_h t comparator z.val) =
      fun _ => ∑ j ∈ comparator.val, xi j / scale from hfloorFun]
    simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
  have hlower :
      (muBirth).real Db * (∑ j ∈ comparator.val, rho j) ≤
        (∑ j ∈ comparator.val, ∫ z in Db, birthY z j ∂muBirth) +
          (muBirth).real Db * (∑ j ∈ comparator.val, xi j / scale) := by
    calc
      _ = ∑ j ∈ comparator.val, (muBirth).real Db * rho j := by rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ comparator.val,
          ((∫ z in Db, birthY z j ∂muBirth) + (muBirth).real Db * (xi j / scale)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h := (fixedID_birth_firstMoment (rate := rate) (rewards := rewards)
          (C_star := C_star) (C_h := C_h) (control0 := control0) (ids := ids)
          (q := q) (t := t) j).1
        dsimp [rho, xi, Db] at h ⊢
        nlinarith [h]
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hupper :
      (∑ j : Fin p.K, theta0 j * ∫ z in Db, birthY z j ∂muBirth) ≤
        (muBirth).real Db * ∑ j : Fin p.K, theta0 j * rho j := by
    calc
      _ ≤ ∑ j : Fin p.K, theta0 j * ((muBirth).real Db * rho j) := by
        apply Finset.sum_le_sum
        intro j hj
        exact mul_le_mul_of_nonneg_left
          (fixedID_birth_firstMoment (rate := rate) (rewards := rewards)
            (C_star := C_star) (C_h := C_h) (control0 := control0) (ids := ids)
            (q := q) (t := t) j).2 (htheta j)
      _ = _ := by
        calc
          _ = ∑ j : Fin p.K, (muBirth).real Db * (theta0 j * rho j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = _ := by rw [Finset.mul_sum]
  rw [hroundInt, hrawInt, hfloorInt]
  nlinarith [hlower, hupper]

end Birth

section OriginalSourceAssembly

variable (date : Fin p.T)

local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h date
local notation "BirthZ" => fun q => ReferenceTotalSourceDisintegration.SourceStratum
  rate rewards C_star C_h date (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date)
local notation "muB" => fun q => ReferenceTotalSourceDisintegration.sourceStratumMeasure
  rate rewards C_star C_h date (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date)
local notation "PlusZ" => fun q (v : Fin (date.val + 1)) =>
  ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h q date
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "muP" => fun q (v : Fin (date.val + 1)) =>
  ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q date
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "EmptyZ" => fun q (v : Fin (date.val + 1)) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h q date
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0
local notation "muE" => fun q (v : Fin (date.val + 1)) =>
  ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q date
    (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0

include control0 in
private theorem not_retained_on_exception (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    omega ∉ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h date := by
  intro hk
  rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
    rate rewards C_star C_h date control0] at hk
  obtain ⟨i, hi, hωi⟩ : ∃ i : Fin 6, (i = 0 ∨ i = 1 ∨ i = 5) ∧ omega ∈ phase i := by
    rcases h with h | h | h
    · exact ⟨0, Or.inl rfl, h⟩
    · exact ⟨1, Or.inr (Or.inl rfl), h⟩
    · exact ⟨5, Or.inr (Or.inr rfl), h⟩
  obtain ⟨j, hj, hωj⟩ : ∃ j : Fin 6, (j = 2 ∨ j = 3 ∨ j = 4) ∧ omega ∈ phase j := by
    rcases hk.1 with h | h | h
    · exact ⟨2, Or.inl rfl, h⟩
    · exact ⟨3, Or.inr (Or.inl rfl), h⟩
    · exact ⟨4, Or.inr (Or.inr rfl), h⟩
  have hij : i ≠ j := by
    rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> decide
  exact Set.disjoint_left.mp
    (ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint
      rate rewards C_star C_h date hij) hωi hωj

private theorem calendarArrival_zero_on_exception (j : Fin p.K)
    (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
      rate rewards C_star C_h date j omega = 0 := by
  rcases h with h | h | h
  · have hL := (ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
      rate rewards C_star C_h omega h).2.1
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    simp only [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells,
      hL, List.getElem?_nil, ite_self]
  · have hfuture : date.val <
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
        rate rewards C_star C_h omega := h.2
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    exact ite_eq_right (Nat.not_le_of_lt hfuture)
  · have hlen :
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveCells
        rate rewards C_star C_h omega).length ≤ date.val -
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveStart
            rate rewards C_star C_h omega := by
      exact (ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h omega).trans_le h.2.2
    unfold ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
    rw [List.getElem?_eq_none hlen]
    simp

include control0 in
private theorem live_observer_zero_on_exception (comparator : ProductSetLaw.ProductSet p.K p.m)
    (omega : BootstrapPrivateRoundStreams.SourceInput p)
    (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) :
    calendarRoundedGap rate rewards C_star C_h date comparator omega = 0 ∧
      calendarRawGap rate rewards C_star C_h date comparator omega = 0 ∧
      calendarFloorLoss rate rewards C_star C_h date comparator omega = 0 := by
  have hnot := not_retained_on_exception rate rewards C_star C_h control0 date omega h
  have hR : calendarRoundedGap rate rewards C_star C_h date comparator omega = 0 := by
    simp [calendarRoundedGap, hnot]
  have hF : calendarFloorLoss rate rewards C_star C_h date comparator omega = 0 := by
    simp [calendarFloorLoss, hnot]
  have hS : (∑ j ∈ comparator.val,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
        rate rewards C_star C_h date j omega) = 0 :=
    Finset.sum_eq_zero fun j hj =>
      calendarArrival_zero_on_exception rate rewards C_star C_h date j omega h
  have hK : (∑ j : Fin p.K,
      ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarTheta
        rate rewards C_star C_h date j omega *
        ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarAcceptedArrival
          rate rewards C_star C_h date j omega) = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [calendarArrival_zero_on_exception rate rewards C_star C_h date j omega h]
      simp
  have hA : calendarRawGap rate rewards C_star C_h date comparator omega = 0 := by
    simp [calendarRawGap, hS, hK]
  exact ⟨hR, hA, hF⟩

include control0 in
private theorem integral_fixedID_components
    (f : BootstrapPrivateRoundStreams.SourceInput p → ℝ) (hf : Integrable f μ)
    (hzero : ∀ omega, omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5 → f omega = 0) :
    (∫ omega in Dset, f omega ∂μ) =
      (∑ q : Fin (M p),
        ∫ z in {z : BirthZ q | z.val.1.1 = ids}, f z.val ∂muB q) +
      ∑ q : Fin (M p), ∑ v : Fin (date.val + 1),
        ((∫ z in {z : PlusZ q v | z.val.val.1.1 = ids},
            f z.val.val ∂muP q v) +
          ∫ z in {z : EmptyZ q v | z.val.val.1.1 = ids},
            f z.val.val ∂muE q v) := by
  let g : BootstrapPrivateRoundStreams.SourceInput p → ℝ := (Dset).indicator f
  have hD : MeasurableSet Dset :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hg : Integrable g μ := by simpa only [g] using hf.indicator hD
  have hzeroG (omega : BootstrapPrivateRoundStreams.SourceInput p)
      (h : omega ∈ phase 0 ∨ omega ∈ phase 1 ∨ omega ∈ phase 5) : g omega = 0 := by
    simp [g, hzero omega h]
  let embB (q : Fin (M p)) := MeasurableEmbedding.subtype_coe
    (ReferenceTotalSourcePairCoupling.measurableSet_sourceStratumEvent rate rewards C_star C_h
      date control0 (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date))
  let embP (q : Fin (M p)) (v : Fin (date.val + 1)) :=
    ReferenceFirstLiveBranchIntegralTransport.measurableEmbedding_forgetBranch
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let embE (q : Fin (M p)) (v : Fin (date.val + 1)) :=
    ReferenceFirstLiveSourcePhasePartition.measurableEmbedding_forgetEmpty
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0
  let b (q : Fin (M p)) := (muB q).map
    (Subtype.val : BirthZ q → BootstrapPrivateRoundStreams.SourceInput p)
  let c (q : Fin (M p)) (v : Fin (date.val + 1)) :=
    (muP q v).map (ReferenceFirstLiveBranchIntegralTransport.forgetBranch
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
    (muE q v).map (ReferenceFirstLiveSourcePhasePartition.forgetEmpty
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0)
  have hbi (q : Fin (M p)) : Integrable (fun z : BirthZ q => g z.val) (muB q) := by
    have hmap : Integrable g (b q) := by
      change Integrable g ((muB q).map (Subtype.val : BirthZ q →
        BootstrapPrivateRoundStreams.SourceInput p))
      rw [ReferenceTotalSourceDisintegration.sourceStratumMeasure_map rate rewards C_star C_h
        date control0 (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date)]
      exact hg.integrableOn
    exact (embB q).integrable_map_iff.mp hmap
  have hpi (q : Fin (M p)) (v : Fin (date.val + 1)) :
      Integrable (fun z : PlusZ q v => g z.val.val) (muP q v) := by
    exact (ReferenceFirstLiveBranchIntegralTransport.integrableOn_originalBranch_iff
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 g).1
      hg.integrableOn
  have hei (q : Fin (M p)) (v : Fin (date.val + 1)) :
      Integrable (fun z : EmptyZ q v => g z.val.val) (muE q v) := by
    exact (ReferenceFirstLiveSourcePhasePartition.integrableOn_originalEmpty_iff
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 g).1
      hg.integrableOn
  have hbiMap (q : Fin (M p)) : Integrable g (b q) := (embB q).integrable_map_iff.mpr (hbi q)
  have hpiMap (q : Fin (M p)) (v : Fin (date.val + 1)) : Integrable g
      ((muP q v).map (ReferenceFirstLiveBranchIntegralTransport.forgetBranch
        rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0)) :=
    (embP q v).integrable_map_iff.mpr (hpi q v)
  have heiMap (q : Fin (M p)) (v : Fin (date.val + 1)) : Integrable g
      ((muE q v).map (ReferenceFirstLiveSourcePhasePartition.forgetEmpty
        rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0)) :=
    (embE q v).integrable_map_iff.mpr (hei q v)
  have hci (q : Fin (M p)) (v : Fin (date.val + 1)) : Integrable g (c q v) :=
    (hpiMap q v).add_measure (heiMap q v)
  have hbs : Integrable g (∑ q : Fin (M p), b q) :=
    integrable_finsetSum_measure.mpr (fun q _ => hbiMap q)
  have hcs (q : Fin (M p)) : Integrable g (∑ v : Fin (date.val + 1), c q v) :=
    integrable_finsetSum_measure.mpr (fun v _ => hci q v)
  have hcss : Integrable g (∑ q : Fin (M p), ∑ v : Fin (date.val + 1), c q v) :=
    integrable_finsetSum_measure.mpr (fun q _ => hcs q)
  have hz (i : Fin 6) (hi : i = 0 ∨ i = 1 ∨ i = 5) :
      g =ᵐ[(μ).restrict (phase i)] 0 := by
    filter_upwards [ae_restrict_mem
      (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
        rate rewards C_star C_h date control0 i)] with omega homega
    rcases hi with rfl | rfl | rfl
    · exact hzeroG omega (Or.inl homega)
    · exact hzeroG omega (Or.inr (Or.inl homega))
    · exact hzeroG omega (Or.inr (Or.inr homega))
  have h0 : Integrable g ((μ).restrict (phase 0)) :=
    (integrable_const (0 : ℝ)).congr (hz 0 (by simp)).symm
  have h1 : Integrable g ((μ).restrict (phase 1)) :=
    (integrable_const (0 : ℝ)).congr (hz 1 (by simp)).symm
  have h5 : Integrable g ((μ).restrict (phase 5)) :=
    (integrable_const (0 : ℝ)).congr (hz 5 (by simp)).symm
  have h01 := h0.add_measure h1
  have h015 := h01.add_measure h5
  have h015b := h015.add_measure hbs
  have hdecomp : μ = (μ).restrict (phase 0) + (μ).restrict (phase 1) + (μ).restrict (phase 5) +
      (∑ q : Fin (M p), b q) + ∑ q : Fin (M p), ∑ v : Fin (date.val + 1), c q v :=
    ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
      rate rewards C_star C_h date control0
  have hglobal :
      (∫ omega, g omega ∂μ) =
        (∑ q : Fin (M p), ∫ z : BirthZ q, g z.val ∂muB q) +
        ∑ q : Fin (M p), ∑ v : Fin (date.val + 1),
          ((∫ z : PlusZ q v, g z.val.val ∂muP q v) +
            ∫ z : EmptyZ q v, g z.val.val ∂muE q v) := by
    rw [hdecomp, integral_add_measure h015b hcss, integral_add_measure h015 hbs,
      integral_add_measure h01 h5, integral_add_measure h0 h1,
      integral_congr_ae (hz 0 (by simp)), integral_congr_ae (hz 1 (by simp)),
      integral_congr_ae (hz 5 (by simp))]
    simp only [Pi.zero_apply, integral_zero, zero_add]
    rw [integral_finsetSum_measure (fun q _ => hbiMap q),
      integral_finsetSum_measure (fun q _ => hcs q)]
    congr 1
    · apply Finset.sum_congr rfl
      intro q hq
      exact (embB q).integral_map g
    · apply Finset.sum_congr rfl
      intro q hq
      rw [integral_finsetSum_measure (fun v _ => hci q v)]
      apply Finset.sum_congr rfl
      intro v hv
      rw [integral_add_measure (hpiMap q v) (heiMap q v)]
      exact congrArg₂ (· + ·)
        ((embP q v).integral_map g) ((embE q v).integral_map g)
  have hDbirth (q : Fin (M p)) : MeasurableSet {z : BirthZ q | z.val.1.1 = ids} :=
    hD.preimage measurable_subtype_coe
  have hDbirth (q : Fin (M p)) :
      (∫ z : BirthZ q, g z.val ∂muB q) =
        ∫ z in {z : BirthZ q | z.val.1.1 = ids}, f z.val ∂muB q := by
    have hfun : (fun z : BirthZ q => g z.val) =
        ({z : BirthZ q | z.val.1.1 = ids}).indicator (fun z => f z.val) := by
      funext z
      simp only [g, Set.indicator, ReferenceFixedIDSourceSection.fixedIDSourceSection,
        Set.mem_ofPred_eq]
      by_cases h : z.val.1.1 = ids <;> simp [h]
    rw [hfun, integral_indicator (hDbirth q)]
  have hDplus (q : Fin (M p)) (v : Fin (date.val + 1)) :
      MeasurableSet {z : PlusZ q v | z.val.val.1.1 = ids} :=
    hD.preimage (measurable_subtype_coe.comp measurable_subtype_coe)
  have hDplusEq (q : Fin (M p)) (v : Fin (date.val + 1)) :
      (∫ z : PlusZ q v, g z.val.val ∂muP q v) =
        ∫ z in {z : PlusZ q v | z.val.val.1.1 = ids},
          f z.val.val ∂muP q v := by
    have hfun : (fun z : PlusZ q v => g z.val.val) =
        ({z : PlusZ q v | z.val.val.1.1 = ids}).indicator
          (fun z => f z.val.val) := by
      funext z
      simp only [g, Set.indicator, ReferenceFixedIDSourceSection.fixedIDSourceSection,
        Set.mem_ofPred_eq]
      by_cases h : z.val.val.1.1 = ids <;> simp [h]
    have hlocal : (∫ z : PlusZ q v, g z.val.val ∂muP q v) =
        ∫ z in {z : PlusZ q v | z.val.val.1.1 = ids}, f z.val.val ∂muP q v := by
      rw [hfun, integral_indicator (hDplus q v)]
    have htransport := ReferenceFirstLiveBranchIntegralTransport.integral_originalBranch
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 g
    calc
      _ = ∫ omega in ReferenceFirstLiveBranchIntegralTransport.originalBranchEvent
          rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          g omega ∂μ := htransport
      _ = _ := htransport.symm.trans hlocal
  have hDempty (q : Fin (M p)) (v : Fin (date.val + 1)) :
      MeasurableSet {z : EmptyZ q v | z.val.val.1.1 = ids} :=
    hD.preimage (measurable_subtype_coe.comp measurable_subtype_coe)
  have hDemptyEq (q : Fin (M p)) (v : Fin (date.val + 1)) :
      (∫ z : EmptyZ q v, g z.val.val ∂muE q v) =
        ∫ z in {z : EmptyZ q v | z.val.val.1.1 = ids},
          f z.val.val ∂muE q v := by
    have hfun : (fun z : EmptyZ q v => g z.val.val) =
        ({z : EmptyZ q v | z.val.val.1.1 = ids}).indicator
          (fun z => f z.val.val) := by
      funext z
      simp only [g, Set.indicator, ReferenceFixedIDSourceSection.fixedIDSourceSection,
        Set.mem_ofPred_eq]
      by_cases h : z.val.val.1.1 = ids <;> simp [h]
    have hlocal : (∫ z : EmptyZ q v, g z.val.val ∂muE q v) =
        ∫ z in {z : EmptyZ q v | z.val.val.1.1 = ids}, f z.val.val ∂muE q v := by
      rw [hfun, integral_indicator (hDempty q v)]
    have htransport := ReferenceFirstLiveSourcePhasePartition.integral_originalEmpty
      rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 g
    calc
      _ = ∫ omega in ReferenceFirstLiveSourcePhasePartition.originalEmptyEvent
          rate rewards C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0,
          g omega ∂μ := htransport
      _ = _ := htransport.symm.trans hlocal
  rw [← integral_indicator hD]
  rw [hglobal]
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    exact hDbirth q
  · apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro v hv
    rw [hDplusEq, hDemptyEq]

end OriginalSourceAssembly

include control0 in
/-- The actual first-LIVE calendar rounding comparison on one literal
fixed-ID section of the original source law. -/
public theorem integral_fixedID_calendarRoundedGap_le_raw_add_floor
    (date : Fin p.T) (comparator : ProductSetLaw.ProductSet p.K p.m) :
    (∫ omega in Dset,
      calendarRoundedGap rate rewards C_star C_h date comparator omega ∂μ) ≤
      (∫ omega in Dset,
        calendarRawGap rate rewards C_star C_h date comparator omega ∂μ) +
      ∫ omega in Dset,
        calendarFloorLoss rate rewards C_star C_h date comparator omega ∂μ := by
  let fR := calendarRoundedGap rate rewards C_star C_h date comparator
  let fA := calendarRawGap rate rewards C_star C_h date comparator
  let fF := calendarFloorLoss rate rewards C_star C_h date comparator
  have hRint := ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRoundedGap
    rate rewards C_star C_h date comparator control0
  have hAint := ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarRawGap
    rate rewards C_star C_h date comparator control0
  have hFint := ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
    rate rewards C_star C_h date comparator control0
  have hzero (f : BootstrapPrivateRoundStreams.SourceInput p → ℝ)
      (hf : f = fR ∨ f = fA ∨ f = fF) :
      ∀ omega, omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase
          rate rewards C_star C_h date 0 ∨
        omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h date 1 ∨
        omega ∈ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h date 5 →
        f omega = 0 := by
    intro omega hphase
    rcases hf with rfl | rfl | rfl
    · exact (live_observer_zero_on_exception (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0)
        (date := date) comparator omega hphase).1
    · exact (live_observer_zero_on_exception (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0)
        (date := date) comparator omega hphase).2.1
    · exact (live_observer_zero_on_exception (rate := rate) (rewards := rewards)
        (C_star := C_star) (C_h := C_h) (control0 := control0)
        (date := date) comparator omega hphase).2.2
  have hR := integral_fixedID_components (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) (ids := ids)
    (date := date) fR hRint (hzero fR (Or.inl rfl))
  have hA := integral_fixedID_components (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) (ids := ids)
    (date := date) fA hAint (hzero fA (Or.inr (Or.inl rfl)))
  have hF := integral_fixedID_components (rate := rate) (rewards := rewards)
    (C_star := C_star) (C_h := C_h) (control0 := control0) (ids := ids)
    (date := date) fF hFint (hzero fF (Or.inr (Or.inr rfl)))
  have hB (q : Fin (M p)) :
      (∫ z in {z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h date
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date) |
            z.val.1.1 = ids},
        fR z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h
          date (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date)) ≤
      (∫ z in {z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h date
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date) |
            z.val.1.1 = ids},
        fA z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h
          date (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date)) +
      ∫ z in {z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h date
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date) |
            z.val.1.1 = ids},
        fF z.val ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h
          date (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q date) := by
    simpa only [fR, fA, fF] using
      fixedID_birth_local (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) (ids := ids) (q := q) (t := date) comparator
  have hP (q : Fin (M p)) (v : Fin (date.val + 1)) :
      (∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 | z.val.val.1.1 = ids},
        fR z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards
          C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0) ≤
      (∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 | z.val.val.1.1 = ids},
        fA z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards
          C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
      ∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 | z.val.val.1.1 = ids},
        fF z.val.val ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards
          C_star C_h q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 := by
    simpa only [fR, fA, fF] using
      fixedID_nonempty_local (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) (ids := ids) (q := q) (t := date)
        (s := v.val) (hs := Nat.lt_succ_iff.mp v.isLt) comparator
  have hE (q : Fin (M p)) (v : Fin (date.val + 1)) :
      (∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 | z.val.val.1.1 = ids},
        fR z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0) ≤
      (∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 | z.val.val.1.1 = ids},
        fA z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0) +
      ∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 | z.val.val.1.1 = ids},
        fF z.val.val ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h
          q date v.val (Nat.lt_succ_iff.mp v.isLt) control0 := by
    simpa only [fR, fA, fF] using
      fixedID_empty_local (rate := rate) (rewards := rewards) (C_star := C_star)
        (C_h := C_h) (control0 := control0) (ids := ids) (q := q) (t := date)
        (s := v.val) (hs := Nat.lt_succ_iff.mp v.isLt) comparator
  rw [hR, hA, hF]
  have hBirth := Finset.sum_le_sum (s := Finset.univ) (fun q hq => hB q)
  rw [Finset.sum_add_distrib] at hBirth
  have hBranches := Finset.sum_le_sum (s := Finset.univ) (fun q hq =>
    Finset.sum_le_sum (s := Finset.univ) (fun v hv => add_le_add (hP q v) (hE q v)))
  simp_rw [Finset.sum_add_distrib] at hBirth hBranches ⊢
  linarith [hBirth, hBranches]

end Bandits.Support.ReferenceFirstLiveFixedIDCalendarRoundedComparison
