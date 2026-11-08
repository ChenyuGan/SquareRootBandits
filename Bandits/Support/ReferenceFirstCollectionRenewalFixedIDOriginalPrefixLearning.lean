/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting
public import Bandits.Support.ReferenceFirstCollectionFixedIDOutgoingWeightedEnergyBudget
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget
public import Bandits.Support.ReferenceFirstCollectionFixedIDOriginalPrefixRoundedLearning

import Mathlib.Tactic

/-!
# Original first-renewal learning on every literal fixed-ID source law

This module assembles the actual first-renewal endpoint bounds on the
unrestricted original-source fixed-ID section.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalPrefixLearning

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)
  (S : ProductSetLaw.ProductSet p.K p.m)

local notation "Z" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "ν" => ReferenceFixedIDSourceSection.fixedIDSourceLaw ids
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "B" =>
  Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
    16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
    (p.m : ℝ) / (16 * rate.eta.val)
local notation "c" => CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
local notation "cFloor" => (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))

private local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private local instance sourceInputProbability : IsProbabilityMeasure (sourceInputLaw p) :=
  BootstrapPrivateRoundStreams.sourceInputLaw_probability p

private abbrev renewalCallEvent (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
    rate rewards C_star C_h u t

private theorem zeroExtendCell_eq_indicator {α : Type*} [MeasurableSpace α]
    (A : Set α) (f : {x // x ∈ A} → ℝ) (x : α) :
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f x =
      A.indicator
        (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f) x := by
  classical
  by_cases hx : x ∈ A
  · simp only [Set.indicator_of_mem hx]
  · have hno : ¬ ∃ y : {x // x ∈ A}, (y : α) = x := by
      rintro ⟨y, hy⟩
      exact hx (hy ▸ y.property)
    simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
      Set.indicator_of_notMem hx, Function.extend_apply', hno]

private theorem zeroExtendCell_integrable {α : Type*} [MeasurableSpace α]
    (A : Set α) (hA : MeasurableSet A) (f : {x // x ∈ A} → ℝ)
    (μ0 : Measure α)
    (hf : Integrable f (μ0.comap (Subtype.val : {x // x ∈ A} → α))) :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f) μ0 := by
  have hcomp : Integrable
      (fun x : {x // x ∈ A} =>
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f x.val)
      (μ0.comap (Subtype.val : {x // x ∈ A} → α)) := by
    have heq :
        (fun x : {x // x ∈ A} =>
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f x.val) = f := by
      funext x
      exact Subtype.val_injective.extend_apply f (fun _ => 0) x
    rw [heq]
    exact hf
  have hOn : IntegrableOn
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f) A μ0 :=
    (integrableOn_iff_comap_subtypeVal hA).2 hcomp
  have heq :
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f =
        A.indicator
          (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f) := by
    funext x
    exact zeroExtendCell_eq_indicator A f x
  rw [heq]
  exact (integrable_indicator_iff hA).2 hOn

private theorem zeroExtendCell_integrable_on_source
    (u t : Fin p.T)
    (f : renewalCallEvent rate rewards C_star C_h u t → ℝ)
    (hf : Integrable f
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t)) :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) f) μ := by
  apply zeroExtendCell_integrable
    (renewalCallEvent rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t) f μ
  simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw] using hf

include control0 S

private theorem rawCellIncrement_integrable (u t : Fin p.T) :
    Integrable
      (fun z : renewalCallEvent rate rewards C_star C_h u t =>
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
            rate rewards C_star C_h u t S z)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S).2.1.add
    (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGapTotal
      rate rewards C_star C_h u t control0 S)

private theorem arrivalCellIncrement_integrable (u t : Fin p.T) :
    Integrable
      (fun z : renewalCallEvent rate rewards C_star C_h u t =>
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
            rate rewards C_star C_h u t z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
            rate rewards C_star C_h u t z)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S).1.add
    (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservationTotal
      rate rewards C_star C_h u t control0)

private theorem roundedCellIncrement_integrable (u t : Fin p.T) :
    Integrable
      (fun z : renewalCallEvent rate rewards C_star C_h u t =>
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
            rate rewards C_star C_h u t S z)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S).2.2.add
    (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureRewardComparatorGapTotal
      rate rewards C_star C_h u t control0 S)

omit control0 S in
private theorem zeroExtendSum_eq_cell
    (f : (u t : Fin p.T) →
      ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t → ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ renewalCallEvent rate rewards C_star C_h u t) :
    (∑ u' : Fin p.T, ∑ t' : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u' t') (f u' t')) z =
      f u t ⟨z, hz⟩ := by
  classical
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]
  · rw [Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_univ _)]
    · simpa [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell] using
        (Subtype.val_injective.extend_apply (f u t) (fun _ => 0) ⟨z, hz⟩)
    · intro t' ht' hne
      have hd := ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEvents_disjoint
        rate rewards C_star C_h u t u t' (by
          intro h
          exact hne (congrArg Prod.snd h.symm))
      have hz' : z ∉ renewalCallEvent rate rewards C_star C_h u t' := by
        intro hz'
        exact (Set.disjoint_left.mp hd hz hz').elim
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell, hz']
  · intro u' hu' hune
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro t' ht'
    by_cases hne : (u, t) = (u', t')
    · exact (hune (congrArg Prod.fst hne.symm)).elim
    · have hd := ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEvents_disjoint
        rate rewards C_star C_h u t u' t' hne
      have hz' : z ∉ renewalCallEvent rate rewards C_star C_h u' t' := by
        intro hz'
        exact (Set.disjoint_left.mp hd hz hz').elim
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell, hz']

include control0 S

private theorem originalExtendedRawGap_integrable :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
  apply (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable
      rate rewards C_star C_h control0 S).add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _
    (rawCellIncrement_integrable rate rewards C_star C_h control0 S u t)

private theorem originalExtendedWeightedArrival_integrable :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
        rate rewards C_star C_h) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
  apply (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_integrable
      rate rewards C_star C_h control0).add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _
    (arrivalCellIncrement_integrable rate rewards C_star C_h control0 S u t)

private theorem originalExtendedRoundedGap_integrable :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
        rate rewards C_star C_h S) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
  apply (ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRoundedGap_integrable
      rate rewards C_star C_h control0 S).add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _
    (roundedCellIncrement_integrable rate rewards C_star C_h control0 S u t)

omit S in
private theorem originalExtendedCost_integrable :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
        rate rewards C_star C_h) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
  exact (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_integrable
      rate rewards C_star C_h control0).add
    (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog_integrable
      rate rewards C_star C_h control0)

omit control0 in
private theorem originalExtendedObservations_eq_endpoint
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S z.val =
        ReferenceFirstCollectionRenewalRawPotential.endpointRawGap
          rate rewards C_star C_h u t S z ∧
    ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
        rate rewards C_star C_h z.val =
        ReferenceFirstCollectionRenewalRawPotential.endpointWeightedArrival
          rate rewards C_star C_h u t z := by
  have h := ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedObservations_eq_endpoint
    rate rewards C_star C_h S u t z
  exact ⟨h.1, h.2.1⟩

omit control0 S in
private theorem originalAfterCallBacklog_eq_cell
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
        rate rewards C_star C_h z.val =
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t z := by
  cases z with
  | mk x hx =>
    change (∑ u' : Fin p.T, ∑ t' : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u' t')
        (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
          rate rewards C_star C_h u' t') x) =
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t ⟨x, hx⟩
    simpa only [Finset.sum_apply] using zeroExtendSum_eq_cell rate rewards C_star C_h
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t) u t x hx

omit control0 in
private theorem originalExtendedRawGap_pointwise (z : SourceInput p) :
    ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S z ≤
      B + 8 * rate.eta.val *
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
            rate rewards C_star C_h z +
          ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
            rate rewards C_star C_h z) := by
  classical
  by_cases hex : ∃ u t : Fin p.T, z ∈ renewalCallEvent rate rewards C_star C_h u t
  · obtain ⟨u, t, hz⟩ := hex
    let w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t := ⟨z, hz⟩
    have heval := originalExtendedObservations_eq_endpoint rate rewards C_star C_h S u t w
    have hcost := originalAfterCallBacklog_eq_cell rate rewards C_star C_h u t w
    have hendpoint := ReferenceFirstCollectionRenewalRawPotential.endpointRawGap_le_horizon_cost_and_arrival
      rate rewards C_star C_h u t S w
    simpa [w, ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost,
      heval.1, heval.2, hcost] using hendpoint
  · have hnone : ∀ u t : Fin p.T, z ∉ renewalCallEvent rate rewards C_star C_h u t := by
      intro u t hz
      exact hex ⟨u, t, hz⟩
    have hzero : ∀ u t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
              rate rewards C_star C_h u t =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                rate rewards C_star C_h u t S w +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                rate rewards C_star C_h u t S w) z = 0 := by
      intro u t
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        hnone u t]
    have hwzero : ∀ u t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
              rate rewards C_star C_h u t =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
                rate rewards C_star C_h u t w +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
                rate rewards C_star C_h u t w) z = 0 := by
      intro u t
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        hnone u t]
    have hback :
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
          rate rewards C_star C_h z = 0 := by
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell, hnone]
    have hraw := ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap_le
      rate rewards C_star C_h S z
    have hcorr := ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection_le
      rate rewards C_star C_h z
    have hraw' :
        ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
            rate rewards C_star C_h S z =
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z := by
      simp [ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap, hzero]
    have hw' :
        ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
            rate rewards C_star C_h z =
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z := by
      simp [ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival, hwzero]
    rw [hraw', hw', ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost, hback]
    linarith

omit control0 S in
/-- The localized first-invocation mass charged by all pre-renewal calendar
gates, with the retained first call kept in its literal source event. -/
public def fixedIDPreGateMass : ℝ :=
  ∑ t : Fin p.T,
    ((μ).real (D ∩
        (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
          ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
      (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
        rate rewards C_star C_h t) +
      ∑ u : Fin p.T, (μ).real (D ∩
        ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t))

omit control0 S in
private theorem fixedIDAfterCallGateMass_eq_post :
    ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDAfterCallGateMass
        rate rewards C_star C_h ids =
      ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
        rate rewards C_star C_h ids := by
  classical
  simp only [ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDAfterCallGateMass,
    ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDCellAfterCallGateMass,
    ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass,
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass,
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass,
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMassAt,
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection]
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg₂ (fun x y : ℝ => x + y)
    (by simp [ReferenceFirstCollectionRenewalNextDateWeightedEnergyStep.retainedNextDate])
    (by
      apply Finset.sum_congr rfl
      intro n hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hfuture : t.val + 1 < n := by omega
      simp [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
        hhi, hfuture])

omit control0 S in
private theorem fixedIDFutureGateMass_fin_eq (u t : Fin p.T) :
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids ∩
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
            rate rewards C_star C_h u t q.val)) =
      ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
        rate rewards C_star C_h u t ids := by
  classical
  by_cases hnext : t.val + 1 < p.T
  · let g : ℕ → ℝ := fun n =>
      if hn : n < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
            rate rewards C_star C_h u t ids ∩
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
              rate rewards C_star C_h u t n)
      else 0
    have hrange :
        (∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
              rate rewards C_star C_h u t ids ∩
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t q.val)) =
          ∑ n ∈ Finset.range p.T, g n := by
      calc
        _ = ∑ q : Fin p.T, g q.val := by
          apply Finset.sum_congr rfl
          intro q hq
          simp only [g, dite_eq_left q.isLt]
        _ = _ := Fin.sum_univ_eq_sum_range g p.T
    have hzeroPrefix : ∑ n ∈ Finset.range (t.val + 2), g n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnt : n < t.val + 2 := Finset.mem_range.mp hn
      by_cases hlt : n < p.T
      · have hfuture : ¬ t.val + 1 < n := by omega
        simp [g, hlt, ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt,
          hfuture]
      · simp [g, hlt]
    have hsplit := Finset.sum_range_add_sum_Ico g (by omega : t.val + 2 ≤ p.T)
    have htail :
        (∑ n ∈ Finset.Ico (t.val + 2) p.T, g n) =
          ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
            rate rewards C_star C_h u t ids := by
      unfold ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
      apply Finset.sum_congr rfl
      intro n hn
      rcases Finset.mem_Ico.mp hn with ⟨hlo, hhi⟩
      have hfuture : t.val + 1 < n := by omega
      simp [ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMassAt,
        g, hhi, hfuture,
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt]
    calc
      _ = ∑ n ∈ Finset.range p.T, g n := hrange
      _ = ∑ n ∈ Finset.Ico (t.val + 2) p.T, g n := by
        rw [← hsplit, hzeroPrefix]
        simp
      _ = _ := htail
  · have hIco : Finset.Ico (t.val + 2) p.T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      have hn' := Finset.mem_Ico.mp hn
      omega
    have hfuture : ∀ q : Fin p.T,
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
          rate rewards C_star C_h u t q.val = ∅ := by
      intro q
      unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
      rw [dite_eq_left q.isLt]
      have hno : ¬ t.val + 1 < q.val := by omega
      rw [dite_eq_right hno]
    simp [ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass,
      ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMassAt,
      ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates,
      hIco, hfuture]

omit control0 S in
private theorem localizedPostGateDateSum_eq_post :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ((if hnext : t.val + 1 < p.T then
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
              rate rewards C_star C_h u t ids ∩
              ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext)
        else 0) +
        ∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
              rate rewards C_star C_h u t ids ∩
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t q.val))) =
      ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
        rate rewards C_star C_h ids := by
  unfold ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro t ht
  exact congrArg₂ (fun x y : ℝ => x + y)
    (by simp [ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass,
      ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection])
    (fixedIDFutureGateMass_fin_eq rate rewards C_star C_h ids u t)

omit S in
/-- The exact fixed-ID source-date mass budget jointly charges all retained
first-call gates and the renewal next/future gates against one source horizon. -/
public theorem fixedIDJointCalendarMass_le_horizon :
    fixedIDPreGateMass rate rewards C_star C_h ids +
        ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
          rate rewards C_star C_h ids ≤
      (p.T : ℝ) * (μ).real D := by
  let phase234 := fun t : Fin p.T =>
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4
  let oldGate := fun t : Fin p.T =>
    ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t
  let currentGate := fun u t : Fin p.T =>
    ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
  have hret :=
    ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget.localized_retainedFirstCall_real_eq_sum
      rate rewards C_star C_h ids control0
  have hret' :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (μ).real (D ∩ currentGate u t)) =
        (μ).real (D ∩
          ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) := by
    simpa [currentGate] using hret
  have hpost :=
    ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget.localized_postGate_total_eq_next_future
      rate rewards C_star C_h ids
  have hAtoM := fixedIDAfterCallGateMass_eq_post rate rewards C_star C_h ids
  have hpre : fixedIDPreGateMass rate rewards C_star C_h ids =
      (Finset.univ.sum fun t : Fin p.T =>
        (μ).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
          (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t)) +
        (μ).real (D ∩
          ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) := by
    let a : Fin p.T → ℝ := fun t => (μ).real (D ∩ phase234 t)
    let b : Fin p.T → ℝ := fun t => (μ).real (D ∩ oldGate t)
    let d : Fin p.T → ℝ := fun t => ∑ u : Fin p.T, (μ).real (D ∩ currentGate u t)
    dsimp [fixedIDPreGateMass]
    change fixedIDPreGateMass rate rewards C_star C_h ids =
      (Finset.univ.sum fun t : Fin p.T => a t + b t) +
        (μ).real (D ∩
          ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h)
    calc
      _ = (Finset.univ.sum fun t : Fin p.T => a t + b t) +
          Finset.univ.sum (fun t : Fin p.T => d t) := by
        dsimp [fixedIDPreGateMass]
        change Finset.univ.sum (fun t : Fin p.T => (a t + b t) + d t) = _
        rw [Finset.sum_add_distrib]
      _ = (Finset.univ.sum fun t : Fin p.T => a t + b t) +
          Finset.univ.sum (fun u : Fin p.T =>
            Finset.univ.sum (fun t : Fin p.T => (μ).real (D ∩ currentGate u t))) := by
        congr 1
        exact Finset.sum_comm
      _ = _ := by rw [hret']
  have h :=
    ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget.localized_sum_sourceDateMass_le_horizon
      rate rewards C_star C_h ids control0
  have hpostA :
      (∑ q : Fin p.T, ∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget.renewalIDSection
            rate rewards C_star C_h ids u t ∩
            ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate
              rate rewards C_star C_h u t q)) =
        ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDAfterCallGateMass
          rate rewards C_star C_h ids := by
    rw [hpost]
    exact (localizedPostGateDateSum_eq_post rate rewards C_star C_h ids).trans hAtoM.symm
  have h' :
      ((Finset.univ.sum fun t : Fin p.T =>
        (μ).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
          (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t)) +
        (μ).real (D ∩
          ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h)) +
        ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDAfterCallGateMass
          rate rewards C_star C_h ids ≤ (p.T : ℝ) * (μ).real D := by
    have h'' := h
    rw [← hpost, hpostA] at h''
    simpa only [phase234, oldGate] using h''
  rw [hpre, ← hAtoM]
  exact h'

omit control0 S in
private theorem originalTerminalEnergy_nonneg (z : SourceInput p) :
    0 ≤ ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
      rate rewards C_star C_h z := by
  unfold ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  by_cases hz : z ∈ renewalCallEvent rate rewards C_star C_h u t
  · have hval :
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t) z =
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
          rate rewards C_star C_h u t ⟨z, hz⟩ := by
      simpa [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell] using
        (Subtype.val_injective.extend_apply
          (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t) (fun _ => 0) ⟨z, hz⟩)
    rw [hval]
    exact ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy_nonneg
      rate rewards C_star C_h u t ⟨z, hz⟩
  · simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell, hz]

omit control0 S in
private theorem originalSupportLoss_nonneg (z : SourceInput p) :
    0 ≤ ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
      rate rewards C_star C_h z := by
  unfold ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  by_cases hz : z ∈ renewalCallEvent rate rewards C_star C_h u t
  · have hval :
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t) z =
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
          rate rewards C_star C_h u t ⟨z, hz⟩ := by
      simpa [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell] using
        (Subtype.val_injective.extend_apply
          (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t) (fun _ => 0) ⟨z, hz⟩)
    rw [hval]
    exact ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_nonneg
      rate rewards C_star C_h u t ⟨z, hz⟩
  · simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell, hz]

omit S in
public theorem integral_originalExtendedCost_fixedID_cylinder_le :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
        rate rewards C_star C_h z ∂μ) ≤
      ((2 / 11 : ℝ) * CanonicalRecordingRates.R p + 3 * (p.m : ℝ)) *
        (p.T : ℝ) * (μ).real D := by
  have hpre :=
    ReferenceFirstCollectionFixedIDOutgoingWeightedEnergyBudget.fixedIDOutgoingEnergyBudget
      rate rewards C_star C_h control0 ids
  have hpost :=
    ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDAfterCallOriginalEnergyBudget
      rate rewards C_star C_h ids control0
  rw [fixedIDAfterCallGateMass_eq_post rate rewards C_star C_h ids] at hpost
  have hmass := fixedIDJointCalendarMass_le_horizon rate rewards C_star C_h control0 ids
  have hpre' :
      (∫ z in D,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus rate rewards C_star C_h z ∂μ) +
      (11 / 2 : ℝ) *
        (∫ z in D,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
            rate rewards C_star C_h z ∂μ) ≤ c * fixedIDPreGateMass rate rewards C_star C_h ids := by
    simpa [fixedIDPreGateMass] using hpre
  have hpost' :
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
      c * ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
          rate rewards C_star C_h ids +
        ∫ z in D,
          ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus rate rewards C_star C_h z ∂μ := by
    simpa [ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDAfterCallGateMass,
      ReferenceFirstCollectionRenewalFixedIDWeightedCalendarAccounting.fixedIDCellAfterCallGateMass] using hpost
  have hterminal :
      0 ≤ ∫ z in D,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalTerminalEnergy
          rate rewards C_star C_h z ∂μ :=
    integral_nonneg (fun z => originalTerminalEnergy_nonneg rate rewards C_star C_h z)
  have hloss :
      0 ≤ ∫ z in D,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalSupportLoss
          rate rewards C_star C_h z ∂μ :=
    integral_nonneg (fun z => originalSupportLoss_nonneg rate rewards C_star C_h z)
  have henergy :
      (11 / 2 : ℝ) *
          ((∫ z in D,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z ∂μ) +
            ∫ z in D,
              ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
                rate rewards C_star C_h z ∂μ) ≤
        c * (fixedIDPreGateMass rate rewards C_star C_h ids +
          ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
            rate rewards C_star C_h ids) := by
    linarith [hpre', hpost', hterminal, hloss]
  have hR : 0 ≤ CanonicalRecordingRates.R p := by
    rw [CanonicalRecordingRates.R]
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
    have hK : 0 < (p.K : ℝ) := by exact_mod_cast ConstructorDimensions.K_pos p
    nlinarith
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  have hc : 0 ≤ c := add_nonneg hR (mul_nonneg (by norm_num) hm)
  have hjoint := mul_le_mul_of_nonneg_left hmass hc
  have hcostsum :
      (11 / 2 : ℝ) *
          ((∫ z in D,
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
                rate rewards C_star C_h z ∂μ) +
            ∫ z in D,
              ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
                rate rewards C_star C_h z ∂μ) ≤ c * ((p.T : ℝ) * (μ).real D) :=
    henergy.trans hjoint
  have hcostIntegral :
      (∫ z in D,
        ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
          rate rewards C_star C_h z ∂μ) =
      (∫ z in D,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
          rate rewards C_star C_h z ∂μ) +
        ∫ z in D,
          ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
            rate rewards C_star C_h z ∂μ := by
    unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
    exact integral_add
      (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_integrable
        rate rewards C_star C_h control0).integrableOn
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog_integrable
        rate rewards C_star C_h control0).integrableOn
  rw [← hcostIntegral] at hcostsum
  have hcoef : (2 / 11 : ℝ) * c =
      (2 / 11 : ℝ) * CanonicalRecordingRates.R p + 3 * (p.m : ℝ) := by
    ring
  calc
    _ = (2 / 11 : ℝ) *
        ((11 / 2 : ℝ) *
          (∫ z in D,
            ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
              rate rewards C_star C_h z ∂μ)) := by ring
    _ ≤ (2 / 11 : ℝ) * (c * ((p.T : ℝ) * (μ).real D)) :=
      mul_le_mul_of_nonneg_left hcostsum (by norm_num)
    _ = ((2 / 11 : ℝ) * c) * ((p.T : ℝ) * (μ).real D) := by ring
    _ = _ := by rw [hcoef]; ring

omit S in
private theorem firstInvocationWeightedArrival_fixedID_preMass_le :
    (∫ z in D,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h z ∂μ) ≤
      (p.m : ℝ) * fixedIDPreGateMass rate rewards C_star C_h ids := by
  let W := ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
    rate rewards C_star C_h
  have hsum (z : SourceInput p) :
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
          rate rewards C_star C_h z = ∑ t : Fin p.T, W t z := by
    rw [ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_eq_calendar]
    rfl
  have hdate (t : Fin p.T) :
      (∫ z in D, W t z ∂μ) ≤
        (p.m : ℝ) * ((μ).real (D ∩
            (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
          (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (μ).real (D ∩
            ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
    have hLive := ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_liveCalendarWeightedArrival_setIntegral_le
      rate rewards C_star C_h control0 ids t
    have hLiveInt := (ReferenceFirstLiveOriginalCalendarArrivalMoments.calendarWeightedArrival_moments
      rate rewards C_star C_h t control0).1
    change Integrable
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
        rate rewards C_star C_h t) μ at hLiveInt
    have hRestInt :=
      (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival_integrable
        rate rewards C_star C_h control0 t).add
        (integrable_finsetSum Finset.univ (fun u _ =>
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival_integrable
            rate rewards C_star C_h control0 u t))
    have hRest := ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_oldCurrentCalendarWeightedArrival_setIntegral_le
      rate rewards C_star C_h control0 ids t
    change (∫ z in D,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
          rate rewards C_star C_h t z +
        (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
            rate rewards C_star C_h t z +
          ∑ u : Fin p.T,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
              rate rewards C_star C_h u t z) ∂μ) ≤ _
    have hAdd :
        (∫ z in D,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
              rate rewards C_star C_h t z +
            (ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
                rate rewards C_star C_h t z +
              ∑ u : Fin p.T,
                ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
                  rate rewards C_star C_h u t z) ∂μ) =
          (∫ z in D,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
              rate rewards C_star C_h t z ∂μ) +
          ∫ z in D,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
                rate rewards C_star C_h t z +
              ∑ u : Fin p.T,
                ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
                  rate rewards C_star C_h u t z ∂μ := by
      change (∫ z, (fun z =>
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
          rate rewards C_star C_h t z) z + (fun z =>
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
            rate rewards C_star C_h t z +
          ∑ u : Fin p.T,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
              rate rewards C_star C_h u t z) z ∂((sourceInputLaw p).restrict D)) = _
      exact integral_add hLiveInt.integrableOn hRestInt.integrableOn
    rw [hAdd]
    have hLive' := hLive
    have hRest' := hRest
    change (∫ z in D,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.liveCalendarWeightedArrival
        rate rewards C_star C_h t z ∂μ) ≤
        (p.m : ℝ) * (μ).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) at hLive'
    change (∫ z in D,
      ReferenceFirstCollectionOriginalWeightedArrivalBudget.oldCalendarWeightedArrival
          rate rewards C_star C_h t z +
        ∑ u : Fin p.T,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.currentCalendarWeightedArrival
            rate rewards C_star C_h u t z ∂μ) ≤
        (p.m : ℝ) * ((μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (μ).real (D ∩
            ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) at hRest'
    calc
      _ ≤ _ := add_le_add hLive' hRest'
      _ = _ := by ring
  calc
    _ = ∫ z in D, (∑ t : Fin p.T, W t z) ∂μ := by
      apply setIntegral_congr_fun (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
      intro z hz
      exact hsum z
    _ = ∑ t : Fin p.T, ∫ z in D, W t z ∂μ := by
      exact integral_finsetSum Finset.univ (fun t _ =>
        (ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival_integrable
          rate rewards C_star C_h control0 t).integrableOn)
    _ ≤ ∑ t : Fin p.T,
        (p.m : ℝ) * ((μ).real (D ∩
            (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
              ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
          (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h t) +
          ∑ u : Fin p.T, (μ).real (D ∩
            ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) :=
      Finset.sum_le_sum (fun t _ => hdate t)
    _ = _ := by
      simp only [fixedIDPreGateMass, Finset.mul_sum]

public theorem integral_originalExtendedWeightedArrival_fixedID_cylinder_le_horizon :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
        rate rewards C_star C_h z ∂μ) ≤
      (p.m : ℝ) * (p.T : ℝ) * (μ).real D := by
  have hpre := firstInvocationWeightedArrival_fixedID_preMass_le
    rate rewards C_star C_h control0 ids
  have hinc :=
    ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.integral_originalExtendedWeightedArrival_sub_firstInvocation_fixedID
      rate rewards C_star C_h control0 S ids
  have hext := originalExtendedWeightedArrival_integrable
    rate rewards C_star C_h control0 S
  have hbase := ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_integrable
    rate rewards C_star C_h control0
  have hdiff :
      (∫ z in D,
        ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
          rate rewards C_star C_h z ∂μ) =
        (∫ z in D,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z ∂μ) +
          ∫ z in D,
            (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
                rate rewards C_star C_h z -
              ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
                rate rewards C_star C_h z) ∂μ := by
    rw [integral_sub hext.integrableOn hbase.integrableOn]
    ring
  have hmass := fixedIDJointCalendarMass_le_horizon rate rewards C_star C_h control0 ids
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  calc
    _ = _ := hdiff
    _ ≤ (p.m : ℝ) * fixedIDPreGateMass rate rewards C_star C_h ids +
        (p.m : ℝ) * ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
          rate rewards C_star C_h ids := add_le_add hpre hinc.2
    _ = (p.m : ℝ) *
        (fixedIDPreGateMass rate rewards C_star C_h ids +
          ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
            rate rewards C_star C_h ids) := by ring
    _ ≤ (p.m : ℝ) * ((p.T : ℝ) * (μ).real D) :=
      mul_le_mul_of_nonneg_left hmass hm
    _ = _ := by ring

private theorem integral_originalExtendedRawGap_fixedID_cylinder_le_horizon :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S z ∂μ) ≤
      (μ).real D *
        (B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ)) := by
  let f := ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
    rate rewards C_star C_h S
  let g := ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedCost
    rate rewards C_star C_h
  let w := ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
    rate rewards C_star C_h
  have hf := originalExtendedRawGap_integrable rate rewards C_star C_h control0 S
  have hg := originalExtendedCost_integrable rate rewards C_star C_h control0
  have hw := originalExtendedWeightedArrival_integrable rate rewards C_star C_h control0 S
  have hmajor : Integrable (fun z : SourceInput p => B + 8 * rate.eta.val * (g z + w z)) μ :=
    (integrable_const B).add ((hg.add hw).const_mul (8 * rate.eta.val))
  have hpoint : ∀ z, f z ≤ B + 8 * rate.eta.val * (g z + w z) :=
    originalExtendedRawGap_pointwise rate rewards C_star C_h S
  have hcost := integral_originalExtendedCost_fixedID_cylinder_le
    rate rewards C_star C_h control0 ids
  have harrival := integral_originalExtendedWeightedArrival_fixedID_cylinder_le_horizon
    rate rewards C_star C_h control0 ids S
  calc
    _ ≤ ∫ z in D, B + 8 * rate.eta.val * (g z + w z) ∂μ :=
      integral_mono hf.integrableOn hmajor.integrableOn hpoint
    _ = B * (μ).real D +
        8 * rate.eta.val *
          ((∫ z in D, g z ∂μ) + ∫ z in D, w z ∂μ) := by
      have hB : (∫ z in D, B ∂μ) = B * (μ).real D := by
        simp only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ]
        ring
      calc
        _ = (∫ z in D, B ∂μ) +
            ∫ z in D, 8 * rate.eta.val * (g z + w z) ∂μ := by
          change (∫ z, (fun _ : SourceInput p => B) z +
            (fun z => 8 * rate.eta.val * (g z + w z)) z
              ∂((sourceInputLaw p).restrict D)) = _
          exact integral_add (integrable_const B).integrableOn
            (((hg.add hw).const_mul (8 * rate.eta.val)).integrableOn)
        _ = _ := by rw [hB, integral_const_mul, integral_add hg.integrableOn hw.integrableOn]
    _ ≤ B * (μ).real D +
        8 * rate.eta.val *
          ((((2 / 11 : ℝ) * CanonicalRecordingRates.R p + 3 * (p.m : ℝ)) +
              (p.m : ℝ)) * (p.T : ℝ) * (μ).real D) := by
      have hs := add_le_add hcost harrival
      have hscale : 0 ≤ 8 * rate.eta.val :=
        mul_nonneg (by norm_num) rate.eta.property.le
      have hscaled := mul_le_mul_of_nonneg_left hs hscale
      calc
        _ = B * (μ).real D +
            8 * rate.eta.val *
              ((∫ z in D, g z ∂μ) + ∫ z in D, w z ∂μ) := rfl
        _ ≤ _ := add_le_add_right hscaled (B * (μ).real D)
        _ = _ := by ring
    _ = _ := by ring

public theorem integral_originalExtendedRawGap_fixedID_le_horizon :
    (∫ z,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S z ∂ν) ≤
      B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
        rate.eta.val * (p.T : ℝ) := by
  have hLocal := integral_originalExtendedRawGap_fixedID_cylinder_le_horizon
    rate rewards C_star C_h control0 ids S
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
    (p := p) ids
    (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
      rate rewards C_star C_h S)] at hLocal
  rw [ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_source_mass_eq_idAtom ids] at hLocal
  have hAtom := ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  apply le_of_mul_le_mul_left _ hAtom
  calc
    _ ≤ (CompletePublicTable.idArrayMeasure p).real {ids} *
        (B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ)) := hLocal
    _ = _ := by ring

omit rate rewards C_star C_h control0 ids S in
private theorem setIntegral_le_gate_mass_local
    {α : Type*} [MeasurableSpace α] (ν0 : Measure α) [IsFiniteMeasure ν0] (A G : Set α)
    (hA : MeasurableSet A) (hG : MeasurableSet G)
    (f : α → ℝ) (c0 : ℝ) (hf : Integrable f ν0)
    (hpoint : ∀ x, f x ≤ G.indicator (fun _ => c0) x) :
    (∫ x in A, f x ∂ν0) ≤ c0 * ν0.real (A ∩ G) := by
  have hfA : Integrable (A.indicator f) ν0 := hf.indicator hA
  have hcA : Integrable ((A ∩ G).indicator (fun _ : α => c0)) ν0 :=
    (integrable_const c0).indicator (hA.inter hG)
  have hle : ∀ x, A.indicator f x ≤ (A ∩ G).indicator (fun _ : α => c0) x := by
    intro x
    by_cases hxA : x ∈ A
    · by_cases hxG : x ∈ G
      · have hxAG : x ∈ A ∩ G := ⟨hxA, hxG⟩
        simpa only [Set.indicator_of_mem hxA, Set.indicator_of_mem hxAG,
          Set.indicator_of_mem hxG] using hpoint x
      · have hx := hpoint x
        have hnot : x ∉ A ∩ G := fun hx' => hxG hx'.2
        simpa only [Set.indicator_of_mem hxA, Set.indicator_of_notMem hxG,
          Set.indicator_of_notMem hnot] using hx
    · have hnot : x ∉ A ∩ G := fun hx => hxA hx.1
      simp [Set.indicator, hxA, hnot]
  have hmono := integral_mono hfA hcA hle
  rw [integral_indicator hA] at hmono
  rw [integral_indicator_const c0 (hA.inter hG)] at hmono
  simpa only [smul_eq_mul, mul_comm] using hmono

private def sharedFloorAtDate (t : Fin p.T) (z : SourceInput p) : ℝ :=
  ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
      rate rewards C_star C_h t S z +
    ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
      rate rewards C_star C_h t S z +
    ∑ u : Fin p.T,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
        rate rewards C_star C_h u t S z

private theorem sharedFloorAtDate_integrable (t : Fin p.T) :
    Integrable (sharedFloorAtDate rate rewards C_star C_h S t) μ := by
  have hLive := ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
    rate rewards C_star C_h t S control0
  have hOld := ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
    rate rewards C_star C_h control0 t S
  have hCurrent (u : Fin p.T) :=
    ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
      rate rewards C_star C_h control0 u t S
  unfold sharedFloorAtDate
  exact (hLive.add hOld).add (integrable_finsetSum Finset.univ (fun u _ => hCurrent u))

private theorem sharedFloorAtDate_setIntegral_le_localMass (t : Fin p.T) :
    (∫ z in D, sharedFloorAtDate rate rewards C_star C_h S t z ∂μ) ≤
      cFloor * ((μ).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
        (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
          rate rewards C_star C_h t) +
        ∑ u : Fin p.T, (μ).real (D ∩
          ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
  let liveGate := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
    rate rewards C_star C_h t
  let oldGate := ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t
  let phase234 :=
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
      ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4
  have hD := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hFle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0
      (t.val + 1) ≤ sourceInputMeasurableSpace :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (t.val + 1)
  have hLiveGate : MeasurableSet liveGate :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.measurableSet_retainedEnabledEvent
      rate rewards C_star C_h t control0
  have hOldGate : MeasurableSet oldGate :=
    hFle oldGate (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)
  have hCurrentGate (u : Fin p.T) :
      MeasurableSet (ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t) :=
    hFle _ (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have hcFloor : 0 ≤ cFloor := div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (mul_pos rate.eta.property
      (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hLiveBound (z : SourceInput p) :
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
          rate rewards C_star C_h t S z ≤
        liveGate.indicator (fun _ => cFloor) z := by
    simpa [liveGate] using
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.calendarFloorLoss_le_actualGateConstant
        rate rewards C_star C_h t S z
  have hOldBound (z : SourceInput p) :
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S z ≤ oldGate.indicator (fun _ => cFloor) z := by
    have hb := ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_bounds
      rate rewards C_star C_h t S z
    by_cases hz : z ∈ oldGate
    · simpa [oldGate, Set.indicator_of_mem hz] using hb.2
    · have hzero :
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
              rate rewards C_star C_h t S z = 0 := by
        apply le_antisymm
        · have hle := hb.2
          simpa [oldGate, hz] using hle
        · exact hb.1
      simp [oldGate, hz, hzero]
  have hCurrentBound (u : Fin p.T) (z : SourceInput p) :
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S z ≤
        (ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t).indicator (fun _ => cFloor) z := by
    let G := ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
    by_cases hz : z ∈ G
    · simpa [G, Set.indicator_of_mem hz] using
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_le
          rate rewards C_star C_h u t S z
    · simp [ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss, G, hz]
  have hLive := setIntegral_le_gate_mass_local μ D liveGate hD hLiveGate _ cFloor
    (ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
      rate rewards C_star C_h t S control0) hLiveBound
  have hOld := setIntegral_le_gate_mass_local μ D oldGate hD hOldGate _ cFloor
    (ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
      rate rewards C_star C_h control0 t S) hOldBound
  have hCurrent (u : Fin p.T) :=
    setIntegral_le_gate_mass_local μ D
      (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)
      hD (hCurrentGate u) _ cFloor
      (ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
        rate rewards C_star C_h control0 u t S) (hCurrentBound u)
  have hLiveSubset : D ∩ liveGate ⊆ D ∩ phase234 := by
    intro z hz
    have heq :=
      ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
        rate rewards C_star C_h t control0
    change z ∈ D ∩ ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent
      rate rewards C_star C_h t at hz
    rw [heq] at hz
    have hphase := hz.2.1
    rw [← Set.union_assoc] at hphase
    exact ⟨hz.1, hphase⟩
  have hmassLive : (μ).real (D ∩ liveGate) ≤ (μ).real (D ∩ phase234) :=
    measureReal_mono hLiveSubset
  have hExpand :
      (∫ z in D, sharedFloorAtDate rate rewards C_star C_h S t z ∂μ) =
        (∫ z in D,
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z ∂μ) +
        (∫ z in D,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z ∂μ) +
        ∑ u : Fin p.T, ∫ z in D,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z ∂μ := by
    unfold sharedFloorAtDate
    have hLiveOn : IntegrableOn
        (ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
          rate rewards C_star C_h t S) D μ :=
      (ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
        rate rewards C_star C_h t S control0).integrableOn
    have hOldOn : IntegrableOn
        (ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
          rate rewards C_star C_h t S) D μ :=
      (ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
        rate rewards C_star C_h control0 t S).integrableOn
    have hCurrentOn (u : Fin p.T) : IntegrableOn
        (ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S) D μ :=
      (ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
        rate rewards C_star C_h control0 u t S).integrableOn
    have hCurrentSum : IntegrableOn
        (fun z : SourceInput p => ∑ u : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z) D μ := by
      change Integrable (fun z : SourceInput p => ∑ u : Fin p.T,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u t S z) ((sourceInputLaw p).restrict D)
      exact integrable_finsetSum Finset.univ (fun u _ => hCurrentOn u)
    calc
      _ = (∫ z in D,
            ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
              rate rewards C_star C_h t S z +
            ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
              rate rewards C_star C_h t S z ∂μ) +
          ∫ z in D, (∑ u : Fin p.T,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
              rate rewards C_star C_h u t S z) ∂μ := by
        change (∫ z, (fun z =>
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z +
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z) z +
          (fun z => ∑ u : Fin p.T,
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
              rate rewards C_star C_h u t S z) z ∂((sourceInputLaw p).restrict D)) = _
        exact integral_add (hLiveOn.add hOldOn) hCurrentSum
      _ = _ := by
        rw [integral_add hLiveOn hOldOn,
          integral_finsetSum Finset.univ (fun u _ => hCurrentOn u)]
  calc
    _ = _ := hExpand
    _ ≤ cFloor * ((μ).real (D ∩ liveGate) + (μ).real (D ∩ oldGate) +
        ∑ u : Fin p.T, (μ).real
          (D ∩ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
      calc
        _ ≤ (cFloor * (μ).real (D ∩ liveGate) + cFloor * (μ).real (D ∩ oldGate)) +
            ∑ u : Fin p.T, cFloor * (μ).real
              (D ∩ ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) := by
          apply add_le_add
          · exact add_le_add hLive hOld
          · exact Finset.sum_le_sum (fun u _ => hCurrent u)
        _ = _ := by rw [← Finset.mul_sum]; ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hcFloor
      linarith [hmassLive]

public theorem originalCalendarFloorLoss_fixedID_cylinder_le_preMass :
    (∫ z in D,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S z ∂μ) ≤
      cFloor * fixedIDPreGateMass rate rewards C_star C_h ids := by
  let dateFloor := sharedFloorAtDate rate rewards C_star C_h S
  have hfloorEq :
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S = fun z => ∑ t : Fin p.T, dateFloor t z := by
    funext z
    change
      ((∑ t : Fin p.T,
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z) +
        (∑ t : Fin p.T,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u t S z) = _
    have hLiveOld :
        (∑ t : Fin p.T,
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h t S z) +
        (∑ t : Fin p.T,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h t S z) =
          ∑ t : Fin p.T,
            (ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                rate rewards C_star C_h t S z +
              ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                rate rewards C_star C_h t S z) := by
      rw [← Finset.sum_add_distrib]
    dsimp [dateFloor, sharedFloorAtDate]
    rw [hLiveOld, Finset.sum_comm, ← Finset.sum_add_distrib]
  have hsum :
      (∫ z in D, (∑ t : Fin p.T, dateFloor t z) ∂μ) ≤
        ∑ t : Fin p.T,
          cFloor * ((μ).real (D ∩
              (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
                ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
                ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
            (μ).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G
              rate rewards C_star C_h t) +
            ∑ u : Fin p.T, (μ).real (D ∩
              ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t)) := by
    rw [integral_finsetSum Finset.univ (fun t _ =>
      (sharedFloorAtDate_integrable rate rewards C_star C_h control0 S t).integrableOn)]
    exact Finset.sum_le_sum (fun t _ =>
      sharedFloorAtDate_setIntegral_le_localMass rate rewards C_star C_h control0 ids S t)
  calc
    _ = ∫ z in D, (∑ t : Fin p.T, dateFloor t z) ∂μ := by
      apply setIntegral_congr_fun (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
      intro z hz
      exact congrFun hfloorEq z
    _ ≤ _ := hsum
    _ = cFloor * fixedIDPreGateMass rate rewards C_star C_h ids := by
      simp only [fixedIDPreGateMass, Finset.mul_sum]

private theorem integral_originalExtendedRoundedGap_fixedID_cylinder_le_horizon :
    (∫ z in D,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
        rate rewards C_star C_h S z ∂μ) ≤
      (μ).real D *
        (B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) + cFloor * (p.T : ℝ)) := by
  have hCalendar :=
    ReferenceFirstCollectionFixedIDOriginalPrefixRoundedLearning.integral_originalCalendarRoundedGap_fixedID_cylinder_le_raw_add_floor
      rate rewards C_star C_h control0 ids S
  have hFloor := originalCalendarFloorLoss_fixedID_cylinder_le_preMass
    rate rewards C_star C_h control0 ids S
  have hIncrement :=
    ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.integral_originalExtendedRoundedGap_sub_calendar_le_raw_sub_firstInvocation_add_fixedIDPostGateMass
      rate rewards C_star C_h control0 S ids
  have hrawEq :
      (∫ z in D,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S z ∂μ) =
      (∫ z in D,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
          rate rewards C_star C_h S z ∂μ) := by
    apply setIntegral_congr_fun (ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids)
    intro z hz
    exact ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRawGap_eq_firstInvocationRawGap
      rate rewards C_star C_h S z
  have hRawExt := originalExtendedRawGap_integrable rate rewards C_star C_h control0 S
  have hRawBase := ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable
    rate rewards C_star C_h control0 S
  have hRoundExt := originalExtendedRoundedGap_integrable rate rewards C_star C_h control0 S
  have hRoundBase :=
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap_integrable
      rate rewards C_star C_h control0 S
  have hRoundDiff :
      (∫ z in D,
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
            rate rewards C_star C_h S z -
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
            rate rewards C_star C_h S z) ∂μ) =
        (∫ z in D,
          ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
            rate rewards C_star C_h S z ∂μ) -
          ∫ z in D,
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
              rate rewards C_star C_h S z ∂μ := by
    rw [integral_sub hRoundExt.integrableOn hRoundBase.integrableOn]
  have hRawDiff :
      (∫ z in D,
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
            rate rewards C_star C_h S z -
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z) ∂μ) =
        (∫ z in D,
          ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
            rate rewards C_star C_h S z ∂μ) -
          ∫ z in D,
            ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
              rate rewards C_star C_h S z ∂μ := by
    rw [integral_sub hRawExt.integrableOn hRawBase.integrableOn]
  have hmass := fixedIDJointCalendarMass_le_horizon rate rewards C_star C_h control0 ids
  have hcFloor : 0 ≤ cFloor := div_nonneg (Nat.cast_nonneg _)
    (le_of_lt (mul_pos rate.eta.property
      (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hbudget := mul_le_mul_of_nonneg_left hmass hcFloor
  have hcalRaw := hCalendar
  rw [hrawEq] at hcalRaw
  have hcalBound :
      (∫ z in D,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
          rate rewards C_star C_h S z ∂μ) ≤
        (∫ z in D,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z ∂μ) +
          cFloor * fixedIDPreGateMass rate rewards C_star C_h ids := by
    calc
      _ ≤ (∫ z in D,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z ∂μ) +
          ∫ z in D,
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
              rate rewards C_star C_h S z ∂μ := hcalRaw
      _ ≤ _ := add_le_add_right hFloor _
  have hmain :
      (∫ z in D,
        ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
          rate rewards C_star C_h S z ∂μ) ≤
        (∫ z in D,
          ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
            rate rewards C_star C_h S z ∂μ) +
          cFloor * (fixedIDPreGateMass rate rewards C_star C_h ids +
            ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport.fixedIDPostGateMass
              rate rewards C_star C_h ids) := by
    rw [hRoundDiff, hRawDiff] at hIncrement
    linarith [hcalBound]
  calc
    _ ≤ _ := hmain
    _ ≤ (∫ z in D,
        ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
          rate rewards C_star C_h S z ∂μ) + cFloor * ((p.T : ℝ) * (μ).real D) := by
      have hscaled := mul_le_mul_of_nonneg_left hmass hcFloor
      linarith
    _ ≤ (μ).real D *
        (B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) + cFloor * (p.T : ℝ)) := by
      have hraw := integral_originalExtendedRawGap_fixedID_cylinder_le_horizon
        rate rewards C_star C_h control0 ids S
      linarith

public theorem integral_originalExtendedRoundedGap_fixedID_le_horizon :
    (∫ z,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
        rate rewards C_star C_h S z ∂ν) ≤
      B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
        rate.eta.val * (p.T : ℝ) + cFloor * (p.T : ℝ) := by
  have hLocal := integral_originalExtendedRoundedGap_fixedID_cylinder_le_horizon
    rate rewards C_star C_h control0 ids S
  rw [ReferenceFixedIDSourceSection.sourceInputLaw_setIntegral_fixedIDSourceSection
    (p := p) ids
    (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
      rate rewards C_star C_h S)] at hLocal
  rw [ReferenceFirstCollectionFixedIDWeightedArrivalBudget.fixedID_source_mass_eq_idAtom ids] at hLocal
  have hAtom := ReferenceFixedIDSourceSection.idArrayAtom_positive ids
  apply le_of_mul_le_mul_left _ hAtom
  calc
    _ ≤ (CompletePublicTable.idArrayMeasure p).real {ids} *
        (B + ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) + cFloor * (p.T : ℝ)) := hLocal
    _ = _ := by ring

end Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalPrefixLearning

end
