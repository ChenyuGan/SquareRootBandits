/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalOriginalPrefixLearning
public import Bandits.Support.ReferenceFirstCollectionRenewalFixedIDLearningMoments

import Mathlib.Tactic

/-!
# Fixed-ID transport of original first-renewal learning moments

The original extended observations are integrated on the literal fixed-ID
section. Each zero-extended renewal-cell increment is transported to the
corresponding section of its existing unnormalized source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport

variable {p : Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (S : ProductSetLaw.ProductSet p.K p.m)
  (ids : CompletePublicTable.IDArray p)

local notation "Z" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "IdSection" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

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

private theorem zeroExtendCell_measurable {α : Type*} [MeasurableSpace α]
    (A : Set α) (hA : MeasurableSet A) (f : {x // x ∈ A} → ℝ)
    (hf : Measurable f) :
    Measurable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f) :=
  (MeasurableEmbedding.subtype_coe hA).measurable_extend hf measurable_const

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
    (hf : Integrable f (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t)) :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) f) μ := by
  apply zeroExtendCell_integrable
    (renewalCallEvent rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t) f μ
  simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw] using hf

private theorem integral_zeroExtendCell_fixedID
    (u t : Fin p.T)
    (f : renewalCallEvent rate rewards C_star C_h u t → ℝ)
    (hf : Measurable f) :
    (∫ z in IdSection,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) f z ∂μ) =
      ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
        f z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  let A := renewalCallEvent rate rewards C_star C_h u t
  let Dut := ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids
  let ext :=
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f
  have hA : MeasurableSet A :=
    ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t
  have hD : MeasurableSet IdSection :=
    ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hDut : MeasurableSet Dut := hD.preimage measurable_subtype_coe
  have hext : Measurable ext := zeroExtendCell_measurable A hA f hf
  have hpoint :
      (fun z : {x // x ∈ A} => Dut.indicator f z) =
        (fun z : {x // x ∈ A} => Set.indicator IdSection ext z.val) := by
    funext z
    by_cases hz : z ∈ Dut
    · have hval : z.val ∈ IdSection := hz
      simp only [Set.indicator_of_mem hz, Set.indicator_of_mem hval]
      exact (Subtype.val_injective.extend_apply f (fun _ => 0) z).symm
    · have hval : z.val ∉ IdSection := by
        intro hzval
        exact hz hzval
      simp [Set.indicator_of_notMem hz, Set.indicator_of_notMem hval]
  have hext_indicator : ext = A.indicator ext := by
    funext z
    exact zeroExtendCell_eq_indicator A f z
  have hpointD : Set.indicator IdSection ext = Set.indicator (IdSection ∩ A) ext := by
    funext z
    rw [hext_indicator]
    by_cases hzD : z ∈ IdSection <;> by_cases hzA : z ∈ A <;>
      simp [Set.indicator, hzD, hzA]
  calc
    _ = ∫ z in IdSection ∩ A, ext z ∂μ := by
      calc
        _ = ∫ z, Set.indicator IdSection ext z ∂μ := (integral_indicator hD).symm
        _ = ∫ z, (IdSection ∩ A).indicator ext z ∂μ := by rw [hpointD]
        _ = _ := integral_indicator (hD.inter hA)
    _ = ∫ z in Dut, f z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
      symm
      calc
        _ = ∫ z, Dut.indicator f z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
          exact (integral_indicator hDut).symm
        _ = ∫ z : {x // x ∈ A}, Set.indicator IdSection ext z.val
              ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun z => congrFun hpoint z)
        _ = ∫ z : Z, Set.indicator IdSection ext z
              ∂(ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).map Subtype.val := by
          exact (MeasurableEmbedding.subtype_coe hA).integral_map (Set.indicator IdSection ext) |>.symm
        _ = ∫ z : Z, Set.indicator IdSection ext z ∂((sourceInputLaw p).restrict A) := by
          rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val]
        _ = ∫ z in A, Set.indicator IdSection ext z ∂μ := rfl
        _ = ∫ z in A ∩ IdSection, ext z ∂μ := by rw [setIntegral_indicator hD]
        _ = ∫ z in IdSection ∩ A, ext z ∂μ := by rw [Set.inter_comm]

/-! The local gate budget uses exactly the same finite next/future calendar as
the accepted fixed-ID moment estimates. -/
public def fixedIDPostGateMass : ℝ :=
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass
        rate rewards C_star C_h u t ids +
      ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
        rate rewards C_star C_h u t ids)

include control0 S

omit S in
private theorem futureArrivalObservationTotal_measurable
    (u t : Fin p.T) :
    Measurable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
        rate rewards C_star C_h u t) := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
  apply Finset.measurable_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨_, hhi⟩
  have hq : n < p.T := hhi
  have hfuture : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
    dite_eq_left hq, dite_eq_left hfuture]
  exact ReferenceFirstCollectionRenewalFutureLearningMoments.measurable_futureArrivalObservation
    rate rewards C_star C_h u t control0 ⟨n, hq⟩ hfuture

private theorem futureArrivalComparatorGapTotal_measurable
    (u t : Fin p.T) :
    Measurable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
        rate rewards C_star C_h u t S) := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
  apply Finset.measurable_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨_, hhi⟩
  have hq : n < p.T := hhi
  have hfuture : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt,
    dite_eq_left hq, dite_eq_left hfuture]
  exact ReferenceFirstCollectionRenewalFutureLearningMoments.measurable_futureArrivalComparatorGap
    rate rewards C_star C_h u t control0 ⟨n, hq⟩ hfuture S

private theorem futureRewardComparatorGapTotal_measurable
    (u t : Fin p.T) :
    Measurable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
        rate rewards C_star C_h u t S) := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
  apply Finset.measurable_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨_, hhi⟩
  have hq : n < p.T := hhi
  have hfuture : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt,
    dite_eq_left hq, dite_eq_left hfuture]
  exact ReferenceFirstCollectionRenewalFutureLearningMoments.measurable_futureRewardComparatorGap
    rate rewards C_star C_h u t control0 ⟨n, hq⟩ hfuture S

private theorem rawCellIncrement_measurable (u t : Fin p.T) :
    Measurable (fun z : renewalCallEvent rate rewards C_star C_h u t =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
          rate rewards C_star C_h u t S z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
          rate rewards C_star C_h u t S z) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_measurable
      rate rewards C_star C_h u t control0 S).2.1.add
    (futureArrivalComparatorGapTotal_measurable rate rewards C_star C_h control0 S u t)

private theorem weightedCellIncrement_measurable (u t : Fin p.T) :
    Measurable (fun z : renewalCallEvent rate rewards C_star C_h u t =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
          rate rewards C_star C_h u t z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
          rate rewards C_star C_h u t z) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_measurable
      rate rewards C_star C_h u t control0 S).1.add
    (futureArrivalObservationTotal_measurable rate rewards C_star C_h control0 u t)

private theorem roundedCellIncrement_measurable (u t : Fin p.T) :
    Measurable (fun z : renewalCallEvent rate rewards C_star C_h u t =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
          rate rewards C_star C_h u t S z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
          rate rewards C_star C_h u t S z) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_measurable
      rate rewards C_star C_h u t control0 S).2.2.add
    (futureRewardComparatorGapTotal_measurable rate rewards C_star C_h control0 S u t)

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

private theorem weightedCellIncrement_integrable (u t : Fin p.T) :
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
private theorem integral_zeroExtendCell_sum_fixedID
    (f : (u t : Fin p.T) →
      (renewalCallEvent rate rewards C_star C_h u t → ℝ))
    (hf : ∀ u t, Measurable (f u t))
    (hfi : ∀ u t, Integrable (f u t) (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t)) :
    (∫ z in IdSection, ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) (f u t) z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          f u t z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) : Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) (f u t)) μ :=
    zeroExtendCell_integrable_on_source rate rewards C_star C_h u t (f u t) (hfi u t)
  calc
    _ = ∑ u : Fin p.T, ∫ z in IdSection, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t) (f u t) z ∂μ :=
      integral_finsetSum Finset.univ (fun u _ =>
        integrable_finsetSum Finset.univ (fun t _ => (hcell u t).integrableOn))
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z in IdSection,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t) (f u t) z ∂μ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_finsetSum Finset.univ (fun t _ => (hcell u t).integrableOn)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      exact integral_zeroExtendCell_fixedID rate rewards C_star C_h ids
        u t (f u t) (hf u t)

private theorem firstInvocationRawGap_integrable :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
        rate rewards C_star C_h S) μ :=
  ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable
    rate rewards C_star C_h control0 S

omit S in
private theorem firstInvocationWeightedArrival_integrable :
    Integrable
      (ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
        rate rewards C_star C_h) μ :=
  ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_integrable
    rate rewards C_star C_h control0

private theorem originalCalendarRoundedGap_integrable :
    Integrable
      (ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
        rate rewards C_star C_h S) μ :=
  ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRoundedGap_integrable
    rate rewards C_star C_h control0 S

private theorem originalExtendedRawGap_integrable :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
  apply firstInvocationRawGap_integrable rate rewards C_star C_h control0 S |>.add
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
  apply firstInvocationWeightedArrival_integrable rate rewards C_star C_h control0 |>.add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _
    (weightedCellIncrement_integrable rate rewards C_star C_h control0 S u t)

private theorem originalExtendedRoundedGap_integrable :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
        rate rewards C_star C_h S) μ := by
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
  apply originalCalendarRoundedGap_integrable rate rewards C_star C_h control0 S |>.add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _
    (roundedCellIncrement_integrable rate rewards C_star C_h control0 S u t)

/-- The raw comparator observation partitions on the literal fixed-ID source
section into its first-invocation term and the actual renewal-cell increments. -/
public theorem integral_originalExtendedRawGap_fixedID_partition :
    (∫ z in IdSection,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
        rate rewards C_star C_h S z ∂μ) =
      (∫ z in IdSection,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
          rate rewards C_star C_h S z ∂μ) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S z)
          ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) := rawCellIncrement_integrable
    rate rewards C_star C_h control0 S u t
  have hsum : Integrable (fun z : Z =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                rate rewards C_star C_h u t S w +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                rate rewards C_star C_h u t S w) z) μ := by
    apply integrable_finsetSum Finset.univ
    intro u hu
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _ (hcell u t)
  have hbase := firstInvocationRawGap_integrable rate rewards C_star C_h control0 S
  have hf (u t : Fin p.T) := rawCellIncrement_measurable rate rewards C_star C_h control0 S u t
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
  rw [integral_add hbase.integrableOn hsum.integrableOn]
  rw [integral_zeroExtendCell_sum_fixedID rate rewards C_star C_h ids
    (fun u t z =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
          rate rewards C_star C_h u t S z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
          rate rewards C_star C_h u t S z) hf hcell]

/-- The weighted-arrival observation partitions into the exact existing
first-invocation observation and the unnormalized actual renewal increments. -/
public theorem integral_originalExtendedWeightedArrival_fixedID_partition :
    (∫ z in IdSection,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
        rate rewards C_star C_h z ∂μ) =
      (∫ z in IdSection,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
          rate rewards C_star C_h z ∂μ) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
              rate rewards C_star C_h u t z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
              rate rewards C_star C_h u t z)
          ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) := weightedCellIncrement_integrable
    rate rewards C_star C_h control0 S u t
  have hsum : Integrable (fun z : Z =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
                rate rewards C_star C_h u t w +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
                rate rewards C_star C_h u t w) z) μ := by
    apply integrable_finsetSum Finset.univ
    intro u hu
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _ (hcell u t)
  have hbase := firstInvocationWeightedArrival_integrable rate rewards C_star C_h control0
  have hf (u t : Fin p.T) := weightedCellIncrement_measurable rate rewards C_star C_h control0 S u t
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
  rw [integral_add hbase.integrableOn hsum.integrableOn]
  rw [integral_zeroExtendCell_sum_fixedID rate rewards C_star C_h ids
    (fun u t z =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
          rate rewards C_star C_h u t z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
          rate rewards C_star C_h u t z) hf hcell]

/-- The rounded comparator observation partitions on the same fixed-ID section
into its original calendar observation and actual renewal increments. -/
public theorem integral_originalExtendedRoundedGap_fixedID_partition :
    (∫ z in IdSection,
      ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
        rate rewards C_star C_h S z ∂μ) =
      (∫ z in IdSection,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
          rate rewards C_star C_h S z ∂μ) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
              rate rewards C_star C_h u t S z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
              rate rewards C_star C_h u t S z)
          ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) := roundedCellIncrement_integrable
    rate rewards C_star C_h control0 S u t
  have hsum : Integrable (fun z : Z =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
                rate rewards C_star C_h u t S w +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
                rate rewards C_star C_h u t S w) z) μ := by
    apply integrable_finsetSum Finset.univ
    intro u hu
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _ (hcell u t)
  have hbase := originalCalendarRoundedGap_integrable rate rewards C_star C_h control0 S
  have hf (u t : Fin p.T) := roundedCellIncrement_measurable rate rewards C_star C_h control0 S u t
  unfold ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
  rw [integral_add hbase.integrableOn hsum.integrableOn]
  rw [integral_zeroExtendCell_sum_fixedID rate rewards C_star C_h ids
    (fun u t z =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
          rate rewards C_star C_h u t S z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
          rate rewards C_star C_h u t S z) hf hcell]

include control0 S

private theorem weightedIncrement_sum_bounds :
    0 ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
              rate rewards C_star C_h u t z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
              rate rewards C_star C_h u t z)
          ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t ∧
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
              rate rewards C_star C_h u t z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
              rate rewards C_star C_h u t z)
          ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) ≤
        (p.m : ℝ) * fixedIDPostGateMass rate rewards C_star C_h ids := by
  have hnext (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.integral_naturalNextArrivalObservation_fixedID
      rate rewards C_star C_h u t control0 ids
  have hfuture (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.integral_futureArrivalObservationTotal_fixedID
      rate rewards C_star C_h u t control0 ids
  have hnextI (u t : Fin p.T) :=
    (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S).1
  have hfutureI (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservationTotal
      rate rewards C_star C_h u t control0
  have hcell (u t : Fin p.T) :
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
        (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
            rate rewards C_star C_h u t z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
            rate rewards C_star C_h u t z)
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
        (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
            rate rewards C_star C_h u t z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
            rate rewards C_star C_h u t z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    exact integral_add (hnextI u t).integrableOn (hfutureI u t).integrableOn
  refine ⟨?_, ?_⟩
  · apply Finset.sum_nonneg
    intro u hu
    apply Finset.sum_nonneg
    intro t ht
    rw [hcell]
    exact add_nonneg (hnext u t).1 (hfuture u t).1
  · calc
      _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
          ((p.m : ℝ) * ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass
              rate rewards C_star C_h u t ids +
            (p.m : ℝ) * ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
              rate rewards C_star C_h u t ids) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro t ht
        rw [hcell]
        exact add_le_add (hnext u t).2 (hfuture u t).2
      _ = (p.m : ℝ) * fixedIDPostGateMass rate rewards C_star C_h ids := by
        simp only [fixedIDPostGateMass, Finset.sum_add_distrib, Finset.mul_sum, mul_add]

/-- The extended weighted-arrival increment is nonnegative on the original
fixed-ID section and is bounded by its exact post-call gate masses. -/
public theorem integral_originalExtendedWeightedArrival_sub_firstInvocation_fixedID :
    0 ≤ ∫ z in IdSection,
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
          rate rewards C_star C_h z -
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
          rate rewards C_star C_h z) ∂μ ∧
    (∫ z in IdSection,
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
          rate rewards C_star C_h z -
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
          rate rewards C_star C_h z) ∂μ) ≤
      (p.m : ℝ) * fixedIDPostGateMass rate rewards C_star C_h ids := by
  have hpart := integral_originalExtendedWeightedArrival_fixedID_partition
    rate rewards C_star C_h control0 S ids
  have hext := originalExtendedWeightedArrival_integrable rate rewards C_star C_h control0 S
  have hbase := firstInvocationWeightedArrival_integrable rate rewards C_star C_h control0
  have hdiff :
      (∫ z in IdSection,
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedWeightedArrival
            rate rewards C_star C_h z -
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
            rate rewards C_star C_h z) ∂μ) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
            (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
                rate rewards C_star C_h u t z +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
                rate rewards C_star C_h u t z)
            ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    rw [integral_sub hext.integrableOn hbase.integrableOn, hpart]
    ring
  rw [hdiff]
  exact weightedIncrement_sum_bounds rate rewards C_star C_h control0 S ids

private theorem roundedIncrement_sum_le_raw_add_postGateMass :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
        (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
            rate rewards C_star C_h u t S z)
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) ≤
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S z)
          ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
        ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
          fixedIDPostGateMass rate rewards C_star C_h ids := by
  have hnext (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.integral_naturalNextRoundedRewardGap_fixedID
      rate rewards C_star C_h u t control0 ids S
  have hfuture (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFixedIDLearningMoments.integral_futureRewardComparatorGapTotal_fixedID
      rate rewards C_star C_h u t control0 ids S
  have hroundI (u t : Fin p.T) :=
    (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S).2.2
  have hcompI (u t : Fin p.T) :=
    (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S).2.1
  have hfutureRoundI (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureRewardComparatorGapTotal
      rate rewards C_star C_h u t control0 S
  have hfutureCompI (u t : Fin p.T) :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGapTotal
      rate rewards C_star C_h u t control0 S
  have hroundAdd (u t : Fin p.T) :
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids,
        (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
            rate rewards C_star C_h u t S z)
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
          rate rewards C_star C_h u t S z
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
      ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
          rate rewards C_star C_h u t S z
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t :=
    integral_add (hroundI u t).integrableOn (hfutureRoundI u t).integrableOn
  have hcompAdd (u t : Fin p.T) :
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids,
        (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
            rate rewards C_star C_h u t S z)
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) =
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
          rate rewards C_star C_h u t S z
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
      ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection
          rate rewards C_star C_h u t ids,
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
          rate rewards C_star C_h u t S z
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t :=
    integral_add (hcompI u t).integrableOn (hfutureCompI u t).integrableOn
  have hcell (u t : Fin p.T) :
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
        (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
            rate rewards C_star C_h u t S z)
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) ≤
      (∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
        (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
            rate rewards C_star C_h u t S z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
            rate rewards C_star C_h u t S z)
        ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
        ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
          (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass
              rate rewards C_star C_h u t ids +
            ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
              rate rewards C_star C_h u t ids) := by
    rw [hroundAdd u t, hcompAdd u t]
    calc
      _ ≤ ((∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
              ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                rate rewards C_star C_h u t S z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
            ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
              ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass
                rate rewards C_star C_h u t ids) +
          ((∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                rate rewards C_star C_h u t S z ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
            ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
              ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
                rate rewards C_star C_h u t ids) :=
        add_le_add (hnext u t) (hfuture u t)
      _ = _ := by ring
  calc
    _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
            (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                rate rewards C_star C_h u t S z +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                rate rewards C_star C_h u t S z)
            ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) +
          ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
            (ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDNextGateMass
                rate rewards C_star C_h u t ids +
              ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDFutureGateMass
                rate rewards C_star C_h u t ids)) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro t ht
      exact hcell u t
    _ = _ := by
      simp only [fixedIDPostGateMass, Finset.sum_add_distrib, Finset.mul_sum, mul_add]

/-- The original fixed-ID rounded increment is bounded by the signed raw
comparator increment plus the same exact local post-call gate-mass charge. -/
public theorem integral_originalExtendedRoundedGap_sub_calendar_le_raw_sub_firstInvocation_add_fixedIDPostGateMass :
    (∫ z in IdSection,
      (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
          rate rewards C_star C_h S z -
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
          rate rewards C_star C_h S z) ∂μ) ≤
      (∫ z in IdSection,
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
            rate rewards C_star C_h S z -
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z) ∂μ) +
        ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
          fixedIDPostGateMass rate rewards C_star C_h ids := by
  have hroundPart := integral_originalExtendedRoundedGap_fixedID_partition
    rate rewards C_star C_h control0 S ids
  have hrawPart := integral_originalExtendedRawGap_fixedID_partition
    rate rewards C_star C_h control0 S ids
  have hroundExt := originalExtendedRoundedGap_integrable
    rate rewards C_star C_h control0 S
  have hroundBase := originalCalendarRoundedGap_integrable
    rate rewards C_star C_h control0 S
  have hrawExt := originalExtendedRawGap_integrable
    rate rewards C_star C_h control0 S
  have hrawBase := firstInvocationRawGap_integrable rate rewards C_star C_h control0 S
  have hroundDiff :
      (∫ z in IdSection,
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRoundedGap
            rate rewards C_star C_h S z -
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
            rate rewards C_star C_h S z) ∂μ) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
            (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
                rate rewards C_star C_h u t S z +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
                rate rewards C_star C_h u t S z)
            ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    rw [integral_sub hroundExt.integrableOn hroundBase.integrableOn, hroundPart]
    ring
  have hrawDiff :
      (∫ z in IdSection,
        (ReferenceFirstCollectionRenewalOriginalPrefixLearning.originalExtendedRawGap
            rate rewards C_star C_h S z -
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S z) ∂μ) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z in ReferenceFirstCollectionRenewalFixedIDLearningMoments.fixedIDRenewalSection rate rewards C_star C_h u t ids,
            (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                rate rewards C_star C_h u t S z +
              ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                rate rewards C_star C_h u t S z)
            ∂ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t := by
    rw [integral_sub hrawExt.integrableOn hrawBase.integrableOn, hrawPart]
    ring
  rw [hroundDiff, hrawDiff]
  exact roundedIncrement_sum_le_raw_add_postGateMass
    rate rewards C_star C_h control0 S ids

end Bandits.Support.ReferenceFirstCollectionRenewalFixedIDOriginalMomentTransport
