/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalRawPotential
public import Bandits.Support.ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget
public import Bandits.Support.ReferenceFirstCollectionOriginalPrefixRoundedLearning

import Mathlib.Tactic

/-!
# Original-source learning through the first renewal endpoint

The scalar observations in this file extend the original first-invocation
observations over the existing disjoint first-renewal cells.  The extension
uses the accepted endpoint word and the same unnormalized original source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceFirstCollectionRenewalOriginalPrefixLearning

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p)
  (S : ProductSetLaw.ProductSet p.K p.m)

local notation "Z" => SourceInput p
local notation "μ" => sourceInputLaw p
local notation "Q" => ReferenceFirstLaunchNumericalCell.queueParameters rate
local notation "B" =>
  Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
    16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
    (p.m : ℝ) / (16 * rate.eta.val)
local notation "cFloor" =>
  (p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p × BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

local instance renewalLawFinite (u t : Fin p.T) :
    IsFiniteMeasure (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_finite
    rate rewards C_star C_h u t

private abbrev renewalCallEvent (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
    rate rewards C_star C_h u t
private abbrev renewalSourceLaw (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
    rate rewards C_star C_h u t
private abbrev nextArrivalObservation (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
    rate rewards C_star C_h u t
private abbrev nextComparatorObservation
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
    rate rewards C_star C_h u t S0
private abbrev nextRoundedObservation
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
    rate rewards C_star C_h u t S0
private abbrev futureArrivalObservationTotal (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
    rate rewards C_star C_h u t
private abbrev futureArrivalComparatorGapTotal
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
    rate rewards C_star C_h u t S0
private abbrev futureRewardComparatorGapTotal
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :=
  ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
    rate rewards C_star C_h u t S0

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
    have heq : (fun x : {x // x ∈ A} =>
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

private theorem integral_zeroExtendCell {α : Type*} [MeasurableSpace α]
    (A : Set α) (hA : MeasurableSet A) (f : {x // x ∈ A} → ℝ)
    (μ0 : Measure α)
    (hf : Measurable (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f)) :
    (∫ x, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f x ∂μ0) =
      ∫ x : {x // x ∈ A}, f x ∂μ0.comap (Subtype.val : {x // x ∈ A} → α) := by
  have heq :
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f =
        A.indicator
          (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f) := by
    funext x
    exact zeroExtendCell_eq_indicator A f x
  rw [heq, integral_indicator hA, ← map_comap_subtype_coe hA]
  calc
    _ = ∫ x : {x // x ∈ A},
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell A f x.val
          ∂μ0.comap (Subtype.val : {x // x ∈ A} → α) := by
      exact integral_map measurable_subtype_coe.aemeasurable
        hf.aestronglyMeasurable
    _ = ∫ x : {x // x ∈ A}, f x
        ∂μ0.comap (Subtype.val : {x // x ∈ A} → α) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        Subtype.val_injective.extend_apply f (fun _ => 0) x

@[expose] public def originalExtendedRawGap
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
      rate rewards C_star C_h S0 z +
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t)
        (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t =>
          ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation rate rewards C_star C_h u t S0 w + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal rate rewards C_star C_h u t S0 w) z

@[expose] public def originalExtendedWeightedArrival
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ) (z : SourceInput p) : ℝ :=
  ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
      rate rewards C_star C_h z +
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t)
        (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t =>
          ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t w + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal rate rewards C_star C_h u t w) z

@[expose] public def originalExtendedRoundedGap
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) : ℝ :=
  ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
      rate rewards C_star C_h S0 z +
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t)
        (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t =>
          ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap rate rewards C_star C_h u t S0 w + ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal rate rewards C_star C_h u t S0 w) z

/-- The exact cost charged by the extended raw potential. -/
@[expose] public def originalExtendedCost
    (rate : ReferenceActivePhysicalStep.RateInput p)
    (rewards : GridRewardTable p) (C_star C_h : ℝ) (z : SourceInput p) : ℝ :=
  ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
      rate rewards C_star C_h z +
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
      rate rewards C_star C_h z

private theorem renewalEvents_disjoint (a b : Fin p.T × Fin p.T) (hne : a ≠ b) :
    Disjoint (renewalCallEvent rate rewards C_star C_h a.1 a.2) (renewalCallEvent rate rewards C_star C_h b.1 b.2) :=
  ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEvents_disjoint
    rate rewards C_star C_h a.1 a.2 b.1 b.2 hne

private theorem zeroExtendSum_eq_cell
    (f : (u t : Fin p.T) → ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t → ℝ)
    (u t : Fin p.T) (z : SourceInput p)
    (hz : z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t) :
    (∑ u' : Fin p.T, ∑ t' : Fin p.T, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u' t') (f u' t')) z = f u t ⟨z, hz⟩ := by
  classical
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem u (Finset.mem_univ _)]
  · rw [Finset.sum_apply]
    rw [Finset.sum_eq_single_of_mem t (Finset.mem_univ _)]
    · simpa [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell] using
        (Subtype.val_injective.extend_apply (f u t) (fun _ => 0) ⟨z, hz⟩)
    · intro t' ht' hne
      have hd := renewalEvents_disjoint rate rewards C_star C_h (u, t) (u, t') (by
        intro h
        exact hne (congrArg Prod.snd h.symm))
      have hz' : z ∉ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t' := by
        intro hz'
        exact (Set.disjoint_left.mp hd hz hz').elim
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        hz']
  · intro u' hu' hune
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro t' ht'
    by_cases hne : (u, t) = (u', t')
    · exact (hune (congrArg Prod.fst hne.symm)).elim
    · have hd := renewalEvents_disjoint rate rewards C_star C_h (u, t) (u', t') hne
      have hz' : z ∉ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u' t' := by
        intro hz'
        exact (Set.disjoint_left.mp hd hz hz').elim
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        hz']

private theorem futureArrivalObservationTotal_measurable
    (control0 : TimeControl p) (u t : Fin p.T) :
    Measurable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal rate rewards C_star C_h u t) := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
  apply Finset.measurable_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn₁, hn₂⟩
  have hq : n < p.T := hn₂
  have hf : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationAt,
    dif_pos hq, dif_pos hf]
  exact ReferenceFirstCollectionRenewalFutureLearningMoments.measurable_futureArrivalObservation
    rate rewards C_star C_h u t control0 ⟨n, hq⟩ hf

private theorem futureArrivalComparatorGapTotal_measurable
    (control0 : TimeControl p) (u t : Fin p.T)
    (S0 : ProductSetLaw.ProductSet p.K p.m) :
    Measurable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal rate rewards C_star C_h u t S0) := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
  apply Finset.measurable_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn₁, hn₂⟩
  have hq : n < p.T := hn₂
  have hf : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapAt,
    dif_pos hq, dif_pos hf]
  exact ReferenceFirstCollectionRenewalFutureLearningMoments.measurable_futureArrivalComparatorGap
    rate rewards C_star C_h u t control0 ⟨n, hq⟩ hf S0

private theorem futureRewardComparatorGapTotal_measurable
    (control0 : TimeControl p) (u t : Fin p.T)
    (S0 : ProductSetLaw.ProductSet p.K p.m) :
    Measurable
      (ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal rate rewards C_star C_h u t S0) := by
  unfold ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
  apply Finset.measurable_sum
  intro n hn
  rcases Finset.mem_Ico.mp hn with ⟨hn₁, hn₂⟩
  have hq : n < p.T := hn₂
  have hf : t.val + 1 < n := by omega
  simp only [ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapAt,
    dif_pos hq, dif_pos hf]
  exact ReferenceFirstCollectionRenewalFutureLearningMoments.measurable_futureRewardComparatorGap
    rate rewards C_star C_h u t control0 ⟨n, hq⟩ hf S0

private theorem rawCellIncrement_measurable (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    Measurable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => nextComparatorObservation rate rewards C_star C_h S0 u t z + futureArrivalComparatorGapTotal rate rewards C_star C_h S0 u t z) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_measurable rate rewards C_star C_h u t control0 S0).2.1.add
      (futureArrivalComparatorGapTotal_measurable rate rewards C_star C_h control0 u t S0)

private theorem weightedCellIncrement_measurable (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    Measurable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => nextArrivalObservation rate rewards C_star C_h u t z + futureArrivalObservationTotal rate rewards C_star C_h u t z) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_measurable rate rewards C_star C_h u t control0 S0).1.add
      (futureArrivalObservationTotal_measurable rate rewards C_star C_h control0 u t)

private theorem roundedCellIncrement_measurable (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    Measurable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => nextRoundedObservation rate rewards C_star C_h S0 u t z + futureRewardComparatorGapTotal rate rewards C_star C_h S0 u t z) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_measurable rate rewards C_star C_h u t control0 S0).2.2.add
      (futureRewardComparatorGapTotal_measurable rate rewards C_star C_h control0 u t S0)

private theorem rawCellIncrement_integrable (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => nextComparatorObservation rate rewards C_star C_h S0 u t z + futureArrivalComparatorGapTotal rate rewards C_star C_h S0 u t z) (renewalSourceLaw rate rewards C_star C_h u t) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable rate rewards C_star C_h u t control0 S0).2.1.add
      (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGapTotal rate rewards C_star C_h u t control0 S0)

private theorem weightedCellIncrement_integrable (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => nextArrivalObservation rate rewards C_star C_h u t z + futureArrivalObservationTotal rate rewards C_star C_h u t z) (renewalSourceLaw rate rewards C_star C_h u t) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable rate rewards C_star C_h u t control0 S0).1.add
      (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservationTotal rate rewards C_star C_h u t control0)

private theorem roundedCellIncrement_integrable (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    Integrable (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t => nextRoundedObservation rate rewards C_star C_h S0 u t z + futureRewardComparatorGapTotal rate rewards C_star C_h S0 u t z) (renewalSourceLaw rate rewards C_star C_h u t) := by
  exact (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable rate rewards C_star C_h u t control0 S0).2.2.add
      (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureRewardComparatorGapTotal rate rewards C_star C_h u t control0 S0)

private theorem zeroExtendCell_integrable_on_source
    (u t : Fin p.T) (f : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t → ℝ)
    (hf : Integrable f (renewalSourceLaw rate rewards C_star C_h u t)) :
    Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell (renewalCallEvent rate rewards C_star C_h u t) f) μ := by
  apply zeroExtendCell_integrable (renewalCallEvent rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent rate rewards C_star C_h u t) f μ
  simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw] using hf

private theorem zeroExtendCell_measurable_on_source
    (u t : Fin p.T) (f : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t → ℝ) (hf : Measurable f) :
    Measurable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell (renewalCallEvent rate rewards C_star C_h u t) f) :=
  zeroExtendCell_measurable (renewalCallEvent rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent rate rewards C_star C_h u t) f hf

private theorem integral_zeroExtendCell_on_source
    (u t : Fin p.T) (f : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t → ℝ) (hf : Measurable f) :
    (∫ z : SourceInput p, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell (renewalCallEvent rate rewards C_star C_h u t) f z ∂μ) = ∫ z, f z ∂(renewalSourceLaw rate rewards C_star C_h u t) := by
  have hm := zeroExtendCell_measurable_on_source rate rewards C_star C_h u t f hf
  have hi := integral_zeroExtendCell (renewalCallEvent rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent rate rewards C_star C_h u t) f μ hm
  simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw] using hi

private theorem originalExtendedRawGap_integrable
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (originalExtendedRawGap rate rewards C_star C_h S0) μ := by
  unfold originalExtendedRawGap
  apply (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable rate rewards C_star C_h control0 S0).add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t
    (fun z => nextComparatorObservation rate rewards C_star C_h S0 u t z + futureArrivalComparatorGapTotal rate rewards C_star C_h S0 u t z)
    (rawCellIncrement_integrable rate rewards C_star C_h control0 S0 u t)

private theorem originalExtendedWeightedArrival_integrable
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    Integrable (originalExtendedWeightedArrival rate rewards C_star C_h) μ := by
  unfold originalExtendedWeightedArrival
  apply (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_integrable rate rewards C_star C_h control0).add
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t
    (fun z => nextArrivalObservation rate rewards C_star C_h u t z + futureArrivalObservationTotal rate rewards C_star C_h u t z)
    (weightedCellIncrement_integrable rate rewards C_star C_h control0 S0 u t)

private theorem originalExtendedCost_integrable (control0 : TimeControl p) :
    Integrable (originalExtendedCost rate rewards C_star C_h) μ := by
  unfold originalExtendedCost
  exact (ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_integrable rate rewards C_star C_h control0).add
    (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog_integrable rate rewards C_star C_h control0)

/-- On an actual first-renewal cell, all three scalar extensions are the
corresponding complete endpoint observations, including the single immediate
successor and the strict future tail. -/
public theorem originalExtendedObservations_eq_endpoint
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t) :
    originalExtendedRawGap rate rewards C_star C_h S0 z.val =
        ReferenceFirstCollectionRenewalRawPotential.endpointRawGap
          rate rewards C_star C_h u t S0 z ∧
    originalExtendedWeightedArrival rate rewards C_star C_h z.val =
        ReferenceFirstCollectionRenewalRawPotential.endpointWeightedArrival
          rate rewards C_star C_h u t z ∧
    originalExtendedRoundedGap rate rewards C_star C_h S0 z.val =
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
            rate rewards C_star C_h S0 z.val +
          ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
              rate rewards C_star C_h u t S0 z +
          ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
              rate rewards C_star C_h u t S0 z := by
  have hraw := zeroExtendSum_eq_cell rate rewards C_star C_h
    (fun u t z =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation rate rewards C_star C_h u t S0 z + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal rate rewards C_star C_h u t S0 z) u t z.val z.property
  have hw := zeroExtendSum_eq_cell rate rewards C_star C_h
    (fun u t z =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t z + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal rate rewards C_star C_h u t z) u t z.val z.property
  have hr := zeroExtendSum_eq_cell rate rewards C_star C_h
    (fun u t z =>
      ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap rate rewards C_star C_h u t S0 z + ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal rate rewards C_star C_h u t S0 z) u t z.val z.property
  simp only [Finset.sum_apply, Subtype.eta] at hraw hw hr
  constructor
  · unfold originalExtendedRawGap
    rw [hraw, ReferenceFirstCollectionRenewalRawPotential.endpointRawGap_decomposition]
    <;> ring
  constructor
  · unfold originalExtendedWeightedArrival
    rw [hw, ReferenceFirstCollectionRenewalRawPotential.endpointWeightedArrival_decomposition]
    <;> ring
  · unfold originalExtendedRoundedGap
    rw [hr]
    ring

private theorem originalAfterCallBacklog_eq_cell
    (u t : Fin p.T) (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
        rate rewards C_star C_h z.val =
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t z := by
  unfold ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
  simpa using zeroExtendSum_eq_cell rate rewards C_star C_h
    (fun u t z => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog rate rewards C_star C_h u t z) u t z.val z.property

private theorem originalExtendedRawGap_pointwise
    (S0 : ProductSetLaw.ProductSet p.K p.m) (z : SourceInput p) :
    originalExtendedRawGap rate rewards C_star C_h S0 z ≤
      B + 8 * rate.eta.val *
        (originalExtendedCost rate rewards C_star C_h z + originalExtendedWeightedArrival rate rewards C_star C_h z) := by
  classical
  by_cases hex : ∃ u t : Fin p.T,
      z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t
  · obtain ⟨u, t, hz⟩ := hex
    let w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t := ⟨z, hz⟩
    have heval := originalExtendedObservations_eq_endpoint
      rate rewards C_star C_h S0 u t w
    have hcost := originalAfterCallBacklog_eq_cell
      rate rewards C_star C_h u t w
    have hendpoint := ReferenceFirstCollectionRenewalRawPotential.endpointRawGap_le_horizon_cost_and_arrival
      rate rewards C_star C_h u t S0 w
    simpa [w, originalExtendedCost, heval.1, heval.2.1, hcost] using hendpoint
  · have hnone : ∀ u t : Fin p.T,
        z ∉ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t := by
      intro u t hz
      exact hex ⟨u, t, hz⟩
    have hzero : ∀ u t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t)
          (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation rate rewards C_star C_h u t S0 w + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal rate rewards C_star C_h u t S0 w) z = 0 := by
      intro u t
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        hnone u t]
    have hwzero : ∀ u t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent rate rewards C_star C_h u t)
          (fun w : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t =>
            ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t w + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal rate rewards C_star C_h u t w) z = 0 := by
      intro u t
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell,
        hnone u t]
    have hback :
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
          rate rewards C_star C_h z = 0 := by
      simp [ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell, hnone]
    have hraw := ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap_le
      rate rewards C_star C_h S0 z
    have hcorr := ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCorrection_le
      rate rewards C_star C_h z
    have hraw' : originalExtendedRawGap rate rewards C_star C_h S0 z =
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
          rate rewards C_star C_h S0 z := by
      simp [originalExtendedRawGap, hzero]
    have hw' : originalExtendedWeightedArrival rate rewards C_star C_h z =
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationWeightedArrival
          rate rewards C_star C_h z := by
      simp [originalExtendedWeightedArrival, hwzero]
    rw [hraw', hw', originalExtendedCost, hback]
    linarith

private theorem originalExtendedRawGap_integral_le_cost_and_arrival
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedRawGap rate rewards C_star C_h S0 z ∂μ) ≤
      B + 8 * rate.eta.val *
        ((∫ z, originalExtendedCost rate rewards C_star C_h z ∂μ) + ∫ z, originalExtendedWeightedArrival rate rewards C_star C_h z ∂μ) := by
  have hraw := originalExtendedRawGap_integrable rate rewards C_star C_h control0 S0
  have hcost := originalExtendedCost_integrable rate rewards C_star C_h control0
  have hw := originalExtendedWeightedArrival_integrable rate rewards C_star C_h control0 S0
  have hmajor : Integrable (fun z : SourceInput p =>
      B + 8 * rate.eta.val * (originalExtendedCost rate rewards C_star C_h z + originalExtendedWeightedArrival rate rewards C_star C_h z)) μ := by
    exact (integrable_const B).add
      ((hcost.add hw).const_mul (8 * rate.eta.val))
  have hp : ∀ z, originalExtendedRawGap rate rewards C_star C_h S0 z ≤
      B + 8 * rate.eta.val *
        (originalExtendedCost rate rewards C_star C_h z + originalExtendedWeightedArrival rate rewards C_star C_h z) :=
    originalExtendedRawGap_pointwise rate rewards C_star C_h S0
  calc
    _ ≤ ∫ z : SourceInput p, B + 8 * rate.eta.val *
          (originalExtendedCost rate rewards C_star C_h z + originalExtendedWeightedArrival rate rewards C_star C_h z) ∂μ :=
      integral_mono hraw hmajor hp
    _ = B + 8 * rate.eta.val *
          ((∫ z, originalExtendedCost rate rewards C_star C_h z ∂μ) + ∫ z, originalExtendedWeightedArrival rate rewards C_star C_h z ∂μ) := by
      have hB : (∫ _ : SourceInput p, B ∂μ) = B := by
        rw [integral_const, probReal_univ, one_smul]
      calc
        _ = (∫ _ : SourceInput p, B ∂μ) +
            ∫ z : SourceInput p,
              8 * rate.eta.val *
                (originalExtendedCost rate rewards C_star C_h z + originalExtendedWeightedArrival rate rewards C_star C_h z) ∂μ := by
          change (∫ z : SourceInput p, (fun _ : SourceInput p => B) z + (fun z => 8 * rate.eta.val * (originalExtendedCost rate rewards C_star C_h z + originalExtendedWeightedArrival rate rewards C_star C_h z)) z ∂μ) = _
          exact integral_add (integrable_const B)
            ((hcost.add hw).const_mul (8 * rate.eta.val))
        _ = B + 8 * rate.eta.val *
            ((∫ z, originalExtendedCost rate rewards C_star C_h z ∂μ) + ∫ z, originalExtendedWeightedArrival rate rewards C_star C_h z ∂μ) := by
          rw [hB, integral_const_mul, integral_add hcost hw]

private theorem firstInvocationCost_eq_originalPreCallWeightedCost (z : SourceInput p) :
    ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
        rate rewards C_star C_h z =
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
        rate rewards C_star C_h z := by
  rw [ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_eq_energyIntegrand]
  rfl

private theorem originalExtendedCost_integral_eq_joined (control0 : TimeControl p) :
    (∫ z : SourceInput p, originalExtendedCost rate rewards C_star C_h z ∂μ) =
      (∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost rate rewards C_star C_h z ∂μ) +
        ∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
          rate rewards C_star C_h z ∂μ := by
  have hpre :=
    ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget.originalPreCallWeightedCost_integrable
      rate rewards C_star C_h control0
  have hafter :=
    ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog_integrable
      rate rewards C_star C_h control0
  calc
    _ = ∫ z, ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalPreCallWeightedCost
          rate rewards C_star C_h z +
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.originalAfterCallBacklog
          rate rewards C_star C_h z ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp [originalExtendedCost, firstInvocationCost_eq_originalPreCallWeightedCost]
    _ = _ := integral_add hpre hafter

private theorem nextArrivalObservation_integral_le_postGate (control0 : TimeControl p)
    (u t : Fin p.T) :
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t z ∂renewalSourceLaw rate rewards C_star C_h u t) ≤
      (p.m : ℝ) *
        (if hnext : t.val + 1 < p.T then (renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate rate rewards C_star C_h u t hnext) else 0) := by
  by_cases hnext : t.val + 1 < p.T
  · have h :=
      ReferenceFirstCollectionRenewalNextLearningMoments.integral_arrivalObservation_condExp_bounds
        rate rewards C_star C_h u t control0 hnext
    simpa [ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation,
      hnext] using h.2
  · simp [ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation,
      hnext]

private theorem weightedCellIncrement_integral_le_afterGate (control0 : TimeControl p)
    (S0 : ProductSetLaw.ProductSet p.K p.m) (u t : Fin p.T) :
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t z + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal rate rewards C_star C_h u t z) ∂renewalSourceLaw rate rewards C_star C_h u t) ≤
      (p.m : ℝ) *
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t := by
  have hnext := nextArrivalObservation_integral_le_postGate
    rate rewards C_star C_h control0 u t
  have hfuture :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integral_futureArrivalObservationTotal_le
      rate rewards C_star C_h u t control0
  have hsum :
      (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t, (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t z + ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal rate rewards C_star C_h u t z) ∂renewalSourceLaw rate rewards C_star C_h u t) =
        (∫ z, ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation rate rewards C_star C_h u t z ∂renewalSourceLaw rate rewards C_star C_h u t) +
          ∫ z, ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
            rate rewards C_star C_h u t z ∂renewalSourceLaw rate rewards C_star C_h u t :=
    integral_add
      (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable rate rewards C_star C_h u t control0 S0).1
      (ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalObservationTotal rate rewards C_star C_h u t control0)
  have hmass :
      (if hnext : t.val + 1 < p.T then (renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate rate rewards C_star C_h u t hnext) else 0) +
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t =
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t := by
    rw [← ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget.afterCallGateMass_eq_joint_postGateMass]
    exact (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateMass_sum_eq rate rewards C_star C_h u t).symm
  calc
    _ = _ := hsum
    _ ≤ (p.m : ℝ) *
          (if hnext : t.val + 1 < p.T then (renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate rate rewards C_star C_h u t hnext) else 0) +
          (p.m : ℝ) *
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
              rate rewards C_star C_h u t := add_le_add hnext hfuture
    _ = (p.m : ℝ) *
          ((if hnext : t.val + 1 < p.T then (renewalSourceLaw rate rewards C_star C_h u t).real (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate rate rewards C_star C_h u t hnext) else 0) + ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass rate rewards C_star C_h u t) := by rw [mul_add]
    _ = (p.m : ℝ) *
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t := by rw [hmass]

private theorem originalExtendedWeightedArrival_integral_eq_partition
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedWeightedArrival rate rewards C_star C_h z ∂μ) =
      (∑ q : Fin p.T, ∫ z : SourceInput p, ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival rate rewards C_star C_h q z ∂μ) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
              rate rewards C_star C_h u t z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
              rate rewards C_star C_h u t z) ∂renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) : Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t)
        (fun z => nextArrivalObservation rate rewards C_star C_h u t z +
          futureArrivalObservationTotal rate rewards C_star C_h u t z)) μ :=
    zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _
      (weightedCellIncrement_integrable rate rewards C_star C_h control0 S0 u t)
  have hcells : Integrable (fun z : SourceInput p =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w => nextArrivalObservation rate rewards C_star C_h u t w +
            futureArrivalObservationTotal rate rewards C_star C_h u t w) z) μ := by
    apply integrable_finsetSum Finset.univ
    intro u hu
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact hcell u t
  have hcalendar :=
    ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival_integrable
      rate rewards C_star C_h control0
  have hcellMeas (u t : Fin p.T) := weightedCellIncrement_measurable
    rate rewards C_star C_h control0 S0 u t
  have hpoint (z : SourceInput p) :
      originalExtendedWeightedArrival rate rewards C_star C_h z =
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
            rate rewards C_star C_h z +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
              (renewalCallEvent rate rewards C_star C_h u t)
              (fun w => nextArrivalObservation rate rewards C_star C_h u t w +
                futureArrivalObservationTotal rate rewards C_star C_h u t w) z := by
    simp only [originalExtendedWeightedArrival,
      ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationWeightedArrival_eq_calendar]
  calc
    _ = ∫ z : SourceInput p,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
              rate rewards C_star C_h z +
            ∑ u : Fin p.T, ∑ t : Fin p.T,
              ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
                (renewalCallEvent rate rewards C_star C_h u t)
                (fun w => nextArrivalObservation rate rewards C_star C_h u t w +
                  futureArrivalObservationTotal rate rewards C_star C_h u t w) z ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = (∫ z : SourceInput p,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.firstInvocationCalendarWeightedArrival
              rate rewards C_star C_h z ∂μ) +
          ∫ z : SourceInput p,
            ∑ u : Fin p.T, ∑ t : Fin p.T,
              ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
                (renewalCallEvent rate rewards C_star C_h u t)
                (fun w => nextArrivalObservation rate rewards C_star C_h u t w +
                  futureArrivalObservationTotal rate rewards C_star C_h u t w) z ∂μ :=
      integral_add hcalendar hcells
    _ = (∑ q : Fin p.T,
          ∫ z : SourceInput p,
            ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
              rate rewards C_star C_h q z ∂μ) +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
                rate rewards C_star C_h u t,
              (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
                  rate rewards C_star C_h u t z +
                ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
                  rate rewards C_star C_h u t z) ∂renewalSourceLaw rate rewards C_star C_h u t := by
      congr 1
      · exact integral_finsetSum Finset.univ (fun q _ =>
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival_integrable
            rate rewards C_star C_h control0 q)
      · calc
          _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
                ∫ z : SourceInput p,
                  ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
                    (renewalCallEvent rate rewards C_star C_h u t)
                    (fun w => nextArrivalObservation rate rewards C_star C_h u t w +
                      futureArrivalObservationTotal rate rewards C_star C_h u t w) z ∂μ := by
            rw [integral_finsetSum Finset.univ (fun u _ =>
              integrable_finsetSum Finset.univ (fun t _ => hcell u t))]
            apply Finset.sum_congr rfl
            intro u hu
            exact integral_finsetSum Finset.univ (fun t _ => hcell u t)
          _ = _ := by
            apply Finset.sum_congr rfl
            intro u hu
            apply Finset.sum_congr rfl
            intro t ht
            exact integral_zeroExtendCell_on_source rate rewards C_star C_h u t _
              (hcellMeas u t)

private theorem originalCalendar_and_afterCall_mass_le_horizon
    (control0 : TimeControl p) :
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h q control0 +
        (sourceInputLaw p).real
          (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))) +
      (sourceInputLaw p).real
        (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t) ≤ (p.T : ℝ) := by
  let preMass : ℝ := ∑ q : Fin p.T,
    (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h q control0 +
      (sourceInputLaw p).real
        (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))
  let firstCallMass : ℝ := (sourceInputLaw p).real
    (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
      rate rewards C_star C_h)
  let afterCallMass : ℝ := ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
      rate rewards C_star C_h u t
  have hpostMass : afterCallMass =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((if hnext : t.val + 1 < p.T then
            (renewalSourceLaw rate rewards C_star C_h u t).real
              (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext)
          else 0) +
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t) := by
    unfold afterCallMass
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro t ht
    calc
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t =
        ∑ q : Fin p.T,
          (renewalSourceLaw rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate
              rate rewards C_star C_h u t q) :=
        (ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget.afterCallGateMass_eq_joint_postGateMass
          rate rewards C_star C_h u t).symm
      _ = _ := ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateMass_sum_eq
        rate rewards C_star C_h u t
  have hbudget :=
    ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.sum_sourceDateMass_le_horizon
      rate rewards C_star C_h control0
  have hjoined : preMass + firstCallMass + afterCallMass ≤ (p.T : ℝ) := by
    rw [hpostMass]
    simpa only [preMass, firstCallMass] using hbudget
  simpa only [preMass, firstCallMass, afterCallMass] using hjoined

private theorem originalCalendarFloorLoss_integral_le_phaseMass
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p,
      ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
        rate rewards C_star C_h S0 z ∂μ) ≤
      ((p.m : ℝ) / (rate.eta.val * (ConstructorDimensions.D p : ℝ))) *
        ((∑ q : Fin p.T,
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h q control0 +
            (sourceInputLaw p).real
              (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))) +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
              rate rewards C_star C_h)) := by
  let c : ℝ := (p.m : ℝ) /
    (rate.eta.val * (ConstructorDimensions.D p : ℝ))
  let liveSum := fun z : SourceInput p =>
    ∑ q : Fin p.T,
      ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
        rate rewards C_star C_h q S0 z
  let oldSum := fun z : SourceInput p =>
    ∑ q : Fin p.T,
      ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
        rate rewards C_star C_h q S0 z
  let currentSum := fun z : SourceInput p =>
    ∑ u : Fin p.T, ∑ q : Fin p.T,
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
        rate rewards C_star C_h u q S0 z
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hdate (q : Fin p.T) :
      ((∫ z : SourceInput p,
          ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
            rate rewards C_star C_h q S0 z ∂μ) +
        ∫ z : SourceInput p,
          ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
            rate rewards C_star C_h q S0 z ∂μ) +
        ∑ u : Fin p.T, ∫ z : SourceInput p,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u q S0 z ∂μ ≤
      c * (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h q control0 +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
          ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) := by
    have hLive := ReferenceFirstCollectionOriginalCalendarRoundingJoin.integral_calendarFloorLoss_le_sourceCellMass
      rate rewards C_star C_h control0 q S0
    have hOld :=
      ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integral_le_gate_mass
        rate rewards C_star C_h control0 q S0
    have hCurrent :
        (∑ u : Fin p.T, ∫ z : SourceInput p,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u q S0 z ∂μ) ≤
        c * ∑ u : Fin p.T, (sourceInputLaw p).real
          (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q) := by
      calc
        _ ≤ ∑ u : Fin p.T, c * (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q) :=
          Finset.sum_le_sum fun u _ =>
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.integral_currentFloorLoss_le_gateMass
              rate rewards C_star C_h control0 u q S0
        _ = _ := by rw [← Finset.mul_sum]
    calc
      _ ≤
          (c * ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h q control0) +
          c * (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
          c * ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q) :=
        add_le_add (add_le_add hLive hOld) hCurrent
      _ = c * (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h q control0 +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
          ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) := by ring
  have hLiveI : Integrable liveSum μ := integrable_finsetSum Finset.univ fun q _ =>
    ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
      rate rewards C_star C_h q S0 control0
  have hOldI : Integrable oldSum μ := integrable_finsetSum Finset.univ fun q _ =>
    ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
      rate rewards C_star C_h control0 q S0
  have hCurI : Integrable currentSum μ := integrable_finsetSum Finset.univ fun u _ =>
    integrable_finsetSum Finset.univ fun q _ =>
      ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
        rate rewards C_star C_h control0 u q S0
  have hCurrentExchange :
      (∫ z : SourceInput p, ∑ u : Fin p.T, ∑ q : Fin p.T,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u q S0 z ∂μ) =
      ∑ q : Fin p.T, ∑ u : Fin p.T, ∫ z : SourceInput p,
        ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
          rate rewards C_star C_h u q S0 z ∂μ := by
    calc
      _ = ∑ u : Fin p.T, ∑ q : Fin p.T, ∫ z : SourceInput p,
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
            rate rewards C_star C_h u q S0 z ∂μ := by
        rw [integral_finsetSum Finset.univ (fun u _ =>
          integrable_finsetSum Finset.univ (fun q _ =>
            ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
              rate rewards C_star C_h control0 u q S0))]
        apply Finset.sum_congr rfl
        intro u hu
        exact integral_finsetSum Finset.univ fun q _ =>
          ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss_integrable
            rate rewards C_star C_h control0 u q S0
      _ = _ := Finset.sum_comm
  have hFloorTotal :
      (∫ z : SourceInput p, (liveSum z + oldSum z) + currentSum z ∂μ) =
        (∫ z, liveSum z ∂μ) + (∫ z, oldSum z ∂μ) + ∫ z, currentSum z ∂μ := by
    calc
      _ = (∫ z, liveSum z + oldSum z ∂μ) + ∫ z, currentSum z ∂μ :=
        integral_add (hLiveI.add hOldI) hCurI
      _ = _ := by rw [integral_add hLiveI hOldI]
  have hdef : ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
      rate rewards C_star C_h S0 = fun z => (liveSum z + oldSum z) + currentSum z := by
    funext z
    rfl
  have htotal :
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S0 z ∂μ) =
        ∑ q : Fin p.T,
          (((∫ z : SourceInput p,
              ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                rate rewards C_star C_h q S0 z ∂μ) +
            ∫ z : SourceInput p,
              ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                rate rewards C_star C_h q S0 z ∂μ) +
            ∑ u : Fin p.T, ∫ z : SourceInput p,
              ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
                rate rewards C_star C_h u q S0 z ∂μ) := by
    rw [hdef, hFloorTotal,
      integral_finsetSum Finset.univ (fun q _ =>
        ReferenceFirstLiveOriginalCalendarRoundedComparison.integrable_calendarFloorLoss
          rate rewards C_star C_h q S0 control0),
      integral_finsetSum Finset.univ (fun q _ =>
        ReferenceFirstCollectionOldOriginalComparatorRounding.old_comparator_floor_loss_integrable
          rate rewards C_star C_h control0 q S0), hCurrentExchange]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  let preMass : ℝ := ∑ q : Fin p.T,
    (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h q control0 +
      (sourceInputLaw p).real
        (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))
  let firstCallMass : ℝ := (sourceInputLaw p).real
    (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
      rate rewards C_star C_h)
  have hcurr :
      (∑ q : Fin p.T, ∑ u : Fin p.T, (sourceInputLaw p).real
        (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) =
        firstCallMass := by
    dsimp [firstCallMass]
    rw [Finset.sum_comm]
    exact ReferenceFirstCollectionActualCallExponentialQueueEstimate.sum_retainedGate_measures_eq_retainedFirstCall_measure
      rate rewards C_star C_h control0
  calc
    _ = ∑ q : Fin p.T,
          (((∫ z : SourceInput p,
              ReferenceFirstLiveOriginalCalendarRoundedComparison.calendarFloorLoss
                rate rewards C_star C_h q S0 z ∂μ) +
            ∫ z : SourceInput p,
              ReferenceFirstCollectionOldOriginalComparatorRounding.oldComparatorFloorLoss
                rate rewards C_star C_h q S0 z ∂μ) +
            ∑ u : Fin p.T, ∫ z : SourceInput p,
              ReferenceFirstCollectionCurrentOriginalRoundedComparison.floorLoss
                rate rewards C_star C_h u q S0 z ∂μ) := htotal
    _ ≤ ∑ q : Fin p.T, c *
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h q control0 +
            (sourceInputLaw p).real
              (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
            ∑ u : Fin p.T, (sourceInputLaw p).real
              (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) :=
      Finset.sum_le_sum fun q _ => hdate q
    _ = c * (preMass + firstCallMass) := by
      rw [← Finset.mul_sum]
      have hmassSum :
          (∑ q : Fin p.T,
            (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                rate rewards C_star C_h q control0 +
              (sourceInputLaw p).real
                (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
              ∑ u : Fin p.T, (sourceInputLaw p).real
                (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q))) =
            preMass + firstCallMass := by
        simp only [preMass]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcurr]
      rw [hmassSum]

public theorem originalExtendedWeightedArrival_integral_le_horizon
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedWeightedArrival rate rewards C_star C_h z ∂μ) ≤
      (p.m : ℝ) * (p.T : ℝ) := by
  rw [originalExtendedWeightedArrival_integral_eq_partition rate rewards C_star C_h control0 S0]
  let preMass : ℝ := ∑ q : Fin p.T,
    (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h q control0 +
      (sourceInputLaw p).real
        (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))
  let firstCallMass : ℝ := (sourceInputLaw p).real
    (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
      rate rewards C_star C_h)
  let afterCallMass : ℝ := ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
      rate rewards C_star C_h u t
  have hdate : ∀ q : Fin p.T,
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
          rate rewards C_star C_h q z ∂μ) ≤
      (p.m : ℝ) *
        (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
            rate rewards C_star C_h q control0 +
          (sourceInputLaw p).real
            (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
          ∑ u : Fin p.T, (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) := by
    intro q
    exact ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival_integral_le_sourceBudget
      rate rewards C_star C_h control0 q
  have hdates :
      (∑ q : Fin p.T,
        ∫ z : SourceInput p,
          ReferenceFirstCollectionOriginalWeightedArrivalBudget.calendarWeightedArrival
            rate rewards C_star C_h q z ∂μ) ≤
        (p.m : ℝ) * (preMass + firstCallMass) := by
    have hsum := Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) => hdate q
    have hcurr :
        (∑ q : Fin p.T, ∑ u : Fin p.T,
          (sourceInputLaw p).real
            (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) =
          firstCallMass := by
      dsimp [firstCallMass]
      rw [Finset.sum_comm]
      exact ReferenceFirstCollectionActualCallExponentialQueueEstimate.sum_retainedGate_measures_eq_retainedFirstCall_measure
        rate rewards C_star C_h control0
    calc
      _ ≤ ∑ q : Fin p.T, (p.m : ℝ) *
          (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
              rate rewards C_star C_h q control0 +
            (sourceInputLaw p).real
              (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
            ∑ u : Fin p.T, (sourceInputLaw p).real
              (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)) := hsum
      _ = (p.m : ℝ) * (preMass + firstCallMass) := by
        rw [← Finset.mul_sum]
        have hmassSum :
            (∑ q : Fin p.T,
              (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
                  rate rewards C_star C_h q control0 +
                (sourceInputLaw p).real
                  (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) +
                ∑ u : Fin p.T, (sourceInputLaw p).real
                  (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q))) =
              preMass + firstCallMass := by
          simp only [preMass]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcurr]
        rw [hmassSum]
  have hcellSum :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalArrivalObservation
              rate rewards C_star C_h u t z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalObservationTotal
              rate rewards C_star C_h u t z) ∂renewalSourceLaw rate rewards C_star C_h u t) ≤
        (p.m : ℝ) * afterCallMass := by
    have hsum := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
      Finset.sum_le_sum fun t (_ : t ∈ Finset.univ) =>
        weightedCellIncrement_integral_le_afterGate rate rewards C_star C_h control0 S0 u t
    dsimp [afterCallMass]
    calc
      _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
          (p.m : ℝ) * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t := hsum
      _ = (p.m : ℝ) *
          (∑ u : Fin p.T, ∑ t : Fin p.T,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
              rate rewards C_star C_h u t) := by
        calc
          _ = ∑ u : Fin p.T, (p.m : ℝ) *
                ∑ t : Fin p.T,
                  ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                    rate rewards C_star C_h u t := by
            apply Finset.sum_congr rfl
            intro u hu
            rw [← Finset.mul_sum]
          _ = _ := by rw [← Finset.mul_sum]
  have hbudget : preMass + firstCallMass + afterCallMass ≤ (p.T : ℝ) := by
    simpa only [preMass, firstCallMass, afterCallMass] using
      originalCalendar_and_afterCall_mass_le_horizon rate rewards C_star C_h control0
  have hm : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ (p.m : ℝ) * (preMass + firstCallMass) +
        (p.m : ℝ) * afterCallMass := add_le_add hdates hcellSum
    _ = (p.m : ℝ) * (preMass + firstCallMass + afterCallMass) := by ring
    _ ≤ (p.m : ℝ) * (p.T : ℝ) := mul_le_mul_of_nonneg_left hbudget hm

public theorem originalExtendedCost_integral_le_horizon
    (control0 : TimeControl p) :
    (∫ z : SourceInput p, originalExtendedCost rate rewards C_star C_h z ∂μ) ≤
      ((2 / 11 : ℝ) * CanonicalRecordingRates.R p + 3 * (p.m : ℝ)) * (p.T : ℝ) := by
  rw [originalExtendedCost_integral_eq_joined rate rewards C_star C_h control0]
  have hsharp :=
    ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget.original_preCall_afterCall_weighted_backlog_budget_sharp
      rate rewards C_star C_h control0
  rw [ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget.originalCalendarCost] at hsharp
  nlinarith [hsharp]

private theorem integral_renewalZeroExtendSum
    (f : ∀ u t : Fin p.T,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t → ℝ)
    (hf : ∀ u t, Measurable (f u t))
    (hfi : ∀ u t, Integrable (f u t) (renewalSourceLaw rate rewards C_star C_h u t)) :
    (∫ z : SourceInput p, ∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) (f u t) z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t, f u t z ∂renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) : Integrable
      (ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
        (renewalCallEvent rate rewards C_star C_h u t) (f u t)) μ :=
    zeroExtendCell_integrable_on_source rate rewards C_star C_h u t (f u t) (hfi u t)
  calc
    _ = ∑ u : Fin p.T, ∫ z : SourceInput p, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t) (f u t) z ∂μ :=
      integral_finsetSum Finset.univ (fun u _ => integrable_finsetSum Finset.univ (fun t _ => hcell u t))
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T, ∫ z : SourceInput p,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t) (f u t) z ∂μ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_finsetSum Finset.univ (fun t _ => hcell u t)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      exact integral_zeroExtendCell_on_source rate rewards C_star C_h u t (f u t)
        (hf u t)

private theorem originalExtendedRoundedGap_integral_eq_partition
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedRoundedGap rate rewards C_star C_h S0 z ∂μ) =
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
          rate rewards C_star C_h S0 z ∂μ) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
              rate rewards C_star C_h u t S0 z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
              rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) := roundedCellIncrement_integrable
    rate rewards C_star C_h control0 S0 u t
  have hsum : Integrable (fun z : SourceInput p =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w => nextRoundedObservation rate rewards C_star C_h S0 u t w +
            futureRewardComparatorGapTotal rate rewards C_star C_h S0 u t w) z) μ := by
    apply integrable_finsetSum Finset.univ
    intro u hu
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _ (hcell u t)
  have hbase := ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRoundedGap_integrable
    rate rewards C_star C_h control0 S0
  have hf (u t : Fin p.T) := roundedCellIncrement_measurable
    rate rewards C_star C_h control0 S0 u t
  unfold originalExtendedRoundedGap
  rw [integral_add hbase hsum]
  rw [integral_renewalZeroExtendSum rate rewards C_star C_h
    (fun u t z => nextRoundedObservation rate rewards C_star C_h S0 u t z +
      futureRewardComparatorGapTotal rate rewards C_star C_h S0 u t z) hf hcell]

private theorem originalExtendedRawGap_integral_eq_partition
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedRawGap rate rewards C_star C_h S0 z ∂μ) =
      (∫ z : SourceInput p,
        ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
          rate rewards C_star C_h S0 z ∂μ) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S0 z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t := by
  have hcell (u t : Fin p.T) := rawCellIncrement_integrable
    rate rewards C_star C_h control0 S0 u t
  have hsum : Integrable (fun z : SourceInput p =>
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ReferenceFirstCollectionRenewalOriginalWeightedContinuation.zeroExtendCell
          (renewalCallEvent rate rewards C_star C_h u t)
          (fun w => nextComparatorObservation rate rewards C_star C_h S0 u t w +
            futureArrivalComparatorGapTotal rate rewards C_star C_h S0 u t w) z) μ := by
    apply integrable_finsetSum Finset.univ
    intro u hu
    apply integrable_finsetSum Finset.univ
    intro t ht
    exact zeroExtendCell_integrable_on_source rate rewards C_star C_h u t _ (hcell u t)
  have hbase := ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationRawGap_integrable
    rate rewards C_star C_h control0 S0
  have hf (u t : Fin p.T) := rawCellIncrement_measurable
    rate rewards C_star C_h control0 S0 u t
  unfold originalExtendedRawGap
  rw [integral_add hbase hsum]
  rw [integral_renewalZeroExtendSum rate rewards C_star C_h
    (fun u t z => nextComparatorObservation rate rewards C_star C_h S0 u t z +
      futureArrivalComparatorGapTotal rate rewards C_star C_h S0 u t z) hf hcell]

private theorem roundedCellIncrement_integral_le_raw_add_afterGate
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m)
    (u t : Fin p.T) :
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
      (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
          rate rewards C_star C_h u t S0 z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
          rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) ≤
      (∫ z, (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
          rate rewards C_star C_h u t S0 z +
        ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
          rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) +
        cFloor * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t := by
  have hnext :
      (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
          rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) ≤
        (∫ z, ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
            rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) +
          cFloor * (if hnext : t.val + 1 < p.T then
            (renewalSourceLaw rate rewards C_star C_h u t).real
              (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext)
          else 0) := by
    by_cases hq : t.val + 1 < p.T
    · have h := ReferenceFirstCollectionRenewalNextLearningMoments.integral_roundedRewardGap_le_comparator_add_floor
        rate rewards C_star C_h u t control0 hq S0
      simpa [ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation,
        hq] using h
    · simp [ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap,
        ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation,
        hq]
  have hfuture :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integral_futureRewardComparatorGapTotal_le
      rate rewards C_star C_h u t control0 S0
  have hroundInt :=
    (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S0).2.2
  have hcompInt :=
    (ReferenceFirstCollectionRenewalNextLearningMoments.naturalObservations_integrable
      rate rewards C_star C_h u t control0 S0).2.1
  have hfutureRoundInt :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureRewardComparatorGapTotal
      rate rewards C_star C_h u t control0 S0
  have hfutureCompInt :=
    ReferenceFirstCollectionRenewalFutureLearningMoments.integrable_futureArrivalComparatorGapTotal
      rate rewards C_star C_h u t control0 S0
  have hroundAdd := integral_add hroundInt hfutureRoundInt
  have hcompAdd := integral_add hcompInt hfutureCompInt
  have hmass :
      (if hnext : t.val + 1 < p.T then
          (renewalSourceLaw rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
              rate rewards C_star C_h u t hnext)
        else 0) +
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t =
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t := by
    rw [← ReferenceFirstCollectionRenewalSharpOriginalWeightedBudget.afterCallGateMass_eq_joint_postGateMass]
    exact (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateMass_sum_eq
      rate rewards C_star C_h u t).symm
  calc
    _ = (∫ z, ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
            rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) +
          ∫ z, ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
            rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t := hroundAdd
    _ ≤ ((∫ z, ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) +
            cFloor * (if hnext : t.val + 1 < p.T then
              (renewalSourceLaw rate rewards C_star C_h u t).real
                (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                  rate rewards C_star C_h u t hnext)
            else 0)) +
          ((∫ z, ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) +
            cFloor * ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
              rate rewards C_star C_h u t) := add_le_add hnext hfuture
    _ = ((∫ z, ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) +
          ∫ z, ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S0 z ∂renewalSourceLaw rate rewards C_star C_h u t) +
          cFloor * ((if hnext : t.val + 1 < p.T then
            (renewalSourceLaw rate rewards C_star C_h u t).real
              (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext)
          else 0) +
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
              rate rewards C_star C_h u t) := by ring
    _ = (∫ z, (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S0 z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) +
          cFloor * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t := by
      rw [← hmass, ← hcompAdd]
    _ = _ := by ring

public theorem integral_originalExtendedRoundedGap_le_raw_add_floor
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedRoundedGap rate rewards C_star C_h S0 z ∂μ) ≤
      (∫ z : SourceInput p, originalExtendedRawGap rate rewards C_star C_h S0 z ∂μ) +
        (∫ z : SourceInput p,
          ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
            rate rewards C_star C_h S0 z ∂μ) +
        cFloor * (∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t) := by
  have hbase :=
    ReferenceFirstCollectionOriginalCalendarRoundingJoin.integral_originalCalendarRoundedGap_le_raw_add_floorLoss
      rate rewards C_star C_h control0 S0
  have hrawEq :
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRawGap
          rate rewards C_star C_h S0 z ∂μ) =
        ∫ z : SourceInput p,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S0 z ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z =>
      ReferenceFirstCollectionOriginalPrefixRoundedLearning.originalCalendarRawGap_eq_firstInvocationRawGap
        rate rewards C_star C_h S0 z
  have hbase' :
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarRoundedGap
          rate rewards C_star C_h S0 z ∂μ) ≤
        (∫ z : SourceInput p,
          ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationRawGap
            rate rewards C_star C_h S0 z ∂μ) +
          ∫ z : SourceInput p,
            ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
              rate rewards C_star C_h S0 z ∂μ := by
    calc
      _ ≤ _ := hbase
      _ = _ := by rw [hrawEq]
  have hcell :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalRoundedRewardGap
              rate rewards C_star C_h u t S0 z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureRewardComparatorGapTotal
              rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) ≤
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
          (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
              rate rewards C_star C_h u t S0 z +
            ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
              rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) +
        cFloor * (∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t) := by
    calc
      _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
            ((∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
                rate rewards C_star C_h u t,
              (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                  rate rewards C_star C_h u t S0 z +
                ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                  rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) +
              cFloor * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                rate rewards C_star C_h u t) := by
        apply Finset.sum_le_sum
        intro u hu
        apply Finset.sum_le_sum
        intro t ht
        exact roundedCellIncrement_integral_le_raw_add_afterGate
          rate rewards C_star C_h control0 S0 u t
      _ = _ := by
        have hsplit :
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              ((∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
                  rate rewards C_star C_h u t,
                (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                    rate rewards C_star C_h u t S0 z +
                  ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                    rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) +
                cFloor * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                  rate rewards C_star C_h u t)) =
              (∑ u : Fin p.T, ∑ t : Fin p.T,
                ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
                    rate rewards C_star C_h u t,
                  (ReferenceFirstCollectionRenewalNextLearningMoments.naturalComparatorObservation
                      rate rewards C_star C_h u t S0 z +
                    ReferenceFirstCollectionRenewalFutureLearningMoments.futureArrivalComparatorGapTotal
                      rate rewards C_star C_h u t S0 z) ∂renewalSourceLaw rate rewards C_star C_h u t) +
                ∑ u : Fin p.T, ∑ t : Fin p.T,
                  cFloor * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                    rate rewards C_star C_h u t := by
          simp_rw [Finset.sum_add_distrib]
        have hfactor :
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              cFloor * ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                rate rewards C_star C_h u t) =
              cFloor * (∑ u : Fin p.T, ∑ t : Fin p.T,
                ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                  rate rewards C_star C_h u t) := by
          calc
            _ = ∑ u : Fin p.T, cFloor *
                  (∑ t : Fin p.T,
                    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                      rate rewards C_star C_h u t) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]
        rw [hsplit, hfactor]
  have hcombined := add_le_add hbase' hcell
  rw [originalExtendedRoundedGap_integral_eq_partition rate rewards C_star C_h control0 S0,
    originalExtendedRawGap_integral_eq_partition rate rewards C_star C_h control0 S0]
  calc
    _ ≤ _ := hcombined
    _ = _ := by ring

/-- One complete endpoint normalizer and the shared original-source cost and
arrival integrals give the expected raw comparator bound. -/
public theorem integral_originalExtendedRawGap_le_horizon
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedRawGap rate rewards C_star C_h S0 z ∂μ) ≤
      Real.log (Nat.choose p.K p.m : ℝ) /
          RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) := by
  have hraw := originalExtendedRawGap_integral_le_cost_and_arrival
    rate rewards C_star C_h control0 S0
  have hcost := originalExtendedCost_integral_le_horizon
    rate rewards C_star C_h control0
  have harrival := originalExtendedWeightedArrival_integral_le_horizon
    rate rewards C_star C_h control0 S0
  have heta0 : 0 < rate.eta.val := rate.eta.property
  have heta : 0 ≤ 8 * rate.eta.val := by positivity
  calc
    _ ≤ B + 8 * rate.eta.val *
          ((∫ z, originalExtendedCost rate rewards C_star C_h z ∂μ) +
            ∫ z, originalExtendedWeightedArrival rate rewards C_star C_h z ∂μ) := hraw
    _ ≤ B + 8 * rate.eta.val *
          (((2 / 11 : ℝ) * CanonicalRecordingRates.R p +
              3 * (p.m : ℝ)) * (p.T : ℝ) +
            (p.m : ℝ) * (p.T : ℝ)) := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left (add_le_add hcost harrival) heta) _
    _ = _ := by ring

public theorem integral_originalExtendedRoundedGap_le_horizon
    (control0 : TimeControl p) (S0 : ProductSetLaw.ProductSet p.K p.m) :
    (∫ z : SourceInput p, originalExtendedRoundedGap rate rewards C_star C_h S0 z ∂μ) ≤
      Real.log (Nat.choose p.K p.m : ℝ) / RecordedPotentialStep.potentialLambda Q +
        16 * (p.m : ℝ) ^ 2 * RecordedPotentialStep.potentialLambda Q * (p.T : ℝ) +
        (p.m : ℝ) / (16 * rate.eta.val) +
        ((16 / 11 : ℝ) * CanonicalRecordingRates.R p + 32 * (p.m : ℝ)) *
          rate.eta.val * (p.T : ℝ) + (p.m : ℝ) * (p.T : ℝ) /
            (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
  let pre : ℝ :=
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h q control0 +
        (sourceInputLaw p).real
          (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))) +
      (sourceInputLaw p).real
        (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h)
  let after : ℝ := ∑ u : Fin p.T, ∑ t : Fin p.T,
    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
      rate rewards C_star C_h u t
  have hmass : pre + after ≤ (p.T : ℝ) := by
    simpa [pre, after] using
      originalCalendar_and_afterCall_mass_le_horizon rate rewards C_star C_h control0
  have hc : 0 ≤ cFloor := div_nonneg (Nat.cast_nonneg _) (le_of_lt
    (mul_pos rate.eta.property (by exact_mod_cast ConstructorDimensions.D_pos p)))
  have hfloor := originalCalendarFloorLoss_integral_le_phaseMass
    rate rewards C_star C_h control0 S0
  have hfloor' :
      (∫ z : SourceInput p,
        ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
          rate rewards C_star C_h S0 z ∂μ) + cFloor * after ≤ cFloor * (p.T : ℝ) := by
    calc
      _ ≤ cFloor * pre + cFloor * after := by
        simpa [pre] using add_le_add_right hfloor (cFloor * after)
      _ = cFloor * (pre + after) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmass hc
  have hraw := integral_originalExtendedRawGap_le_horizon
    rate rewards C_star C_h control0 S0
  have hround := integral_originalExtendedRoundedGap_le_raw_add_floor
    rate rewards C_star C_h control0 S0
  calc
    _ ≤ (∫ z, originalExtendedRawGap rate rewards C_star C_h S0 z ∂μ) +
          ((∫ z, ReferenceFirstCollectionOriginalCalendarRoundingJoin.originalCalendarFloorLoss
              rate rewards C_star C_h S0 z ∂μ) + cFloor * after) := by
      simpa [add_assoc] using hround
    _ ≤ _ := add_le_add hraw hfloor'
    _ = _ := by ring

end Bandits.Support.ReferenceFirstCollectionRenewalOriginalPrefixLearning

end
