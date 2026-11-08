/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ActualCompleteSourceEventRewardCoupling
public import Bandits.Support.ReferenceCompleteErrorSelectedRowProbability
public import Bandits.Support.ExecutionRegretComparison

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Ring

/-!
# Actual/reference expectation comparison at a fixed complete output

Sources: `sources/zip4/manuscript/08_main_theorem.tex:29-75` and
`sources/zip4/manuscript/07_public_setup.tex:123-164`.

The comparison integrates over the original extended private law at every
whole published output. The complete four-error union and the actual virtual
forward-test event are literal private sections. The resulting regret
corollary keeps the original selected-index row average.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions
open Bandits.Support.CompletePublicTable
open Bandits.Support.BootstrapPrivateRoundStreams

namespace Bandits.Support.ActualCompleteReferenceErrorRowComparison

variable {p : ConstructorDimensions.Parameters}

/-- The literal private section of the accepted four-event complete error. -/
def completeErrorPrivateEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    Set (ExtendedPrivateCoordinates p) :=
  {e | (published, e) ∈
    ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
      rate rewards C_star C_h}

/-- The literal private section of the actual finite-index virtual forward
pass event, with the selected index computed from the same original private
coordinates. -/
def falseForwardPrivateEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    Set (ExtendedPrivateCoordinates p) :=
  {e | (published, e) ∈
    GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
      C_star C_h rate.eta rewards
      (ActualInitializationPhysicalStep.selectedRowIndex p (published, e))}

/-- Original-private probability of the fixed-output complete-error event. -/
def completeErrorPrivateMass
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) : ℝ :=
  (extendedPrivateLaw p).real
    (completeErrorPrivateEvent rate rewards C_star C_h published)

/-- Original-private probability of the fixed-output actual forward-test
event. -/
def falseForwardPrivateMass
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) : ℝ :=
  (extendedPrivateLaw p).real
    (falseForwardPrivateEvent rate rewards C_star C_h published)

/-- The actual expected regret observation at a fixed whole published output,
using the existing actual complete-history reward on the full original
private carrier. -/
def actualPrivateExpectedRegret
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) : ℝ :=
  ReferenceCompleteSelectedRowExpectation.gridComparator p rewards -
    ∫ e : ExtendedPrivateCoordinates p,
      ActualCompleteHistoryRewardReadouts.fixedPublicSourceInitializedActualCompleteTotalReward
        (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
        (rewards := rewards) published e ∂extendedPrivateLaw p

private theorem measurableSet_completeErrorPrivateEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    MeasurableSet (completeErrorPrivateEvent rate rewards C_star C_h published) := by
  exact (ReferenceCompleteErrorSelectedRowProbability.measurableSet_completeErrorEvent
    rate rewards C_star C_h).preimage (measurable_const.prodMk measurable_id)

private theorem measurableSet_falseForwardPrivateEvent
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    MeasurableSet (falseForwardPrivateEvent rate rewards C_star C_h published) := by
  have hevent : falseForwardPrivateEvent rate rewards C_star C_h published =
      ⋃ j : Fin (ConstructorDimensions.M p),
        ReferenceCompleteSelectedRowExpectation.indexCell p j ∩
          {e : ExtendedPrivateCoordinates p |
            (published, e) ∈
              GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
                C_star C_h rate.eta rewards j} := by
    ext e
    simp only [falseForwardPrivateEvent, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff]
    constructor
    · intro hpass
      refine ⟨ActualInitializationPhysicalStep.selectedRowIndex p (published, e), ?_, hpass⟩
      change PrivateSourceStreams.coordinatorIndex p e.1.2 = _
      rfl
    · rintro ⟨j, hindex, hpass⟩
      have hselected : ActualInitializationPhysicalStep.selectedRowIndex p
          (published, e) = j := by
        change PrivateSourceStreams.coordinatorIndex p e.1.2 = j at hindex ⊢
        exact hindex
      simpa only [hselected] using hpass
  rw [hevent]
  refine MeasurableSet.iUnion fun j => ?_
  apply (ReferenceCompleteSelectedRowExpectation.measurableSet_indexCell p j).inter
  exact (GeneratedFalseForwardEvent.measurableSet_actualAnyFalseForwardPrefixPassSet
    C_star C_h rate.eta rewards j).preimage
      (measurable_const.prodMk measurable_id)

private theorem completeErrorPrivateMass_eq_fixedRowAverage
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    completeErrorPrivateMass rate rewards C_star C_h published =
      (1 / (ConstructorDimensions.M p : ℝ)) *
        ∑ j : Fin (ConstructorDimensions.M p),
          ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
            rate rewards C_star C_h published.1 j (published.2 j) := by
  have hmeas := measurableSet_completeErrorPrivateEvent
    rate rewards C_star C_h published
  have hindicator :
      (fun e : ExtendedPrivateCoordinates p =>
        ReferenceCompleteErrorSelectedRowProbability.completeErrorIndicator
          rate rewards C_star C_h (published, e)) =
        (completeErrorPrivateEvent rate rewards C_star C_h published).indicator
          (fun _ : ExtendedPrivateCoordinates p => (1 : ℝ)) := by
    funext e
    rfl
  calc
    _ = ∫ e : ExtendedPrivateCoordinates p,
          (completeErrorPrivateEvent rate rewards C_star C_h published).indicator
            (fun _ => (1 : ℝ)) e ∂extendedPrivateLaw p := by
      unfold completeErrorPrivateMass
      exact (integral_indicator_one hmeas).symm
    _ = ∫ e : ExtendedPrivateCoordinates p,
          ReferenceCompleteErrorSelectedRowProbability.completeErrorIndicator
            rate rewards C_star C_h (published, e) ∂extendedPrivateLaw p := by
      rw [hindicator]
    _ = _ :=
      ReferenceCompleteErrorSelectedRowProbability.completeError_privateExpectation_eq_fixedRowAverage
        rate rewards C_star C_h published.1 published.2

private theorem completeErrorPrivateMass_nonneg
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    0 ≤ completeErrorPrivateMass rate rewards C_star C_h published := by
  change 0 ≤ ((extendedPrivateLaw p)
    (completeErrorPrivateEvent rate rewards C_star C_h published)).toReal
  exact ENNReal.toReal_nonneg

private theorem falseForwardPrivateMass_nonneg
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    0 ≤ falseForwardPrivateMass rate rewards C_star C_h published := by
  change 0 ≤ ((extendedPrivateLaw p)
    (falseForwardPrivateEvent rate rewards C_star C_h published)).toReal
  exact ENNReal.toReal_nonneg

/-- At every fixed whole published output, actual and reference expected
regrets differ by at most `m*T` times the original-private probabilities of
the literal complete-error and actual virtual-forward events. -/
theorem actualPrivateExpectedRegret_le_reference_add_exceptionalMass
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    actualPrivateExpectedRegret rate rewards C_star C_h published ≤
      ReferenceCompleteSelectedRowExpectation.gridComparator p rewards -
        ∫ e : ExtendedPrivateCoordinates p,
          ReferenceCompletePhysicalRewards.completeReward rate (published, e)
            rewards C_star C_h ∂extendedPrivateLaw p +
        ((p.m : ℝ) * (p.T : ℝ)) *
          (completeErrorPrivateMass rate rewards C_star C_h published +
            falseForwardPrivateMass rate rewards C_star C_h published) := by
  let actualReward :=
    ActualCompleteHistoryRewardReadouts.fixedPublicSourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) published
  let referenceReward := fun e : ExtendedPrivateCoordinates p =>
    ReferenceCompletePhysicalRewards.completeReward rate (published, e) rewards C_star C_h
  let bad := completeErrorPrivateEvent rate rewards C_star C_h published
  let forward := falseForwardPrivateEvent rate rewards C_star C_h published
  let μ := extendedPrivateLaw p
  have hactualInt : Integrable actualReward μ := by
    exact ActualCompleteHistoryRewardReadouts.integrable_fixedPublicSourceInitializedActualCompleteTotalReward
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) published
  have hreferenceInt : Integrable referenceReward μ := by
    exact ReferenceCompleteRewardMeasurability.integrable_completeReward_privateSection
      rate rewards C_star C_h published
  have hbound : 0 ≤ (p.m : ℝ) * (p.T : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hactualBounds : ∀ᵐ e ∂μ, actualReward e ∈
      Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
    refine ae_of_all _ fun e => ?_
    exact ActualCompleteHistoryRewardReadouts.sourceInitializedActualCompleteTotalReward_bounds
      (p := p) (rate := rate) (C_star := C_star) (C_h := C_h)
      (rewards := rewards) (published, e)
  have hreferenceBounds : ∀ᵐ e ∂μ, referenceReward e ∈
      Set.Icc (0 : ℝ) ((p.m : ℝ) * (p.T : ℝ)) := by
    refine ae_of_all _ fun e => ?_
    exact ReferenceCompletePhysicalRewards.completeReward_bounds rate
      (published, e) rewards C_star C_h
  have hbadMeas : MeasurableSet bad :=
    measurableSet_completeErrorPrivateEvent rate rewards C_star C_h published
  have hforwardMeas : MeasurableSet forward :=
    measurableSet_falseForwardPrivateEvent rate rewards C_star C_h published
  have hequal : ∀ᵐ e ∂μ, e ∉ (bad ∪ forward) → actualReward e = referenceReward e := by
    refine ae_of_all _ fun e hevents => ?_
    have hnotBad : e ∉ bad := fun h => hevents (Or.inl h)
    have hnotForward : e ∉ forward := fun h => hevents (Or.inr h)
    let source : BootstrapPrivateRoundStreams.SourceInput p := (published, e)
    have hnotComplete : source ∉
        ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent
          rate rewards C_star C_h := by
      exact hnotBad
    have hnotInitialization : source ∉
        ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent
          rate rewards C_star C_h := by
      intro hinit
      apply hnotComplete
      simp [ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent, hinit]
    have hgenerated :
        ReferenceCompletePhysicalHistory.generatedInput rate source rewards C_star C_h =
          ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate := rfl
    have hinit : ¬ InitializationFailureProvenance.operationalInitializationFailure
        (ActualReferenceInitializationBlock.referenceInput source rewards C_star C_h rate) := by
      intro hoperational
      apply hnotInitialization
      apply (ReferenceCompleteErrorSelectedRowProbability.sourceInitializationFailureEvent_iff_operational
        rate rewards C_star C_h source).mpr
      simpa only [hgenerated] using hoperational
    have hwrong : source ∉
        ReferenceCompleteInclusivePhysicalDecoderErrors.stoppedOrdinaryWrongCompletionEvent
          rate rewards C_star C_h := by
      intro hfalse
      apply hnotComplete
      simp [ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent, hfalse]
    have hfalseForward : source ∉
        GeneratedFalseForwardEvent.actualAnyFalseForwardPrefixPassSet
          C_star C_h rate.eta rewards
          (ActualInitializationPhysicalStep.selectedRowIndex p source) := hnotForward
    have hnoOverflow : source ∉
        ReferenceCompletePhysicalCalendarFirstCrossing.physicalFirstOverflowEvent
          rate rewards C_star C_h := by
      intro hoverflow
      apply hnotComplete
      simp [ReferenceCompleteErrorSelectedRowProbability.completeErrorEvent, hoverflow]
    have hcoupling :=
      ActualCompleteSourceEventRewardCoupling.actualSourceExceptionalEvent_reward_prefix_and_noOverflow_total
        p rate source rewards C_star C_h hinit hfalseForward hwrong
    have hreward := hcoupling.2 hnoOverflow
    exact hreward
  have hcomparison := ExecutionRegretComparison.comparator_minus_integral_le_of_bad_event_mass
    μ actualReward referenceReward hactualInt hreferenceInt
    ((p.m : ℝ) * (p.T : ℝ)) hbound bad forward hbadMeas hforwardMeas
    hactualBounds hreferenceBounds hequal
    (ReferenceCompleteSelectedRowExpectation.gridComparator p rewards)
  change ReferenceCompleteSelectedRowExpectation.gridComparator p rewards -
      ∫ e : ExtendedPrivateCoordinates p,
        actualReward e ∂μ ≤ _
  simpa only [actualReward, referenceReward, bad, forward, μ,
    completeErrorPrivateMass, falseForwardPrivateMass] using hcomparison

/-- Fixed-output source-compatible row-average regret bound. It uses the same
original-index private row probabilities as the complete reference regret,
and retains the full extended private law in the forward-event mass. -/
theorem actualPrivateExpectedRegret_le_fixedRowAverage
    (rate : ActualCompleteHistoryRewardReadouts.RateInput p)
    (rewards : ActualInitializationPhysicalStep.GridRewardTable p)
    (C_star C_h : ℝ) (published : PublishedOutput p) :
    actualPrivateExpectedRegret rate rewards C_star C_h published ≤
      (1 / (ConstructorDimensions.M p : ℝ)) *
        (∑ j : Fin (ConstructorDimensions.M p),
          (ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
              rate rewards C_star C_h published.1 j (published.2 j) +
            (2 * (p.m : ℝ) * (p.T : ℝ)) *
              ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                rate rewards C_star C_h published.1 j (published.2 j))) +
      (2 * (p.m : ℝ) * (p.T : ℝ)) *
        falseForwardPrivateMass rate rewards C_star C_h published := by
  have hcomparison := actualPrivateExpectedRegret_le_reference_add_exceptionalMass
    rate rewards C_star C_h published
  have herrorAverage := completeErrorPrivateMass_eq_fixedRowAverage
    rate rewards C_star C_h published
  have hreferenceRegret :=
    ReferenceCompleteSelectedRowExpectation.referenceRegret_eq_uniform_fixedRows
      rate rewards C_star C_h published
  have hreferenceIntegral :
      ReferenceCompleteSelectedRowExpectation.gridComparator p rewards -
          ∫ e : ExtendedPrivateCoordinates p,
            ReferenceCompletePhysicalRewards.completeReward rate (published, e)
              rewards C_star C_h ∂extendedPrivateLaw p =
        (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
              rate rewards C_star C_h published.1 j (published.2 j) := by
    simpa only [ReferenceCompleteRewardMeasurability.completePrivateExpectedReward] using
      hreferenceRegret
  have herrNonneg := completeErrorPrivateMass_nonneg rate rewards C_star C_h published
  have hforwardNonneg := falseForwardPrivateMass_nonneg rate rewards C_star C_h published
  have hmassNonneg :
      0 ≤ completeErrorPrivateMass rate rewards C_star C_h published +
        falseForwardPrivateMass rate rewards C_star C_h published :=
    add_nonneg herrNonneg hforwardNonneg
  have hcoefficient :
      (p.m : ℝ) * (p.T : ℝ) ≤ 2 * (p.m : ℝ) * (p.T : ℝ) := by
    have hmt : 0 ≤ (p.m : ℝ) * (p.T : ℝ) :=
      mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    calc
      (p.m : ℝ) * (p.T : ℝ) ≤ 2 * ((p.m : ℝ) * (p.T : ℝ)) := by linarith
      _ = 2 * (p.m : ℝ) * (p.T : ℝ) := (mul_assoc _ _ _).symm
  have hmassScale := mul_le_mul_of_nonneg_right hcoefficient hmassNonneg
  have hrowCombine :
      (1 / (ConstructorDimensions.M p : ℝ)) *
          ∑ j : Fin (ConstructorDimensions.M p),
            (ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
                rate rewards C_star C_h published.1 j (published.2 j) +
              (2 * (p.m : ℝ) * (p.T : ℝ)) *
                ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                  rate rewards C_star C_h published.1 j (published.2 j)) =
        (1 / (ConstructorDimensions.M p : ℝ)) *
            ∑ j : Fin (ConstructorDimensions.M p),
              ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
                rate rewards C_star C_h published.1 j (published.2 j) +
          (2 * (p.m : ℝ) * (p.T : ℝ)) *
            ((1 / (ConstructorDimensions.M p : ℝ)) *
              ∑ j : Fin (ConstructorDimensions.M p),
                ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                  rate rewards C_star C_h published.1 j (published.2 j)) := by
    have hsumScale :
        (2 * (p.m : ℝ) * (p.T : ℝ)) *
            (∑ j : Fin (ConstructorDimensions.M p),
              ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                rate rewards C_star C_h published.1 j (published.2 j)) =
          ∑ j : Fin (ConstructorDimensions.M p),
            (2 * (p.m : ℝ) * (p.T : ℝ)) *
              ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                rate rewards C_star C_h published.1 j (published.2 j) := by
      rw [Finset.mul_sum]
    rw [Finset.sum_add_distrib, mul_add]
    rw [← hsumScale]
    ring
  calc
    _ ≤ ReferenceCompleteSelectedRowExpectation.gridComparator p rewards -
          ∫ e : ExtendedPrivateCoordinates p,
            ReferenceCompletePhysicalRewards.completeReward rate (published, e)
              rewards C_star C_h ∂extendedPrivateLaw p +
          (2 * (p.m : ℝ) * (p.T : ℝ)) *
            (completeErrorPrivateMass rate rewards C_star C_h published +
              falseForwardPrivateMass rate rewards C_star C_h published) := by
      calc
        _ ≤ ReferenceCompleteSelectedRowExpectation.gridComparator p rewards -
              ∫ e : ExtendedPrivateCoordinates p,
                ReferenceCompletePhysicalRewards.completeReward rate (published, e)
                  rewards C_star C_h ∂extendedPrivateLaw p +
              ((p.m : ℝ) * (p.T : ℝ)) *
                (completeErrorPrivateMass rate rewards C_star C_h published +
                  falseForwardPrivateMass rate rewards C_star C_h published) := hcomparison
        _ ≤ _ := add_le_add (le_refl _) hmassScale
    _ = (1 / (ConstructorDimensions.M p : ℝ)) *
          (∑ j : Fin (ConstructorDimensions.M p),
            (ReferenceCompleteSelectedRowExpectation.fixedRowPrivateExpectedRegret
                rate rewards C_star C_h published.1 j (published.2 j) +
              (2 * (p.m : ℝ) * (p.T : ℝ)) *
                ReferenceCompleteErrorSelectedRowProbability.completeErrorFixedRowProbability
                  rate rewards C_star C_h published.1 j (published.2 j))) +
          (2 * (p.m : ℝ) * (p.T : ℝ)) *
            falseForwardPrivateMass rate rewards C_star C_h published := by
      rw [hreferenceIntegral, herrorAverage]
      rw [hrowCombine]
      ring

end Bandits.Support.ActualCompleteReferenceErrorRowComparison

end
