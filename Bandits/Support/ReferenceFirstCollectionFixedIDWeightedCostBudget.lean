/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Bandits Lean Project contributors
-/
module

public import Bandits.Support.ReferenceFirstCollectionOriginalPrefixLearning
public import Bandits.Support.ReferenceFirstCollectionPrecallFixedIDMean

import Mathlib.Tactic

/-!
# Fixed-ID first-invocation quadratic cost budget

This result localizes the actual first-invocation quadratic cost on each
literal fixed-ID cylinder of the unchanged original source law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionFixedIDWeightedCostBudget

open ConstructorDimensions (Parameters)
open ReferenceActivePhysicalStep (RateInput)
open ActualInitializationPhysicalStep (GridRewardTable)
open ContinuousLearningRows (TimeControl)
open BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)

variable {p : Parameters}
  (rate : RateInput p) (rewards : GridRewardTable p)
  (C_star C_h : ℝ) (control0 : TimeControl p)
  (ids : CompletePublicTable.IDArray p)

private local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

include control0 in
/-- The fixed-ID mass admitted by the mutually exclusive first-live, old, and
current-event gates at one physical date is bounded by that ID's atom mass. -/
public theorem fixedIDCalendarMass_le (t : Fin p.T) :
    (sourceInputLaw p).real
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
      (sourceInputLaw p).real
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) +
      ∑ u : Fin p.T, (sourceInputLaw p).real
        (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
          ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) ≤
      (CompletePublicTable.idArrayMeasure p).real {ids} := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let P := ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4
  let O := ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t
  let Q : Fin p.T → Set (SourceInput p) := fun u =>
    ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
  have hD : MeasurableSet D := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hP : MeasurableSet P :=
    ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_sourcePhase234
      rate rewards C_star C_h t control0
  have hO : MeasurableSet O :=
    ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_G_ambient
      rate rewards C_star C_h t control0
  have hQ (u : Fin p.T) : MeasurableSet (Q u) :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.measurableSet_currentRetainedGate_ambient
      rate rewards C_star C_h t control0 u
  have hQQ : Pairwise (fun u v : Fin p.T => Disjoint (Q u) (Q v)) :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.currentRetainedGate_pairwise_disjoint
      rate rewards C_star C_h t
  have hDQQ : Pairwise (fun u v : Fin p.T => Disjoint (D ∩ Q u) (D ∩ Q v)) := by
    intro u v huv
    exact (hQQ huv).mono Set.inter_subset_right Set.inter_subset_right
  have hQmass : ∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ Q u) =
      (sourceInputLaw p).real (D ∩ ⋃ u : Fin p.T, Q u) := by
    rw [← measureReal_iUnion_fintype hDQQ (fun u => hD.inter (hQ u))]
    congr 1
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    tauto
  have hPO : Disjoint P O :=
    Set.disjoint_left.mpr (by
      intro z hzP hzO
      exact (Set.disjoint_left.mp
        (ReferenceFirstCollectionPrecallLiveOldMass.old_event_disjoint_source_phases
          rate rewards C_star C_h t control0)) hzO.1.1 hzP)
  have hPq : Disjoint P (⋃ u : Fin p.T, Q u) :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.sourcePhase234_disjoint_currentRetainedGateUnion
      rate rewards C_star C_h t control0
  have hOq : Disjoint O (⋃ u : Fin p.T, Q u) :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.oldG_disjoint_currentRetainedGateUnion
      rate rewards C_star C_h t
  have hbaseCall : Disjoint (D ∩ (P ∪ O)) (D ∩ ⋃ u : Fin p.T, Q u) := by
    apply Set.disjoint_left.mpr
    intro z hzBase hzCall
    rcases hzBase.2 with hzP | hzO
    · exact (Set.disjoint_left.mp hPq) hzP hzCall.2
    · exact (Set.disjoint_left.mp hOq) hzO hzCall.2
  have hcallMeas : MeasurableSet (D ∩ ⋃ u : Fin p.T, Q u) :=
    hD.inter (MeasurableSet.iUnion hQ)
  have hbaseSplit : (sourceInputLaw p).real (D ∩ P) +
      (sourceInputLaw p).real (D ∩ O) = (sourceInputLaw p).real (D ∩ (P ∪ O)) := by
    rw [← measureReal_union (hPO.mono Set.inter_subset_right Set.inter_subset_right)
      (hD.inter hO)]
    congr 1
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff]
    tauto
  have hlocalUnion :
      (sourceInputLaw p).real (D ∩ (P ∪ O)) +
        (sourceInputLaw p).real (D ∩ ⋃ u : Fin p.T, Q u) ≤
        (sourceInputLaw p).real D := by
    rw [← measureReal_union hbaseCall hcallMeas]
    exact measureReal_mono (by
      intro z hz
      rcases hz with hz | hz
      · exact hz.1
      · exact hz.1)
  have hDmass : (sourceInputLaw p).real D =
      (CompletePublicTable.idArrayMeasure p).real {ids} := by
    exact ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection ids
  change (sourceInputLaw p).real (D ∩ P) + (sourceInputLaw p).real (D ∩ O) +
      ∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ Q u) ≤
    (CompletePublicTable.idArrayMeasure p).real {ids}
  calc
    _ = (sourceInputLaw p).real (D ∩ (P ∪ O)) +
        (sourceInputLaw p).real (D ∩ ⋃ u : Fin p.T, Q u) := by
      rw [hbaseSplit, hQmass]
    _ ≤ (sourceInputLaw p).real D := hlocalUnion
    _ = (CompletePublicTable.idArrayMeasure p).real {ids} := hDmass

include control0 in
/-- The current first-call energy drift is localized on the fixed-ID cylinder. -/
public theorem fixedIDCurrentEnergyBudget (u t : Fin p.T) :
    (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
        ReferenceFirstCollectionCurrentQueueEnergy.VPlus
        rate rewards C_star C_h u t z -
      ReferenceFirstCollectionCurrentQueueEnergy.VMinus
        rate rewards C_star C_h u t z ∂sourceInputLaw p) +
      (11 / 2 : ℝ) *
        (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
          (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
            rate rewards C_star C_h u t) z ∂sourceInputLaw p) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real
          (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
            ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t) := by
  let B := ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
    rate rewards C_star C_h u t
  let G := ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u t
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hD : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] D :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids t.val
  have hle :
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1) ≤
        (inferInstance : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet G := hle _
    (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
      rate rewards C_star C_h control0 u t)
  have hB : Integrable B (sourceInputLaw p) :=
    ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_integrable
      rate rewards C_star C_h control0 u t
  have hDG : MeasurableSet (D ∩ G) := (hle _ hD).inter hG
  have hmasked : Integrable (fun z : SourceInput p => (D ∩ G).indicator B z)
      (sourceInputLaw p) := hB.indicator hDG
  have hmaskedOne : Integrable
      (fun z : SourceInput p => (D ∩ G).indicator (fun _ => (1 : ℝ)) z)
      (sourceInputLaw p) := (integrable_const (1 : ℝ)).indicator hDG
  have hstep := ReferenceFirstCollectionCurrentConditionalWeightedDrift.sourceSetIntegral_energy_drift
    rate rewards C_star C_h control0 u t D hD
  have hsplit :
      (∫ z in D, G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z ∂sourceInputLaw p) =
        C * (sourceInputLaw p).real (D ∩ G) -
          (11 / 2 : ℝ) * (∫ z in D, G.indicator B z ∂sourceInputLaw p) := by
    rw [setIntegral_indicator hG]
    have hfun : (fun z : SourceInput p => (D ∩ G).indicator
        (fun x => C - (11 / 2 : ℝ) * B x) z) =
        (fun z => C * (D ∩ G).indicator (fun _ => (1 : ℝ)) z +
          (-(11 / 2 : ℝ)) * (D ∩ G).indicator B z) := by
      funext z
      by_cases hz : z ∈ D ∩ G
      · simp [Set.indicator, hz]
        ring
      · simp [Set.indicator, hz]
    have hmassIntegral :
        (∫ z : SourceInput p, (D ∩ G).indicator (fun _ => (1 : ℝ)) z ∂sourceInputLaw p) =
          (sourceInputLaw p).real (D ∩ G) := by
      rw [integral_indicator hDG, integral_const, smul_eq_mul]
      simp [measureReal_def]
    have hbacklogIntegral :
        (∫ z : SourceInput p, (D ∩ G).indicator B z ∂sourceInputLaw p) =
          (∫ z in D, G.indicator B z ∂sourceInputLaw p) := by
      rw [integral_indicator hDG, ← setIntegral_indicator hG]
    rw [← integral_indicator hDG]
    rw [hfun,
      integral_add (hmaskedOne.const_mul C) (hmasked.const_mul (-(11 / 2 : ℝ))),
      integral_const_mul, integral_const_mul, hmassIntegral, hbacklogIntegral]
    ring
  rw [hsplit] at hstep
  exact (le_sub_iff_add_le).mp hstep

include control0 in
/-- The old-queue energy drift is localized on the same original prefix law. -/
public theorem fixedIDOldEnergyBudget (t : Fin p.T) :
    (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
      ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
        rate rewards C_star C_h t z ∂sourceInputLaw p) +
      (11 / 2 : ℝ) *
        (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
            rate rewards C_star C_h t z ∂sourceInputLaw p) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (sourceInputLaw p).real
          (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
            ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t) := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let G := ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t
  let B := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldBacklog
    rate rewards C_star C_h t.val
  let d := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld
    rate rewards C_star C_h t
  let cost := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
    rate rewards C_star C_h t
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hD : MeasurableSet[
      ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)] D :=
    ReferenceFirstCollectionPrecallFixedIDMean.measurableSet_fixedIDSourceSection_prefix
      control0 ids t.val
  have hFle : ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration
      control0 (t.val + 1) ≤ (inferInstance : MeasurableSpace (SourceInput p)) :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (t.val + 1)
  have hG : MeasurableSet G := hFle _
    (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
      rate rewards C_star C_h control0 t)
  have hregular := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
    rate rewards C_star C_h control0 t
  have hd : Integrable d (sourceInputLaw p) := by simpa [d] using hregular.2.1
  have hcost : Integrable cost (sourceInputLaw p) := by simpa [cost] using hregular.2.2.2
  have hcostEq : cost = fun z => G.indicator B z := by
    funext z
    rfl
  have hcreditEq : (fun z : SourceInput p => G.indicator
      (fun z => C - (11 / 2 : ℝ) * B z) z) =
      fun z => G.indicator (fun _ => C) z - (11 / 2 : ℝ) * cost z := by
    funext z
    by_cases hz : z ∈ G
    · simp [Set.indicator, hcostEq, hz]
    · simp [Set.indicator, hcostEq, hz]
  have hcredit : Integrable (fun z : SourceInput p => G.indicator
      (fun z => C - (11 / 2 : ℝ) * B z) z) (sourceInputLaw p) := by
    rw [hcreditEq]
    exact ((integrable_const C).indicator hG).sub (hcost.const_mul _)
  have hcond := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.conditional_weighted_drift
    rate rewards C_star C_h control0 t
  have hmono :
      (∫ z in D, (sourceInputLaw p)[d |
        ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0 (t.val + 1)]
          z ∂sourceInputLaw p) ≤
        ∫ z in D, G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z ∂sourceInputLaw p :=
    setIntegral_mono_ae integrable_condExp.integrableOn hcredit.integrableOn hcond
  rw [setIntegral_condExp hFle hd hD] at hmono
  have hDG : MeasurableSet (D ∩ G) := (hFle _ hD).inter hG
  have hmasked : Integrable (fun z : SourceInput p => (D ∩ G).indicator cost z)
      (sourceInputLaw p) := hcost.indicator hDG
  have hmaskedOne : Integrable
      (fun z : SourceInput p => (D ∩ G).indicator (fun _ => (1 : ℝ)) z)
      (sourceInputLaw p) := (integrable_const (1 : ℝ)).indicator hDG
  have hsplit :
      (∫ z in D, G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z ∂sourceInputLaw p) =
        C * (sourceInputLaw p).real (D ∩ G) -
          (11 / 2 : ℝ) * (∫ z in D, cost z ∂sourceInputLaw p) := by
    rw [setIntegral_indicator hG, ← integral_indicator hDG]
    have hfun : (fun z : SourceInput p => (D ∩ G).indicator
        (fun x => C - (11 / 2 : ℝ) * B x) z) =
        (fun z => C * (D ∩ G).indicator (fun _ => (1 : ℝ)) z +
          (-(11 / 2 : ℝ)) * (D ∩ G).indicator cost z) := by
      funext z
      by_cases hd : z ∈ D
      · by_cases hg : z ∈ G
        · have hc : cost z = B z := by
            rw [hcostEq]
            simp [G, hg]
          simp [Set.indicator, hd, hg]
          rw [hc]
          ring
        · simp [Set.indicator, cost, G, hd, hg]
      · simp [Set.indicator, cost, G, hd]
    have hmassIntegral :
        (∫ z : SourceInput p, (D ∩ G).indicator (fun _ => (1 : ℝ)) z ∂sourceInputLaw p) =
          (sourceInputLaw p).real (D ∩ G) := by
      rw [integral_indicator hDG, integral_const, smul_eq_mul]
      simp [measureReal_def]
    have hcostIntegral :
        (∫ z : SourceInput p, (D ∩ G).indicator cost z ∂sourceInputLaw p) =
          (∫ z in D, cost z ∂sourceInputLaw p) := by
      rw [integral_indicator hDG, hcostEq]
      calc
        _ = ∫ z in D ∩ G, B z ∂sourceInputLaw p := by
          apply setIntegral_congr_fun hDG
          intro z hz
          simp [Set.indicator, hz.2]
        _ = ∫ z in D, G.indicator B z ∂sourceInputLaw p :=
          (setIntegral_indicator hG).symm
    rw [hfun,
      integral_add (hmaskedOne.const_mul C) (hmasked.const_mul (-(11 / 2 : ℝ))),
      integral_const_mul, integral_const_mul, hmassIntegral, hcostIntegral]
    ring
  rw [hsplit] at hmono
  exact (le_sub_iff_add_le).mp hmono

include control0 in
/-- Empty-pending live drift retains its actual unnormalized fixed-ID mass. -/
public theorem fixedIDEmptyPendingEnergyBudget (q : Fin (ConstructorDimensions.M p))
    (t : Fin p.T) (s : ℕ) (hs : s ≤ t.val) :
    (∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 |
          z.val.val.1.1 = ids},
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
          rate rewards C_star C_h q t s hs control0 z -
        ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
          rate rewards C_star C_h q t s hs control0 z
        ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
          rate rewards C_star C_h q t s hs control0) +
      (11 / 2 : ℝ) *
        (∫ z in {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
            rate rewards C_star C_h q t s hs control0 |
              z.val.val.1.1 = ids},
          (ReferenceFirstLiveEmptyPendingAcceptedMoments.G
              rate rewards C_star C_h q t s hs control0).indicator
            (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
              rate rewards C_star C_h q t s hs control0) z
          ∂ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
            rate rewards C_star C_h q t s hs control0) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
          rate rewards C_star C_h q t s hs control0).real
          ({z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
              rate rewards C_star C_h q t s hs control0 |
                z.val.val.1.1 = ids} ∩
            ReferenceFirstLiveEmptyPendingAcceptedMoments.G
              rate rewards C_star C_h q t s hs control0) := by
  let D : Set (ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) :=
    {z | z.val.val.1.1 = ids}
  let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G
    rate rewards C_star C_h q t s hs control0
  let μ := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty
    rate rewards C_star C_h q t s hs control0
  let B := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  let d := fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 =>
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter
        rate rewards C_star C_h q t s hs control0 z -
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore
        rate rewards C_star C_h q t s hs control0 z
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hD : MeasurableSet[ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0] D := by
    exact ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_empty
      rate rewards C_star C_h q t s hs control0 {ids} (measurableSet_singleton ids)
  have hFle : ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
      rate rewards C_star C_h q t s hs control0 ≤ (inferInstance : MeasurableSpace
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0)) :=
    ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty_le
      rate rewards C_star C_h q t s hs control0
  have hDamb : MeasurableSet D := hFle _ hD
  have hG : MeasurableSet[(inferInstance : MeasurableSpace
      (ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0))] G := by
    exact ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
      rate rewards C_star C_h q t s hs control0
  have hB : Integrable B μ :=
    ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_weightedBacklogBefore
      rate rewards C_star C_h q t s hs control0
  have hd : Integrable d μ := by
    simpa [d] using
      ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_potentialDifference
        rate rewards C_star C_h q t s hs control0
  have hcredit : Integrable (fun z => G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z) μ := by
    have hbase : Integrable (fun z => C - (11 / 2 : ℝ) * B z) μ :=
      (integrable_const C).sub (hB.const_mul (11 / 2 : ℝ))
    exact hbase.indicator hG
  have hcond :=
    ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.potential_drift_conditional_rate_sum
      rate rewards C_star C_h q t s hs control0
  have hrate (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0) :
      ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.markerRateWeightSum
          rate rewards C_star C_h q t s hs control0 z ≤ CanonicalRecordingRates.R p :=
    ReferenceFirstLiveEmptyPendingAnchorRateFeasibility.sum_thetaBefore_div_xiEmpty_le_R
      rate rewards C_star C_h q t s hs control0 z
  have hcreditPoint :
      (fun z => G.indicator (fun z =>
        -(11 / 2 : ℝ) * B z +
          ReferenceFirstLiveEmptyPendingConditionalWeightedDrift.markerRateWeightSum
            rate rewards C_star C_h q t s hs control0 z +
          (33 / 2 : ℝ) * (p.m : ℝ)) z) ≤ᵐ[μ]
      (fun z => G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z) := by
    apply ae_of_all μ
    intro z
    by_cases hz : z ∈ G
    · simp only [Set.indicator_of_mem hz]
      dsimp [C]
      linarith [hrate z]
    · simp [Set.indicator_of_notMem hz]
  have hdrift :
      μ[d | ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
        rate rewards C_star C_h q t s hs control0] ≤ᵐ[μ]
        (fun z => G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z) := by
    simpa [d, G, B] using hcond.trans hcreditPoint
  have hmono :
      (∫ z in D, μ[d |
        ReferenceFirstLiveEmptyPendingMarkerLaw.Fempty
          rate rewards C_star C_h q t s hs control0] z ∂μ) ≤
        ∫ z in D, G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z ∂μ :=
    setIntegral_mono_ae integrable_condExp.integrableOn hcredit.integrableOn
      hdrift
  rw [setIntegral_condExp hFle hd hD] at hmono
  have hDG : MeasurableSet (D ∩ G) := hDamb.inter hG
  have hmaskedB : Integrable (fun z => (D ∩ G).indicator B z) μ := hB.indicator hDG
  have hmasked1 : Integrable
      (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 =>
          (D ∩ G).indicator (fun _ => (1 : ℝ)) z) μ :=
    (integrable_const (1 : ℝ)).indicator hDG
  have hsplit :
      (∫ z in D, G.indicator (fun z => C - (11 / 2 : ℝ) * B z) z ∂μ) =
        C * μ.real (D ∩ G) - (11 / 2 : ℝ) *
          (∫ z in D, G.indicator B z ∂μ) := by
    rw [setIntegral_indicator hG, ← integral_indicator hDG]
    have hfun : (fun z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0 =>
          (D ∩ G).indicator (fun x => C - (11 / 2 : ℝ) * B x) z) =
        fun z => C * (D ∩ G).indicator (fun _ => (1 : ℝ)) z +
          (-(11 / 2 : ℝ)) * (D ∩ G).indicator B z := by
      funext z
      by_cases hz : z ∈ D ∩ G
      · simp [Set.indicator, hz]
        ring
      · simp [Set.indicator, hz]
    have hmass :
        (∫ z, (D ∩ G).indicator (fun _ => (1 : ℝ)) z ∂μ) = μ.real (D ∩ G) := by
      rw [integral_indicator hDG, integral_const, smul_eq_mul]
      simp [measureReal_def]
    have hbacklog :
        (∫ z, (D ∩ G).indicator B z ∂μ) = ∫ z in D, G.indicator B z ∂μ := by
      rw [integral_indicator hDG, ← setIntegral_indicator hG]
    rw [hfun, integral_add (hmasked1.const_mul C)
        (hmaskedB.const_mul (-(11 / 2 : ℝ))),
      integral_const_mul, integral_const_mul, hmass, hbacklog]
    ring
  rw [hsplit] at hmono
  exact (le_sub_iff_add_le).mp hmono

include control0 in
/-- Continuing live drift retains its actual unnormalized fixed-ID mass. -/
public theorem fixedIDContinuingEnergyBudget
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) (s : ℕ)
    (hs : s ≤ t.val) :
    (∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0 |
          z.val.val.1.1 = ids},
      ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
          rate rewards C_star C_h q t s hs control0 z -
        ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
          rate rewards C_star C_h q t s hs control0 z
        ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate rewards C_star C_h q t s hs control0) +
      (11 / 2 : ℝ) *
        (∫ z in {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
            rate rewards C_star C_h q t s hs control0 |
              z.val.val.1.1 = ids},
          (ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
              rate rewards C_star C_h q t s hs control0).indicator
            (ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
              rate rewards C_star C_h q t s hs control0) z
          ∂ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
            rate rewards C_star C_h q t s hs control0) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
          rate rewards C_star C_h q t s hs control0).real
          ({z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
              rate rewards C_star C_h q t s hs control0 |
                z.val.val.1.1 = ids} ∩
            ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
              rate rewards C_star C_h q t s hs control0) := by
  let D : Set (ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0) := {z | z.val.val.1.1 = ids}
  let G := ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
    rate rewards C_star C_h q t s hs control0
  let μ := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
    rate rewards C_star C_h q t s hs control0
  let before := ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore
    rate rewards C_star C_h q t s hs control0
  let after := ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter
    rate rewards C_star C_h q t s hs control0
  let B := ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore
    rate rewards C_star C_h q t s hs control0
  let C := CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
  have hD : MeasurableSet[
      ReferenceFirstLiveAllArmPrefixAdaptation.sourcePlusPrefixField
        rate rewards C_star C_h q t s hs control0] D :=
    ReferenceFirstLiveRetainedIDExponentialStep.measurableSet_originalIDSet_nonempty
      rate rewards C_star C_h q t s hs control0 {ids} (measurableSet_singleton ids)
  have hbefore : Integrable before μ := by
    simpa [before, μ] using
      ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialBefore
        rate rewards C_star C_h q t s hs control0
  have hafter : Integrable after μ := by
    simpa [after, μ] using
      ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialAfter
        rate rewards C_star C_h q t s hs control0
  have hbudget := ReferenceFirstLiveRateBoundedDrift.weightedBacklog_budget_on
    rate rewards C_star C_h q t s hs control0 D hD
  have hbudget' :
      (11 / 2 : ℝ) *
          (∫ z in D, G.indicator B z ∂μ) ≤
        C * μ.real (D ∩ G) +
          (∫ z in D, before z ∂μ) - (∫ z in D, after z ∂μ) := by
    change (11 / 2 : ℝ) *
          (∫ z in D, G.indicator B z ∂μ) ≤
        C * μ.real (D ∩ G) +
          (∫ z in D, before z ∂μ) - (∫ z in D, after z ∂μ) at hbudget
    exact hbudget
  have hresult :
      (∫ z in D, after z - before z ∂μ) +
          (11 / 2 : ℝ) * (∫ z in D, G.indicator B z ∂μ) ≤
        C * μ.real (D ∩ G) := by
    rw [integral_sub hafter.integrableOn hbefore.integrableOn]
    linarith [hbudget']
  simpa [D, G, μ, before, after, B, C] using hresult

include control0 in
/-- The literal first launch update has a quadratic energy budget on each
fixed-ID source section, using the original birth stratum measure. -/
public theorem fixedIDBirthEnergyBudget
    (q : Fin (ConstructorDimensions.M p)) (t : Fin p.T) :
    (∫ z in {z : ReferenceTotalSourceDisintegration.SourceStratum
        rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) |
          z.val.1.1 = ids},
      ReferenceFirstLaunchEnergyInitialization.birthPotential
        rate rewards C_star C_h q t control0 z
      ∂ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
          (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)).real
          {z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
            (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) |
              z.val.1.1 = ids} := by
  let Zbirth := ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  let muBirth := ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
    (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)
  let X := ReferenceFirstLaunchRecordingPhysicalMarker.RetainedStart
    rate rewards C_star C_h q t control0
  let coords := ReferenceFirstLaunchRecordingSourceLaw.sourceCoordinates
    rate rewards C_star C_h q t control0
  let muC := ReferenceRetainedSourceCoupling.retainedRemainderMeasure
    rate rewards C_star C_h q t t.val le_rfl control0
  let Aset : Set X := {x | x.val.1.1 = ids}
  let Dset : Set Zbirth := {z | z.val.1.1 = ids}
  let Y := ReferenceFirstLaunchCommonUpdateSource.firstConservedReadout
    rate rewards C_star C_h q t control0
  let theta0 : Fin p.K → ℝ := fun j => ProductSetLaw.theta p.m (fun _ => 1) j
  let A : Zbirth → ℝ := fun z => ∑ j : Fin p.K, theta0 j * (Y z j) ^ 2
  let factor : ℝ := 1 + 8 * rate.eta.val
  have hAset : MeasurableSet Aset := by
    exact (measurableSet_singleton ids).preimage
      ((measurable_fst.comp measurable_fst).comp measurable_subtype_coe)
  have hIDmass : muBirth Dset = muC Aset := by
    have hm := congrArg (fun ν => ν (Aset ×ˢ Set.univ))
      (ReferenceFirstLaunchRecordingSourceLaw.map_sourceCoordinates
        rate rewards C_star C_h q t control0)
    rw [Measure.map_apply
        (ReferenceFirstLaunchRecordingSourceLaw.measurable_sourceCoordinates
          rate rewards C_star C_h q t control0)
        (hAset.prod MeasurableSet.univ), Measure.prod_prod] at hm
    have hcoords : coords ⁻¹' (Aset ×ˢ Set.univ) = Dset := by
      ext z
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true, Aset, Dset]
      change (coords z).1.val.1.1 = ids ↔ z.val.1.1 = ids
      rw [ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
        rate rewards C_star C_h q t control0 z]
    rw [hcoords] at hm
    simpa only [measure_univ, mul_one] using hm
  have hIDmassReal : muC.real Aset = muBirth.real Dset := by
    exact congrArg ENNReal.toReal hIDmass.symm
  have hfactor : 0 ≤ factor := by
    dsimp [factor]
    positivity [rate.eta.property]
  have hmassNonneg : 0 ≤ muBirth.real Dset := MeasureTheory.measureReal_nonneg
  have hsmall : rate.eta.val ≤ 1 / 64 := by
    have hcap : (ReferenceFirstLaunchNumericalCell.queueParameters rate).eta ≤
        1 / (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by
      simpa only [ReferenceFirstLaunchNumericalCell.queueParameters] using rate.sourceCap
    exact RecordedWeightedDrift.eta_le_one_div_sixtyFour p
      (ReferenceFirstLaunchNumericalCell.queueParameters rate) hcap
  have hpoint (z : Zbirth) :
      ReferenceFirstLaunchEnergyInitialization.birthPotential
          rate rewards C_star C_h q t control0 z ≤ factor * A z := by
    let Q := ReferenceFirstLaunchNumericalCell.queueParameters rate
    let U := ReferenceFirstLaunchCommonUpdateSource.firstUpdate
      rate rewards C_star C_h q t control0 z
    have hgrowth (j : Fin p.K) := RecordedMarginalGrowth.step_theta_growth
      Q (RecordedQueueRun.initialState p.K)
      (ReferenceFirstLaunchCommonUpdateSource.firstCell
        rate rewards C_star C_h q t control0 z) j p.two_le_m p.m_lt_K hsmall
    have hweight0 : RecordedQueueRun.scoreWeight Q
        (RecordedQueueRun.initialState p.K) = fun _ => 1 := by
      funext j
      simp [RecordedQueueRun.scoreWeight, RecordedQueueRun.initialState,
        ScoreWeights.scoreWeight]
    have hden : 0 < rate.eta.val * (ConstructorDimensions.D p : ℝ) :=
      mul_pos rate.eta.property (Nat.cast_pos.mpr (ConstructorDimensions.D_pos p))
    have hback (j : Fin p.K) :
        StoppedQueueBound.normalizedBacklog Q U j =
          ((U.registers j).2 : ℝ) /
            (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := by
      change ((U.registers j).2 : ℝ) / (rate.n : ℝ) = _
      rw [rate.n_scale]
    have hreadout (j : Fin p.K) :
        Y z j = (((U.registers j).1 + (U.registers j).2 : ℕ) : ℝ) /
          (rate.eta.val * (ConstructorDimensions.D p : ℝ)) := rfl
    have hstate := ReferenceFirstLaunchCommonUpdateSource.source_first_update
      rate rewards C_star C_h q t control0 z
    have hbackBound (j : Fin p.K) :
        0 ≤ StoppedQueueBound.normalizedBacklog Q U j ∧
          StoppedQueueBound.normalizedBacklog Q U j ≤ Y z j := by
      rw [hback j, hreadout j]
      constructor
      · exact div_nonneg (Nat.cast_nonneg _) hden.le
      · apply div_le_div_of_nonneg_right _ hden.le
        have hreg := (hstate.1 j).2.1
        have hnat : (U.registers j).2 ≤ (U.registers j).1 + (U.registers j).2 := by
          rw [hreg]
          omega
        exact_mod_cast hnat
    have hsum :
        ReferenceFirstLaunchEnergyInitialization.birthPotential
            rate rewards C_star C_h q t control0 z =
          ∑ j : Fin p.K,
            ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q U) j *
              (StoppedQueueBound.normalizedBacklog Q U j) ^ 2 := rfl
    have htheta (j : Fin p.K) :
        ProductSetLaw.theta p.m (RecordedQueueRun.scoreWeight Q U) j ≤
          factor * theta0 j := by
      have h := (hgrowth j).1.trans (hgrowth j).2
      rw [hweight0] at h
      exact h
    rw [hsum]
    calc
      _ ≤ ∑ j : Fin p.K, factor * theta0 j * (Y z j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have htheta0 : 0 ≤ theta0 j := by
          dsimp [theta0]
          exact (ProductSetLaw.theta_pos (fun _ => 1) j
            (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K (by intro i; norm_num)).le
        have hsq := (sq_le_sq₀ (hbackBound j).1 (by
          have : 0 ≤ Y z j := by
            rw [hreadout j]
            positivity
          exact this)).2 (hbackBound j).2
        calc
          _ ≤ (factor * theta0 j) *
              (StoppedQueueBound.normalizedBacklog Q U j) ^ 2 :=
            mul_le_mul_of_nonneg_right (htheta j) (sq_nonneg _)
          _ ≤ (factor * theta0 j) * (Y z j) ^ 2 :=
            mul_le_mul_of_nonneg_left hsq (mul_nonneg hfactor htheta0)
          _ = factor * theta0 j * (Y z j) ^ 2 := by ring
      _ = factor * A z := by
        dsimp [A, factor]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hpotential : Integrable
      (ReferenceFirstLaunchEnergyInitialization.birthPotential
        rate rewards C_star C_h q t control0) muBirth :=
    ReferenceFirstLaunchEnergyInitialization.integrable_birthPotential
      rate rewards C_star C_h q t control0
  have hAint : Integrable A muBirth := by
    dsimp [A]
    apply integrable_finsetSum
    intro j hj
    have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Set.univ Set.univ
      MeasurableSet.univ MeasurableSet.univ
    exact hmom.2.2.2.1.const_mul (theta0 j)
  have hfactorA : Integrable (fun z => factor * A z) muBirth := hAint.const_mul factor
  have hRsum := CanonicalRecordingRates.sum_theta_div_xi_le_R p rate.eta.property
    (fun _ => 1) (fun _ => 1) (by intro j; norm_num)
    (by intro j; exact ⟨le_rfl, by norm_num⟩)
  have hsecond (j : Fin p.K) :
      (∫ z in Dset, (Y z j) ^ 2 ∂muBirth) =
        muBirth.real Dset *
          (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
            (QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
              rate.eta.val (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
              (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ))) ^ 2) := by
    let xi := CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j
    let rho := (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ))
    let value := QuantizedRecordingMoments.quantizedValue
      (ConstructorDimensions.D p) rate.eta.val xi rho
    have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
      rate rewards C_star C_h q t control0 j Aset Set.univ hAset MeasurableSet.univ
    have hrect : {z : Zbirth | (coords z).1 ∈ Aset ∧ (coords z).2.1 ∈ Set.univ} = Dset := by
      ext z
      simp only [Aset, Dset, Set.mem_univ, and_true]
      change (coords z).1.val.1.1 = ids ↔ z.val.1.1 = ids
      rw [ReferenceFirstLiveRetainedIDExponentialStep.sourceCoordinates_originalID
        rate rewards C_star C_h q t control0 z]
    have hraw := hmom.2.2.2.2.2
    rw [hrect] at hraw
    have hassign :
        (ContinuousControlSlice.assignmentLaw p.K Set.univ).toReal = 1 := by simp
    have hIDmassToReal : (muC Aset).toReal = (muBirth Dset).toReal :=
      congrArg ENNReal.toReal hIDmass.symm
    rw [hassign, hIDmassToReal] at hraw
    simpa only [muBirth, Y, xi, rho, value, one_mul, mul_assoc, measureReal_def] using hraw
  have hsquareBudget :
      (∫ z in Dset, A z ∂muBirth) ≤ muBirth.real Dset * CanonicalRecordingRates.R p := by
    calc
      _ = ∑ j : Fin p.K, theta0 j *
          (∫ z in Dset, (Y z j) ^ 2 ∂muBirth) := by
        dsimp [A]
        rw [integral_finsetSum Finset.univ (fun j hj =>
          (ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
            rate rewards C_star C_h q t control0 j Aset Set.univ hAset
            MeasurableSet.univ).2.2.2.1.integrableOn.const_mul (theta0 j))]
        simp_rw [integral_const_mul, Y, muBirth]
      _ ≤ ∑ j : Fin p.K, muBirth.real Dset *
          (theta0 j / CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hmom := ReferenceFirstLaunchCommonUpdateSource.first_update_all_arm_source_moments
          rate rewards C_star C_h q t control0 j Aset Set.univ hAset MeasurableSet.univ
        have hcoef := ReferenceFirstLaunchCommonUpdateSource.first_update_moment_coefficients_bounds
          rate rewards t j
        have hcoef' :
            CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
              (QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
                rate.eta.val (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
                (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ))) ^ 2 ≤
              1 / CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j := by
          exact hcoef.2.2.1.trans hcoef.2.2.2
        have htheta0 : 0 ≤ theta0 j := by
          exact (ProductSetLaw.theta_pos (fun _ => 1) j
            (Nat.zero_lt_of_lt p.two_le_m) p.m_lt_K (by intro i; norm_num)).le
        rw [hsecond j]
        calc
          _ = muBirth.real Dset * (theta0 j *
                (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j *
                  (QuantizedRecordingMoments.quantizedValue (ConstructorDimensions.D p)
                    rate.eta.val (CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)
                    (((rewards t j).val : ℝ) / (ConstructorDimensions.D p : ℝ))) ^ 2)) := by ring
          _ ≤ muBirth.real Dset * (theta0 j *
                (1 / CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hcoef' htheta0) hmassNonneg
          _ = muBirth.real Dset *
                (theta0 j / CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j) := by
            rw [div_eq_mul_inv]
            ring
      _ = muBirth.real Dset *
          ∑ j : Fin p.K,
            theta0 j / CanonicalRecordingRates.xi p rate.eta.val (fun _ => 1) j := by
        rw [← Finset.mul_sum]
      _ ≤ muBirth.real Dset * CanonicalRecordingRates.R p :=
        mul_le_mul_of_nonneg_left hRsum hmassNonneg
  have hRnonneg : 0 ≤ CanonicalRecordingRates.R p := by
    unfold CanonicalRecordingRates.R
    have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
    have hsub : 0 ≤ 2 * (p.K : ℝ) - (p.m : ℝ) := by linarith
    positivity
  have hEtaR : 8 * rate.eta.val * CanonicalRecordingRates.R p ≤ (p.m : ℝ) := by
    have hm : 0 < (p.m : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.m_pos p)
    have hK : 0 < (p.K : ℝ) := Nat.cast_pos.mpr (ConstructorDimensions.K_pos p)
    have hL : (1 : ℝ) ≤ (CanonicalRecordingRates.L_stab p : ℝ) := by
      exact_mod_cast CanonicalRecordingRates.L_stab_ge_one p
    have hden : 0 < 1024 * (p.m : ℝ) * (p.K : ℝ) *
        (CanonicalRecordingRates.L_stab p : ℝ) := by positivity
    have hEtaDen : rate.eta.val *
        (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) ≤ 1 :=
      (le_div_iff₀ hden).mp rate.sourceCap
    have hKfactor : 2 * (p.K : ℝ) - (p.m : ℝ) ≤
        2 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) := by
      have hmK : (p.m : ℝ) ≤ (p.K : ℝ) := by exact_mod_cast p.m_lt_K.le
      calc
        2 * (p.K : ℝ) - (p.m : ℝ) ≤ 2 * (p.K : ℝ) := by linarith
        _ = 2 * (p.K : ℝ) * 1 := by ring
        _ ≤ 2 * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
    have hcoef : 512 * (p.m : ℝ) ^ 2 * (2 * (p.K : ℝ) - (p.m : ℝ)) ≤
        (p.m : ℝ) * (1024 * (p.m : ℝ) * (p.K : ℝ) *
          (CanonicalRecordingRates.L_stab p : ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hKfactor (by positivity : 0 ≤ 512 * (p.m : ℝ)^2)
      nlinarith only [h]
    calc
      8 * rate.eta.val * CanonicalRecordingRates.R p =
          rate.eta.val * (512 * (p.m : ℝ)^2 * (2 * (p.K : ℝ) - (p.m : ℝ))):= by
        simp [CanonicalRecordingRates.R]
        ring
      _ ≤ rate.eta.val * ((p.m : ℝ) *
          (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ))) :=
        mul_le_mul_of_nonneg_left hcoef rate.eta.property.le
      _ = (p.m : ℝ) * (rate.eta.val *
          (1024 * (p.m : ℝ) * (p.K : ℝ) * (CanonicalRecordingRates.L_stab p : ℝ))) := by ring
      _ ≤ (p.m : ℝ) := by nlinarith only [hEtaDen, hm]
  have hbudget : factor * CanonicalRecordingRates.R p ≤
      CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
    have hmnonneg : 0 ≤ (p.m : ℝ) := Nat.cast_nonneg p.m
    calc
      factor * CanonicalRecordingRates.R p =
          CanonicalRecordingRates.R p + 8 * rate.eta.val * CanonicalRecordingRates.R p := by
        dsimp [factor]
        ring
      _ ≤ CanonicalRecordingRates.R p + (p.m : ℝ) := add_le_add_right hEtaR _
      _ ≤ CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ) := by
        apply add_le_add_right
        nlinarith only [hmnonneg]
  have hfinal :
      (∫ z in Dset,
        ReferenceFirstLaunchEnergyInitialization.birthPotential
          rate rewards C_star C_h q t control0 z ∂muBirth) ≤
        ∫ z in Dset, factor * A z ∂muBirth := by
    apply integral_mono (μ := muBirth.restrict Dset)
    · exact hpotential.integrableOn
    · exact hfactorA.integrableOn
    · exact hpoint
  calc
    _ ≤ ∫ z in Dset, factor * A z ∂muBirth := hfinal
    _ = factor * (∫ z in Dset, A z ∂muBirth) := by
      exact integral_const_mul factor A
    _ ≤ factor * (muBirth.real Dset * CanonicalRecordingRates.R p) :=
      mul_le_mul_of_nonneg_left hsquareBudget hfactor
    _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        muBirth.real Dset := by
      calc
        factor * (muBirth.real Dset * CanonicalRecordingRates.R p) =
            (factor * CanonicalRecordingRates.R p) * muBirth.real Dset := by ring
        _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            muBirth.real Dset := mul_le_mul_of_nonneg_right hbudget hmassNonneg

section Assembly

variable (t : Fin p.T)
local notation "S" => SourceInput p
local notation "mu" => sourceInputLaw p
local notation "V" => ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt
  rate rewards C_star C_h
local notation "LIVE" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
  rate rewards C_star C_h
local notation "c" => CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)

local notation "phase" => ReferenceFirstLiveSourcePhasePartition.sourcePhase
  rate rewards C_star C_h t
local notation "birthM" => fun (q : Fin (ConstructorDimensions.M p)) =>
  Measure.map
    (Subtype.val : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t) → S)
    (ReferenceTotalSourceDisintegration.sourceStratumMeasure rate rewards C_star C_h t
      (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t))
local notation "plusM" => fun (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) =>
  Measure.map
    (ReferenceFirstLiveBranchIntegralTransport.forgetBranch rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)
    (ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)
local notation "emptyM" => fun (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)) =>
  Measure.map
    (ReferenceFirstLiveSourcePhasePartition.forgetEmpty rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)
    (ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t
      (Fin.val v) (Nat.lt_succ_iff.mp (Fin.isLt v)) control0)

private theorem integral_source_cells {f : S → ℝ} (hf : Integrable f mu) :
    (∫ z, f z ∂mu) =
      (∫ z in phase 0, f z ∂mu) + (∫ z in phase 1, f z ∂mu) +
      (∫ z in phase 5, f z ∂mu) +
      (∑ q : Fin (ConstructorDimensions.M p), ∫ z, f z ∂birthM q) +
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ z, f z ∂plusM q v) + (∫ z, f z ∂emptyM q v)) := by
  have hd := ReferenceFirstLiveCalendarIntegralAssembly.original_source_measure_decomposition
    rate rewards C_star C_h t control0
  have hi := hf
  rw [hd] at hi
  have hiO := hi.left_of_add_measure.left_of_add_measure
  have hiB := hi.left_of_add_measure.right_of_add_measure
  have hiC := hi.right_of_add_measure
  have hB := integral_finsetSum_measure (integrable_finsetSum_measure.mp hiB)
  have hC : (∫ z, f z ∂(∑ q : Fin (ConstructorDimensions.M p),
      ∑ v : Fin (t.val + 1), (plusM q v + emptyM q v))) =
      ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
        ((∫ z, f z ∂plusM q v) + (∫ z, f z ∂emptyM q v)) := by
    rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hiC)]
    apply Finset.sum_congr rfl
    intro q hq
    have hqInt := integrable_finsetSum_measure.mp hiC q hq
    rw [integral_finsetSum_measure (integrable_finsetSum_measure.mp hqInt)]
    apply Finset.sum_congr rfl
    intro v hv
    have hvInt := integrable_finsetSum_measure.mp hqInt v hv
    exact integral_add_measure hvInt.left_of_add_measure hvInt.right_of_add_measure
  calc
    _ = ∫ z, f z ∂((mu).restrict (phase 0) + (mu).restrict (phase 1) +
        (mu).restrict (phase 5) + (∑ q : Fin (ConstructorDimensions.M p), birthM q) +
        ∑ q : Fin (ConstructorDimensions.M p), ∑ v : Fin (t.val + 1),
          (plusM q v + emptyM q v)) := by rw [← hd]
    _ = _ := by
      rw [integral_add_measure hi.left_of_add_measure hi.right_of_add_measure,
        integral_add_measure hiO hiB,
        integral_add_measure hiO.left_of_add_measure hiO.right_of_add_measure,
        integral_add_measure hiO.left_of_add_measure.left_of_add_measure
          hiO.left_of_add_measure.right_of_add_measure, hB, hC]

private theorem calendar_increment_zero_on_exception (z : S)
    (hz : z ∈ phase 0 ∨ z ∈ phase 1 ∨ z ∈ phase 5) :
    V (t.val + 1) z - V t.val z = 0 := by
  have hprefix : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z).take
        (t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) =
      (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
        rate rewards C_star C_h z).take
        (t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h) := by
    rcases hz with h0 | h1 | h5
    · change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing = none at h0
      rw [(ReferenceFirstLiveOverflowReadout.wholeFirstLive_no_launch
        rate rewards C_star C_h z h0).2.1]
      simp only [List.take_nil]
    · change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing.isSome = true ∧
        t.val < ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at h1
      have hbefore : t.val - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h = 0 := by omega
      have hafter : t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart
          rate z rewards C_star C_h = 0 := by omega
      rw [hbefore, hafter]
    · change (ReferenceCompletePhysicalHistory.generatedBoundary
        rate z rewards C_star C_h).crossing.isSome = true ∧
        ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h < t.val ∧
        (ReferenceFirstLiveOverflowReadout.wholeFirstLiveWindow
          rate rewards C_star C_h z).length ≤
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h at h5
      have hlen := ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h z
      have hb : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h z).length ≤
          t.val - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        rw [hlen]
        exact h5.2.2
      have ha : (ReferenceFirstLiveOverflowReadout.wholeFirstLiveCells
          rate rewards C_star C_h z).length ≤
          t.val + 1 - ReferenceCompletePhysicalHistory.physicalStart rate z rewards C_star C_h := by
        omega
      rw [List.take_of_length_le ha, List.take_of_length_le hb]
  simp only [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt, hprefix, sub_self]

include control0 in
private theorem retained_cost_on_continuing (z : S)
    (hz : z ∈ phase 3 ∨ z ∈ phase 4) :
    LIVE t z =
      (if (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
          rate rewards C_star C_h t.val z).overflow = false then
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt
          rate rewards C_star C_h t.val z else 0) := by
  unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
  rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
    rate rewards C_star C_h t control0]
  have hphase : z ∈ phase 2 ∪ (phase 3 ∪ phase 4) := Or.inr hz
  simp only [Set.indicator, Set.mem_inter_iff, hphase, true_and]
  rfl

include control0 in
/-- The LIVE energy increment is integrated after localization on the literal
ID cylinder. Every original birth, continuing, and empty cell keeps its mass. -/
public theorem fixedIDLiveEnergyBudget :
    (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
      V (t.val + 1) z - V t.val z ∂mu) +
      (11 / 2 : ℝ) * (∫ z in ReferenceFixedIDSourceSection.fixedIDSourceSection ids,
        LIVE t z ∂mu) ≤
      c * (mu).real (ReferenceFixedIDSourceSection.fixedIDSourceSection ids ∩
        (phase 2 ∪ phase 3 ∪ phase 4)) := by
  let D := ReferenceFixedIDSourceSection.fixedIDSourceSection ids
  let E := phase 2 ∪ phase 3 ∪ phase 4
  let delta : S → ℝ := fun z => V (t.val + 1) z - V t.val z + (11 / 2 : ℝ) * LIVE t z
  let f : S → ℝ := D.indicator delta
  let g : S → ℝ := (D ∩ E).indicator (fun _ => c)
  have hD : MeasurableSet D := ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection ids
  have hE : MeasurableSet E :=
    ReferenceFirstCollectionPrecallLiveOldMass.measurableSet_sourcePhase234
      rate rewards C_star C_h t control0
  have hC : 0 ≤ c :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.sourceDriftConstant_nonneg
  have hV (n : ℕ) := ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
    rate rewards C_star C_h n
  have hL := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
    rate rewards C_star C_h t control0
  have hdelta : Integrable delta mu := ((hV _).sub (hV _)).add (hL.const_mul _)
  have hf : Integrable f mu := hdelta.indicator hD
  have hg : Integrable g mu := (integrable_const c).indicator (hD.inter hE)
  have hcell : ∀ {Z : Type} [MeasurableSpace Z] (ν : Measure Z) (ι : Z → S),
      Measurable ι → ν.map ι ≤ mu → (∀ z, ι z ∈ E) →
      (∫ z in ι ⁻¹' D, delta (ι z) ∂ν) ≤ c * ν.real (ι ⁻¹' D) →
      (∫ z, f z ∂ν.map ι) ≤ ∫ z, g z ∂ν.map ι := by
    intro Z _ ν ι hι hdom hactive hstep
    rw [integral_map hι.aemeasurable (hf.mono_measure hdom).aestronglyMeasurable,
      integral_map hι.aemeasurable (hg.mono_measure hdom).aestronglyMeasurable]
    have hleft : (fun z => f (ι z)) = (ι ⁻¹' D).indicator (fun z => delta (ι z)) := by
      funext z
      by_cases hz : ι z ∈ D <;> simp [f, Set.indicator, hz]
    have hright : (fun z => g (ι z)) = (ι ⁻¹' D).indicator (fun _ => c) := by
      funext z
      have he := hactive z
      by_cases hz : ι z ∈ D <;> simp [g, Set.indicator, hz, he]
    rw [hleft, hright, integral_indicator (hD.preimage hι),
      integral_indicator (hD.preimage hι), integral_const]
    simpa only [smul_eq_mul, measureReal_restrict_apply_univ, mul_comm] using hstep
  have hbirth : ∀ q : Fin (ConstructorDimensions.M p),
      (∫ z, f z ∂birthM q) ≤ ∫ z, g z ∂birthM q := by
    intro q
    have hactive (z : ReferenceTotalSourceDisintegration.SourceStratum rate rewards C_star C_h t
        (ReferenceFirstLaunchRecordingSourceLaw.firstStratumIndex q t)) : z.val ∈ phase 2 := by
      rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_birth_iUnion rate rewards C_star C_h t]
      exact Set.mem_iUnion.mpr ⟨q, z.property⟩
    apply hcell _ Subtype.val measurable_subtype_coe
    · rw [ReferenceTotalSourceDisintegration.sourceStratumMeasure_map rate rewards C_star C_h t control0]
      exact Measure.restrict_le_self
    · exact fun z => Or.inl (Or.inl (hactive z))
    · convert fixedIDBirthEnergyBudget rate rewards C_star C_h control0 ids q t using 1
      apply setIntegral_congr_fun (hD.preimage measurable_subtype_coe)
      intro z _
      dsimp only [delta]
      rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_birth_before
          rate rewards C_star C_h q t z,
        ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_birth_after
          rate rewards C_star C_h q t control0 z,
        ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost_eq_zero_on_birth
          rate rewards C_star C_h t z.val (hactive z)]
      simp only [sub_zero, mul_zero, add_zero]
      rfl
      rfl
  have hplus : ∀ (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)),
      (∫ z, f z ∂plusM q v) ≤ ∫ z, g z ∂plusM q v := by
    intro q v
    let s := v.val
    have hs : s ≤ t.val := Nat.lt_succ_iff.mp v.isLt
    let ν := ReferenceFirstLiveRecordingSourceCylinder.branchSourceMeasure
      rate rewards C_star C_h q t s hs control0
    let G := ReferenceFirstLiveAllArmPrefixAdaptation.strictPastOverflowFalseSet
      rate rewards C_star C_h q t s hs control0
    let A := {z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
      rate rewards C_star C_h q t s hs control0 | z.val.val.1.1 = ids}
    have hactive (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
        rate rewards C_star C_h q t s hs control0) : z.val.val ∈ phase 3 := by
      rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_nonempty_iUnion
        rate rewards C_star C_h t control0]
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, ⟨z.val, z.property, rfl⟩⟩⟩
    apply hcell _ (ReferenceFirstLiveBranchIntegralTransport.forgetBranch
      rate rewards C_star C_h q t s hs control0) (measurable_subtype_coe.comp measurable_subtype_coe)
    · rw [ReferenceFirstLiveBranchIntegralTransport.branchSourceMeasure_map_original]
      exact Measure.restrict_le_self
    · exact fun z => Or.inl (Or.inr (hactive z))
    · have hb := fixedIDContinuingEnergyBudget rate rewards C_star C_h control0 ids q t s hs
      have hm : c * ν.real (A ∩ G) ≤ c * ν.real A :=
        mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_left) hC
      refine le_trans ?_ (hb.trans hm)
      have hbefore := ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialBefore
        rate rewards C_star C_h q t s hs control0
      have hafter := ReferenceFirstLiveQueueEnergyEnvelope.integrable_potentialAfter
        rate rewards C_star C_h q t s hs control0
      have hcost := ReferenceFirstLiveQueueEnergyEnvelope.integrable_weightedBacklogBefore
        rate rewards C_star C_h q t s hs control0
      have hGambient := ReferenceFirstLiveAllArmPrefixAdaptation.measurableSet_strictPastOverflowFalseSet_ambient
        rate rewards C_star C_h q t s hs control0
      have heq (z : ReferenceFirstLiveRecordingSourceCylinder.SourcePlus
          rate rewards C_star C_h q t s hs control0) :
          delta z.val.val =
            (ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter rate rewards C_star C_h q t s hs control0 z -
              ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore rate rewards C_star C_h q t s hs control0 z) +
            (11 / 2 : ℝ) * G.indicator
              (ReferenceFirstLiveQueueEnergyEnvelope.weightedBacklogBefore rate rewards C_star C_h q t s hs control0) z := by
        dsimp only [delta]
        rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_after rate rewards C_star C_h q t s hs control0 z,
          ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt_before rate rewards C_star C_h q t s hs control0 z,
          retained_cost_on_continuing rate rewards C_star C_h control0 t z.val.val (Or.inl (hactive z))]
        have hsafe := ReferenceFirstLiveOriginalBranchEstimates.strictPastOverflowFalse_iff_wholeSource
          rate rewards C_star C_h q t s hs control0 z
        have hsafe' : G z ↔ (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveRunAt
            rate rewards C_star C_h t.val z.val.val).overflow = false := hsafe
        by_cases hz : z ∈ G
        · simp only [ite_eq_left (hsafe'.mp hz), Set.indicator_of_mem hz]
          rw [ReferenceFirstLiveCalendarPrefixReadout.firstWindowWeightedBacklogAt_before
            rate rewards C_star C_h q t s hs control0 z]
        · simp only [ite_eq_right (fun h => hz (hsafe'.mpr h)), Set.indicator_of_notMem hz]
      change (∫ z in A, delta z.val.val ∂ν) ≤ _
      simp_rw [heq]
      dsimp only [A, G, ν]
      rw [integral_add (f := fun z =>
          ReferenceFirstLiveQueueEnergyEnvelope.potentialAfter rate rewards C_star C_h q t s hs control0 z -
          ReferenceFirstLiveQueueEnergyEnvelope.potentialBefore rate rewards C_star C_h q t s hs control0 z)
        (hafter.sub hbefore).integrableOn
        ((hcost.indicator hGambient).const_mul (11 / 2 : ℝ)).integrableOn, integral_const_mul]
  have hempty : ∀ (q : Fin (ConstructorDimensions.M p)) (v : Fin (t.val + 1)),
      (∫ z, f z ∂emptyM q v) ≤ ∫ z, g z ∂emptyM q v := by
    intro q v
    let s := v.val
    have hs : s ≤ t.val := Nat.lt_succ_iff.mp v.isLt
    let ν := ReferenceFirstLiveEmptyPendingMarkerLaw.muEmpty rate rewards C_star C_h q t s hs control0
    let G := ReferenceFirstLiveEmptyPendingAcceptedMoments.G rate rewards C_star C_h q t s hs control0
    let A := {z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
      rate rewards C_star C_h q t s hs control0 | z.val.val.1.1 = ids}
    have hactive (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
        rate rewards C_star C_h q t s hs control0) : z.val.val ∈ phase 4 := by
      rw [ReferenceFirstLiveCalendarIntegralAssembly.sourcePhase_empty_iUnion rate rewards C_star C_h t control0]
      exact Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨v, ⟨z.val, z.property, rfl⟩⟩⟩
    apply hcell _ (ReferenceFirstLiveSourcePhasePartition.forgetEmpty
      rate rewards C_star C_h q t s hs control0) (measurable_subtype_coe.comp measurable_subtype_coe)
    · rw [ReferenceFirstLiveSourcePhasePartition.muEmpty_map_original]
      exact Measure.restrict_le_self
    · exact fun z => Or.inr (hactive z)
    · have hb := fixedIDEmptyPendingEnergyBudget rate rewards C_star C_h control0 ids q t s hs
      have hm : c * ν.real (A ∩ G) ≤ c * ν.real A :=
        mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_left) hC
      refine le_trans ?_ (hb.trans hm)
      have hbefore := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_potentialBefore
        rate rewards C_star C_h q t s hs control0
      have hafter := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_potentialAfter
        rate rewards C_star C_h q t s hs control0
      have hcost := ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.integrable_weightedBacklogBefore
        rate rewards C_star C_h q t s hs control0
      have hGambient := ReferenceFirstLiveEmptyPendingAcceptedMoments.measurableSet_G_ambient
        rate rewards C_star C_h q t s hs control0
      have heq (z : ReferenceFirstLiveEmptyPendingMarkerLaw.Zempty
          rate rewards C_star C_h q t s hs control0) :
          delta z.val.val =
            (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter rate rewards C_star C_h q t s hs control0 z -
              ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore rate rewards C_star C_h q t s hs control0 z) +
            (11 / 2 : ℝ) * G.indicator
              (ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.weightedBacklogBefore rate rewards C_star C_h q t s hs control0) z := by
        dsimp only [delta]
        change (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLivePotentialAt
          rate rewards C_star C_h (t.val + 1) z.val.val -
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLivePotentialAt
          rate rewards C_star C_h t.val z.val.val) + (11 / 2 : ℝ) * LIVE t z.val.val = _
        rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.emptyFirstWindowPotentialAfter_eq rate rewards C_star C_h q t s hs control0 z,
          ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.emptyFirstWindowPotentialBefore_eq rate rewards C_star C_h q t s hs control0 z,
          retained_cost_on_continuing rate rewards C_star C_h control0 t z.val.val (Or.inr (hactive z))]
        have hsafe := ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.emptyFirstWindowOldOverflowFalse_iff_G
          rate rewards C_star C_h q t s hs control0 z
        by_cases hz : z ∈ G
        · simp only [ite_eq_left (hsafe.mpr hz), Set.indicator_of_mem hz]
          change _ + (11 / 2 : ℝ) * ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.firstLiveWeightedBacklogAt
            rate rewards C_star C_h t.val z.val.val = _
          rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.emptyFirstWindowWeightedBacklogBefore_eq
            rate rewards C_star C_h q t s hs control0 z]
        · simp only [ite_eq_right (fun h => hz (hsafe.mp h)), Set.indicator_of_notMem hz]
      change (∫ z in A, delta z.val.val ∂ν) ≤ _
      simp_rw [heq]
      dsimp only [A, G, ν]
      rw [integral_add (f := fun z =>
          ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialAfter rate rewards C_star C_h q t s hs control0 z -
          ReferenceFirstLiveEmptyPendingQueueEnergyEnvelope.potentialBefore rate rewards C_star C_h q t s hs control0 z)
        (hafter.sub hbefore).integrableOn
        ((hcost.indicator hGambient).const_mul (11 / 2 : ℝ)).integrableOn, integral_const_mul]
  have hexception : ∀ (i : Fin 6), i = 0 ∨ i = 1 ∨ i = 5 →
      (∫ z in phase i, f z ∂mu) ≤ ∫ z in phase i, g z ∂mu := by
    intro i hi
    have hz : (∫ z in phase i, f z ∂mu) = 0 := by
      apply integral_eq_zero_of_ae
      apply (ae_restrict_iff'
        (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
          rate rewards C_star C_h t control0 i)).mpr
      filter_upwards [] with z hz
      change f z = (0 : ℝ)
      have hm : z ∈ phase 0 ∨ z ∈ phase 1 ∨ z ∈ phase 5 := by
        rcases hi with rfl | rfl | rfl
        · exact Or.inl hz
        · exact Or.inr (Or.inl hz)
        · exact Or.inr (Or.inr hz)
      have hd := calendar_increment_zero_on_exception rate rewards C_star C_h t z hm
      have hdis (i j : Fin 6) (hi : z ∈ phase i) (hj : z ∈ phase j) : i = j := by
        by_contra hij
        exact Set.disjoint_left.mp
          (ReferenceFirstLiveSourcePhasePartition.source_phases_disjoint
            rate rewards C_star C_h t hij) hi hj
      have hnot : z ∉ phase 2 ∪ (phase 3 ∪ phase 4) := by
        intro ha
        rcases hm with h0 | h1 | h5 <;> rcases ha with h2 | h3 | h4
        · have he := hdis _ _ h0 h2; norm_num at he
        · have he := hdis _ _ h0 h3; norm_num at he
        · have he := hdis _ _ h0 h4; norm_num at he
        · have he := hdis _ _ h1 h2; norm_num at he
        · have he := hdis _ _ h1 h3; norm_num at he
        · have he := hdis _ _ h1 h4; norm_num at he
        · have he := hdis _ _ h5 h2; norm_num at he
        · have he := hdis _ _ h5 h3; norm_num at he
        · have he := hdis _ _ h5 h4; norm_num at he
      have hc : LIVE t z = 0 := by
        unfold ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
        rw [ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedEnabledEvent_eq_phaseRestriction
          rate rewards C_star C_h t control0]
        exact Set.indicator_of_notMem (fun h => hnot h.1) _
      have hd' : delta z = 0 := by simp only [delta, hd, hc, mul_zero, add_zero]
      by_cases hmem : z ∈ D
      · simpa only [f, Set.indicator_of_mem hmem, delta] using hd'
      · exact Set.indicator_of_notMem hmem delta
    rw [hz]
    exact integral_nonneg (fun z => Set.indicator_nonneg (fun _ _ => hC) z)
  have htotal : (∫ z, f z ∂mu) ≤ ∫ z, g z ∂mu := by
    rw [integral_source_cells rate rewards C_star C_h control0 t hf,
      integral_source_cells rate rewards C_star C_h control0 t hg]
    apply add_le_add
    · apply add_le_add
      · exact add_le_add (add_le_add
          (hexception 0 (Or.inl rfl)) (hexception 1 (Or.inr (Or.inl rfl))))
          (hexception 5 (Or.inr (Or.inr rfl)))
      · exact Finset.sum_le_sum (fun q _ => hbirth q)
    · apply Finset.sum_le_sum
      intro q _
      exact Finset.sum_le_sum (fun v _ => add_le_add (hplus q v) (hempty q v))
  have htotal' : (∫ z in D, delta z ∂mu) ≤ c * (mu).real (D ∩ E) := by
    calc
      _ = ∫ z, f z ∂mu := (integral_indicator hD).symm
      _ ≤ ∫ z, g z ∂mu := htotal
      _ = c * (mu).real (D ∩ E) := by
        dsimp only [g]
        rw [integral_indicator (hD.inter hE), integral_const]
        simp only [smul_eq_mul, measureReal_restrict_apply_univ, mul_comm]
  dsimp only [delta] at htotal'
  rw [integral_add (f := fun z => V (t.val + 1) z - V t.val z)
    ((hV _).sub (hV _)).integrableOn
    (hL.const_mul (11 / 2 : ℝ)).integrableOn, integral_const_mul] at htotal'
  exact htotal'

end Assembly

local notation "mu" => sourceInputLaw p
local notation "D" => ReferenceFixedIDSourceSection.fixedIDSourceSection ids
local notation "c" => CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)
local notation "Phi" => ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential rate rewards C_star C_h
local notation "V" => ReferenceFirstLiveCalendarPrefixReadout.firstWindowPotentialAt rate rewards C_star C_h
local notation "LIVE" => ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost rate rewards C_star C_h
local notation "OLD" => ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld rate rewards C_star C_h
local notation "VP" => ReferenceFirstCollectionCurrentQueueEnergy.VPlus rate rewards C_star C_h
local notation "VM" => ReferenceFirstCollectionCurrentQueueEnergy.VMinus rate rewards C_star C_h
local notation "G" => ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h
local notation "B" => ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog rate rewards C_star C_h
local notation "CP" => ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus rate rewards C_star C_h
local notation "CM" => ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus rate rewards C_star C_h
local notation "CB" => ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog rate rewards C_star C_h

private theorem sum_calendar_sub (b : ℕ → ℝ) (n : ℕ) :
    (∑ t : Fin n, (b (t.val + 1) - b t.val)) = b n - b 0 := by
  induction n with
  | zero => simp only [Fin.sum_univ_zero, sub_self]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

include control0 in
/-- The actual first-invocation quadratic cost, scaled by the literal ID atom
mass under the original source law. All inputs are root data; in particular,
no conditional law, moment, survival, or successful-call premise is supplied. -/
public theorem fixedIDFirstInvocationCostBudget :
    (11 / 2 : ℝ) * (∫ z in D,
      ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
        rate rewards C_star C_h z ∂mu) ≤
      c * (p.T : ℝ) * (CompletePublicTable.idArrayMeasure p).real {ids} := by
  have hC : 0 ≤ c :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.sourceDriftConstant_nonneg
  have hPhi (n : ℕ) (hn : n ≤ p.T) :=
    (ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
      rate rewards C_star C_h n hn).2
  have hV (n : ℕ) := ReferenceFirstLiveCalendarPrefixReadout.integrable_firstWindowPotentialAt
    rate rewards C_star C_h n
  have hL (t : Fin p.T) :=
    ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.integrable_retainedWeightedBacklogCost
      rate rewards C_star C_h t control0
  have hO (t : Fin p.T) :=
    ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.old_readouts_regular
      rate rewards C_star C_h control0 t
  have hP (u t : Fin p.T) := ReferenceFirstCollectionCurrentQueueEnergy.VPlus_integrable
    rate rewards C_star C_h control0 u t
  have hM (u t : Fin p.T) := ReferenceFirstCollectionCurrentQueueEnergy.VMinus_integrable
    rate rewards C_star C_h control0 u t
  have hB (u t : Fin p.T) : Integrable ((G u t).indicator (B u t)) mu :=
    (ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog_integrable
      rate rewards C_star C_h control0 u t).indicator
      ((ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le' (t.val + 1) _
        (ReferenceFirstCollectionCurrentRetainedGate.measurableSet_G
          rate rewards C_star C_h control0 u t))
  have hpre (t : Fin p.T) :
      (∫ z in D, Phi (t.val + 1) z - Phi t.val z ∂mu) +
        (11 / 2 : ℝ) * (∫ z in D, LIVE t z + OLD t z ∂mu) ≤
      c * ((mu).real (D ∩
          (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 2 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 3 ∪
            ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h t 4)) +
        (mu).real (D ∩ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h t)) := by
    have hl := fixedIDLiveEnergyBudget rate rewards C_star C_h control0 ids t
    have ho := fixedIDOldEnergyBudget rate rewards C_star C_h control0 ids t
    have heq : (fun z : SourceInput p => Phi (t.val + 1) z - Phi t.val z) =
        fun z => (V (t.val + 1) z - V t.val z) +
          ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.dOld rate rewards C_star C_h t z := by
      funext z
      exact ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_calendar_increment
        rate rewards C_star C_h t z
    rw [heq, integral_add (f := fun z => V (t.val + 1) z - V t.val z)
      ((hV _).sub (hV _)).integrableOn (hO t).2.1.integrableOn,
      integral_add (hL t).integrableOn (hO t).2.2.2.integrableOn]
    linarith only [hl, ho]
  have hstep (t : Fin p.T) :
      ((∫ z in D, Phi (t.val + 1) z - Phi t.val z ∂mu) +
        ∑ u : Fin p.T, ∫ z in D, VP u t z - VM u t z ∂mu) +
      (11 / 2 : ℝ) * ((∫ z in D, LIVE t z + OLD t z ∂mu) +
        ∑ u : Fin p.T, ∫ z in D, (G u t).indicator (B u t) z ∂mu) ≤
      c * (CompletePublicTable.idArrayMeasure p).real {ids} := by
    have hc := Finset.sum_le_sum fun (u : Fin p.T) (_ : u ∈ Finset.univ) =>
      fixedIDCurrentEnergyBudget rate rewards C_star C_h control0 ids u t
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hc
    have hm := mul_le_mul_of_nonneg_left
      (fixedIDCalendarMass_le rate rewards C_star C_h control0 ids t) hC
    linarith only [hpre t, hc, hm]
  have hsum := Finset.sum_le_sum fun (t : Fin p.T) (_ : t ∈ Finset.univ) => hstep t
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have htel : (∑ t : Fin p.T, ∫ z in D, Phi (t.val + 1) z - Phi t.val z ∂mu) =
      ∫ z in D, Phi p.T z ∂mu := by
    rw [← integral_finsetSum Finset.univ
      (f := fun (t : Fin p.T) z => Phi (t.val + 1) z - Phi t.val z) (fun t _ =>
        ((hPhi _ (Nat.succ_le_of_lt t.isLt)).sub (hPhi _ t.isLt.le)).integrableOn)]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [sum_calendar_sub (fun n => Phi n z) p.T, ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_zero
      rate rewards C_star C_h z, sub_zero]
  have hcur : (∑ t : Fin p.T, ∑ u : Fin p.T, ∫ z in D, VP u t z - VM u t z ∂mu) =
      ∫ z in D, CP z - CM z ∂mu := by
    simp_rw [← integral_finsetSum Finset.univ
      (f := fun (u : Fin p.T) z => VP u _ z - VM u _ z)
      (fun u _ => ((hP u _).sub (hM u _)).integrableOn)]
    rw [← integral_finsetSum Finset.univ
      (f := fun (t : Fin p.T) z => ∑ u : Fin p.T, (VP u t z - VM u t z))
      (fun t _ => integrable_finsetSum Finset.univ (fun u _ => ((hP u t).sub (hM u t)).integrableOn))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [Finset.sum_comm]
    simp only [ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus,
      ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus, Finset.sum_sub_distrib]
  have hcost : (∑ t : Fin p.T, ∫ z in D, LIVE t z + OLD t z ∂mu) +
      (∑ t : Fin p.T, ∑ u : Fin p.T, ∫ z in D, (G u t).indicator (B u t) z ∂mu) =
      ∫ z in D, ReferenceFirstCollectionFirstInvocationRawPotential.firstInvocationCost
        rate rewards C_star C_h z ∂mu := by
    simp_rw [← integral_finsetSum Finset.univ
      (f := fun (u : Fin p.T) z => (G u _).indicator (B u _) z)
      (fun u _ => (hB u _).integrableOn)]
    rw [← integral_finsetSum Finset.univ
        (f := fun (t : Fin p.T) z => LIVE t z + OLD t z)
        (fun t _ => ((hL t).add (hO t).2.2.2).integrableOn),
      ← integral_finsetSum Finset.univ
        (f := fun (t : Fin p.T) z => ∑ u : Fin p.T, (G u t).indicator (B u t) z)
        (fun t _ => integrable_finsetSum Finset.univ (fun u _ => (hB u t).integrableOn))]
    rw [← integral_add
      (f := fun z => ∑ t : Fin p.T, (LIVE t z + OLD t z))
      (g := fun z => ∑ t : Fin p.T, ∑ u : Fin p.T, (G u t).indicator (B u t) z)
      (integrable_finsetSum Finset.univ (fun t _ => ((hL t).add (hO t).2.2.2).integrableOn))
      (integrable_finsetSum Finset.univ (fun t _ =>
        integrable_finsetSum Finset.univ (fun u _ => (hB u t).integrableOn)))]
    apply integral_congr_ae
    filter_upwards [] with z
    rw [ReferenceFirstCollectionOriginalPrefixLearning.firstInvocationCost_eq_energyIntegrand
      rate rewards C_star C_h z]
    congr 1
    rw [Finset.sum_comm]
    rfl
  rw [htel, hcur, hcost] at hsum
  have hCP := ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_integrable
    rate rewards C_star C_h control0
  have hCM := ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
    rate rewards C_star C_h control0
  have hrem : 0 ≤ (∫ z in D, Phi p.T z ∂mu) + (∫ z in D, CP z - CM z ∂mu) := by
    rw [← integral_add (g := fun z => CP z - CM z)
      (hPhi _ le_rfl).integrableOn (hCP.sub hCM).integrableOn]
    apply integral_nonneg
    intro z
    have hin := ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.callVMinus_le_preCallPotential_terminal
      rate rewards C_star C_h z
    have hout := ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_nonneg rate rewards C_star C_h z
    change 0 ≤ Phi p.T z + (CP z - CM z)
    linarith only [hin, hout]
  have hfinal := le_trans (le_add_of_nonneg_left hrem) hsum
  convert hfinal using 1
  ring

end Bandits.Support.ReferenceFirstCollectionFixedIDWeightedCostBudget

end
