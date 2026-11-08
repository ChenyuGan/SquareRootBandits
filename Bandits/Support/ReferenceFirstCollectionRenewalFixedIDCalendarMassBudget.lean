/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalOriginalCalendarMassBudget
public import Bandits.Support.ReferenceFixedIDSourceSection

import Mathlib.Tactic

/-!
# Localized original-source calendar mass for one fixed ID array

Every date's LIVE, OLD, retained first-call, and actual post-call gates are
intersected with the literal fixed-ID section of the original source law.
Renewal-cell masses remain unnormalized, including on null cells.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (ids : CompletePublicTable.IDArray p)

local notation "S" => SourceInput p
local notation "D" =>
  ReferenceFixedIDSourceSection.fixedIDSourceSection (p := p) ids
local notation "phase234" dateArg:max =>
  (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h dateArg 2 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h dateArg 3 ∪
    ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h dateArg 4)
local notation "oldGate" dateArg:max =>
  ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h dateArg
local notation "currentGate" cutArg:max dateArg:max =>
  ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h cutArg dateArg
local notation "postCallGate" cutArg:max callArg:max dateArg:max =>
  ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate
    rate rewards C_star C_h cutArg callArg dateArg

local instance sourceInputMeasurableSpace : MeasurableSpace S := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private theorem sourceInputLaw_measure_ne_top
    (E : Set S) : sourceInputLaw p E ≠ (⊤ : ENNReal) := by
  have hprob : IsProbabilityMeasure (sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  apply ne_of_lt
  calc
    sourceInputLaw p E ≤ sourceInputLaw p Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := hprob.measure_univ
    _ < (⊤ : ENNReal) := ENNReal.one_lt_top

/-- The fixed-ID section has the exact original fair-bit ID atom mass. -/
theorem fixedIDSection_real_eq_idAtom :
    (sourceInputLaw p).real D = (CompletePublicTable.idArrayMeasure p).real {ids} :=
  ReferenceFixedIDSourceSection.sourceInputLaw_real_fixedIDSourceSection
    (p := p) ids

private theorem measurableSet_D : MeasurableSet D :=
  ReferenceFixedIDSourceSection.measurable_fixedIDSourceSection (p := p) ids

private theorem measurableSet_inter_D (A : Set S) (hA : MeasurableSet A) :
    MeasurableSet (D ∩ A) := by
  have hD : MeasurableSet D := measurableSet_D ids
  exact MeasurableSet.inter hD hA

/-- The literal fixed-ID slice of one existing renewal-call subtype. -/
@[expose] public def renewalIDSection (u t : Fin p.T) :
    Set (ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t) :=
  (Subtype.val : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t → S) ⁻¹' D

private theorem measurableSet_renewalIDSection (u t : Fin p.T) :
    MeasurableSet (renewalIDSection rate rewards C_star C_h ids u t) := by
  change MeasurableSet
    ((Subtype.val :
      ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t → S) ⁻¹'
      ReferenceFixedIDSourceSection.fixedIDSourceSection (p := p) ids)
  have hD : MeasurableSet D := measurableSet_D ids
  exact MeasurableSet.preimage hD measurable_subtype_coe

private theorem measurableSet_phase234 (control0 : TimeControl p)
    (q : Fin p.T) : MeasurableSet (phase234 q) := by
  exact ((ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h q control0 2).union
    (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h q control0 3)).union
    (ReferenceFirstLiveSourcePhasePartition.measurableSet_sourcePhase
      rate rewards C_star C_h q control0 4)

private theorem measurableSet_oldGate (control0 : TimeControl p)
    (q : Fin p.T) : MeasurableSet (oldGate q) := by
  have hle :=
    (ReferenceSourcePrefixHistoryFiltration.sourcePrefixFiltration control0).le'
      (q.val + 1)
  exact hle _ (ReferenceFirstCollectionOldCalendarExponentialStep.measurableSet_G
    rate rewards C_star C_h control0 q)

private theorem measurableSet_currentGate (control0 : TimeControl p)
    (u q : Fin p.T) : MeasurableSet (currentGate u q) :=
  ReferenceFirstCollectionPrecallFirstCallMassBudget.measurableSet_currentRetainedGate_ambient
    rate rewards C_star C_h q control0 u

private theorem measurableSet_postGateImage (control0 : TimeControl p)
    (u t q : Fin p.T) :
    MeasurableSet
      (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
        rate rewards C_star C_h u t q) :=
  ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.measurableSet_postGateSourceImage
    rate rewards C_star C_h control0 u t q

private theorem localized_union_real (A B : Set S)
    (hB : MeasurableSet B)
    (hAB : Disjoint A B) :
    (sourceInputLaw p).real (D ∩ A) + (sourceInputLaw p).real (D ∩ B) = (sourceInputLaw p).real (D ∩ (A ∪ B)) := by
  have hdisj : Disjoint (D ∩ A) (D ∩ B) := by
    apply Set.disjoint_left.mpr
    intro z hzA hzB
    exact (Set.disjoint_left.mp hAB) hzA.2 hzB.2
  have hset : D ∩ (A ∪ B) = (D ∩ A) ∪ (D ∩ B) := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_union]
    tauto
  rw [hset]
  exact (measureReal_union hdisj (measurableSet_inter_D ids B hB)
    (sourceInputLaw_measure_ne_top (D ∩ A))
    (sourceInputLaw_measure_ne_top (D ∩ B))).symm

private theorem localized_currentGate_sum_eq_union
    (control0 : TimeControl p) (q : Fin p.T) :
    (∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ currentGate u q)) =
      (sourceInputLaw p).real (D ∩ ⋃ u : Fin p.T, currentGate u q) := by
  have hpair : Pairwise (fun u v : Fin p.T =>
      Disjoint (D ∩ currentGate u q) (D ∩ currentGate v q)) := by
    intro u v huv
    apply Set.disjoint_left.mpr
    intro z hzu hzv
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.currentRetainedGate_pairwise_disjoint
        rate rewards C_star C_h q huv)) hzu.2 hzv.2
  have hmeas (u : Fin p.T) : MeasurableSet (D ∩ currentGate u q) :=
    measurableSet_inter_D ids (currentGate u q)
      (measurableSet_currentGate rate rewards C_star C_h control0 u q)
  have hsum := measureReal_iUnion_fintype hpair hmeas
    (fun u => sourceInputLaw_measure_ne_top (D ∩ currentGate u q))
  calc
    _ = (sourceInputLaw p).real (⋃ u : Fin p.T, D ∩ currentGate u q) := hsum.symm
    _ = (sourceInputLaw p).real (D ∩ ⋃ u : Fin p.T, currentGate u q) := by
      congr 1
      ext z
      simp only [Set.mem_iUnion, Set.mem_inter_iff]
      tauto

private theorem localized_preCallMass_eq_union
    (control0 : TimeControl p) (q : Fin p.T) :
    ((sourceInputLaw p).real (D ∩ phase234 q) + (sourceInputLaw p).real (D ∩ oldGate q)) +
      (∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ currentGate u q)) =
      (sourceInputLaw p).real (D ∩ ((phase234 q ∪ oldGate q) ∪ ⋃ u : Fin p.T, currentGate u q)) := by
  have hOldSub : oldGate q ⊆
      ReferenceFirstCollectionOldCalendarExponentialStep.E rate rewards C_star C_h q := by
    intro z hz
    exact hz.1.1
  have hphaseOld : Disjoint (phase234 q) (oldGate q) := by
    apply Set.disjoint_left.mpr
    intro z hzPhase hzOld
    exact (Set.disjoint_left.mp
      (ReferenceFirstCollectionPrecallLiveOldMass.old_event_disjoint_source_phases
        rate rewards C_star C_h q control0)) (hOldSub hzOld) hzPhase
  have hphaseCurrent :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.sourcePhase234_disjoint_currentRetainedGateUnion
      rate rewards C_star C_h q control0
  have hOldCurrent :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.oldG_disjoint_currentRetainedGateUnion
      rate rewards C_star C_h q
  have hbaseCurrent : Disjoint (phase234 q ∪ oldGate q) (⋃ u : Fin p.T, currentGate u q) := by
    apply Set.disjoint_left.mpr
    intro z hzBase hzCurrent
    rcases hzBase with hzPhase | hzOld
    · exact (Set.disjoint_left.mp hphaseCurrent) hzPhase hzCurrent
    · exact (Set.disjoint_left.mp hOldCurrent) hzOld hzCurrent
  have hphase := localized_union_real ids
    (phase234 q) (oldGate q)
    (measurableSet_oldGate rate rewards C_star C_h control0 q) hphaseOld
  have hcur := localized_currentGate_sum_eq_union
    rate rewards C_star C_h ids control0 q
  have hbase := localized_union_real ids
    (phase234 q ∪ oldGate q)
    (⋃ u : Fin p.T, currentGate u q)
    (MeasurableSet.iUnion (fun u =>
      measurableSet_currentGate rate rewards C_star C_h control0 u q))
    hbaseCurrent
  calc
    _ = (sourceInputLaw p).real (D ∩ (phase234 q ∪ oldGate q)) + (sourceInputLaw p).real (D ∩ ⋃ u : Fin p.T, currentGate u q) := by
      rw [hcur, hphase]
    _ = (sourceInputLaw p).real (D ∩ ((phase234 q ∪ oldGate q) ∪ ⋃ u : Fin p.T, currentGate u q)) := hbase

private theorem renewalIDSection_image_postGate (u t q : Fin p.T) :
    Subtype.val ''
      (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q) =
      D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
        rate rewards C_star C_h u t q := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨hx.1, ⟨x, hx.2, rfl⟩⟩
  · rintro ⟨hzD, ⟨x, hx, rfl⟩⟩
    exact ⟨x, ⟨hzD, hx⟩, rfl⟩

/-- Exact unnormalized transport after restricting both sides to the same
fixed-ID section. This identity also holds when the renewal cell is null. -/
theorem renewalID_postGate_real_eq_sourceImage (u t q : Fin p.T) :
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
        (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q) =
      (sourceInputLaw p).real
        (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
          rate rewards C_star C_h u t q) := by
  have hmeasure :
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t) (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q) =
        sourceInputLaw p (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
          rate rewards C_star C_h u t q) := by
    calc
      _ = sourceInputLaw p (Subtype.val ''
          (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) := by
        rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw]
        exact comap_subtype_coe_apply
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
            rate rewards C_star C_h u t)
          (sourceInputLaw p)
          (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)
      _ = sourceInputLaw p
          (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
            rate rewards C_star C_h u t q) := by
        rw [renewalIDSection_image_postGate rate rewards C_star C_h ids u t q]
  exact congrArg ENNReal.toReal hmeasure

/-- At each date the localized source-cell, OLD, retained-call, and actual
post-call masses add exactly to the localized union of their source events. -/
theorem localized_sourceDateMass_eq_union (control0 : TimeControl p)
    (q : Fin p.T) :
    (((sourceInputLaw p).real (D ∩ phase234 q) + (sourceInputLaw p).real (D ∩ oldGate q)) +
      (∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ currentGate u q))) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) =
    (sourceInputLaw p).real (D ∩
      (((phase234 q ∪ oldGate q) ∪ ⋃ u : Fin p.T, currentGate u q) ∪
        ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion
          rate rewards C_star C_h q)) := by
  have hpre := localized_preCallMass_eq_union
    rate rewards C_star C_h ids control0 q
  have hpost :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) =
        (sourceInputLaw p).real (D ∩
          ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion
            rate rewards C_star C_h q) := by
    let cellMass : Fin p.T × Fin p.T → ℝ := fun cell =>
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h cell.1 cell.2).real
        (renewalIDSection rate rewards C_star C_h ids cell.1 cell.2 ∩
          postCallGate cell.1 cell.2 q)
    let imageMass : Fin p.T × Fin p.T → ℝ := fun cell =>
      (sourceInputLaw p).real (D ∩
        ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
          rate rewards C_star C_h cell.1 cell.2 q)
    have htransport :
        (∑ cell : Fin p.T × Fin p.T, cellMass cell) =
          ∑ cell : Fin p.T × Fin p.T, imageMass cell := by
      apply Finset.sum_congr rfl
      intro cell _
      exact renewalID_postGate_real_eq_sourceImage
        rate rewards C_star C_h ids cell.1 cell.2 q
    have hpair : Pairwise (fun cell₁ cell₂ : Fin p.T × Fin p.T =>
        Disjoint
          (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
            rate rewards C_star C_h cell₁.1 cell₁.2 q)
          (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
            rate rewards C_star C_h cell₂.1 cell₂.2 q)) := by
      intro cell₁ cell₂ hne
      apply Set.disjoint_left.mpr
      intro z hz₁ hz₂
      exact (Set.disjoint_left.mp
        (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImages_pairwise_disjoint
          rate rewards C_star C_h q hne)) hz₁.2 hz₂.2
    have hmeas (cell : Fin p.T × Fin p.T) :
        MeasurableSet
          (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
            rate rewards C_star C_h cell.1 cell.2 q) :=
      measurableSet_inter_D ids
        (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
          rate rewards C_star C_h cell.1 cell.2 q)
        (measurableSet_postGateImage rate rewards C_star C_h control0
          cell.1 cell.2 q)
    calc
      _ = ∑ cell : Fin p.T × Fin p.T, cellMass cell := by
        change (∑ u : Fin p.T, ∑ t : Fin p.T, cellMass (u, t)) = _
        rw [← Fintype.sum_prod_type]
      _ = ∑ cell : Fin p.T × Fin p.T, imageMass cell := htransport
      _ = (sourceInputLaw p).real
          (⋃ cell : Fin p.T × Fin p.T,
            D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
              rate rewards C_star C_h cell.1 cell.2 q) := by
        simpa [imageMass] using
          (measureReal_iUnion_fintype hpair hmeas
            (fun cell => sourceInputLaw_measure_ne_top
              (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImage
                rate rewards C_star C_h cell.1 cell.2 q))).symm
      _ = (sourceInputLaw p).real
          (D ∩ ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion
            rate rewards C_star C_h q) := by
        congr 1
        ext z
        simp only [Set.mem_iUnion, Set.mem_inter_iff,
          ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion]
        tauto
  have hdisjBase :
      Disjoint ((phase234 q ∪ oldGate q) ∪ ⋃ u : Fin p.T, currentGate u q)
        (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion
          rate rewards C_star C_h q) :=
    ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.preCallSourceUnion_disjoint_postGateSourceImageUnion
      rate rewards C_star C_h control0 q
  have hmeasPre :
      MeasurableSet ((phase234 q ∪ oldGate q) ∪ ⋃ u : Fin p.T, currentGate u q) := by
    exact ((measurableSet_phase234 rate rewards C_star C_h control0 q).union
      (measurableSet_oldGate rate rewards C_star C_h control0 q)).union
      (MeasurableSet.iUnion (fun u =>
        measurableSet_currentGate rate rewards C_star C_h control0 u q))
  have hmeasPost : MeasurableSet
      (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion
        rate rewards C_star C_h q) := by
    apply MeasurableSet.iUnion
    intro cell
    exact measurableSet_postGateImage rate rewards C_star C_h control0
      cell.1 cell.2 q
  rw [hpre, hpost]
  exact localized_union_real ids
    ((phase234 q ∪ oldGate q) ∪ ⋃ u : Fin p.T, currentGate u q)
    (ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGateSourceImageUnion
      rate rewards C_star C_h q)
    hmeasPost hdisjBase

/-- The exact date budget is bounded by the mass of the same fixed-ID
section; it is not obtained by restricting an unconditional scalar bound. -/
theorem localized_sourceDateMass_le_sectionMass (control0 : TimeControl p)
    (q : Fin p.T) :
    (((sourceInputLaw p).real (D ∩ phase234 q) + (sourceInputLaw p).real (D ∩ oldGate q)) +
      (∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ currentGate u q))) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) ≤
      (sourceInputLaw p).real D := by
  rw [localized_sourceDateMass_eq_union rate rewards C_star C_h ids control0 q]
  exact measureReal_mono (fun _ hz => hz.1) (sourceInputLaw_measure_ne_top D)

private theorem postGate_eq_empty_of_le (u t q : Fin p.T)
    (hle : q.val ≤ t.val) : postCallGate u t q = ∅ := by
  have hnext : q.val ≠ t.val + 1 := by omega
  simp only [ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate,
    dite_eq_right hnext]
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
  rw [dite_eq_left q.isLt]
  have hfuture : ¬ t.val + 1 < q.val := by omega
  rw [dite_eq_right hfuture]

private theorem postGate_eq_future (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    postCallGate u t q =
      ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture := by
  have hnext : q.val ≠ t.val + 1 := by omega
  simp only [ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate,
    dite_eq_right hnext]
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
  rw [dite_eq_left q.isLt, dite_eq_left hfuture]

private theorem postGate_eq_next (u t q : Fin p.T)
    (hnext : q.val = t.val + 1) :
    postCallGate u t q =
      ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
        rate rewards C_star C_h u t (by omega) := by
  simp only [ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate,
    dite_eq_left hnext]

/-- Summing the exact localized post-call gates over calendar dates splits
into the actual next date (zero at the terminal date) and strict future gates. -/
theorem localized_postGateMass_sum_eq_next_and_future (u t : Fin p.T) :
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) =
      (if hnext : t.val + 1 < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
          (renewalIDSection rate rewards C_star C_h ids u t ∩
            ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
              rate rewards C_star C_h u t hnext)
       else 0) +
        (∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t q.val)) := by
  classical
  by_cases hnext : t.val + 1 < p.T
  · let f : ℕ → ℝ := fun n =>
      if hn : n < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
          (renewalIDSection rate rewards C_star C_h ids u t ∩
            postCallGate u t ⟨n, hn⟩)
      else 0
    have hsum :
        (∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) =
          ∑ n ∈ Finset.range p.T, f n := by
      calc
        _ = ∑ q : Fin p.T, f q.val := by
          apply Finset.sum_congr rfl
          intro q _
          simp only [f, dite_eq_left q.isLt]
        _ = ∑ n ∈ Finset.range p.T, f n := Fin.sum_univ_eq_sum_range f p.T
    have hprefix : ∑ n ∈ Finset.range (t.val + 1), f n = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      have hnt : n < t.val + 1 := Finset.mem_range.mp hn
      have hlt : n < p.T := by omega
      dsimp [f]
      rw [dite_eq_left hlt]
      have hle : (⟨n, hlt⟩ : Fin p.T).val ≤ t.val := by
        change n ≤ t.val
        omega
      rw [postGate_eq_empty_of_le rate rewards C_star C_h u t ⟨n, hlt⟩ hle]
      simp
    have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_of_lt hnext)
    have hinterval : Finset.Ico (t.val + 1) p.T =
        insert (t.val + 1) (Finset.Ico (t.val + 2) p.T) :=
      (Finset.insert_Ico_add_one_left_eq_Ico hnext).symm
    have hnot : t.val + 1 ∉ Finset.Ico (t.val + 2) p.T := by simp
    have hnextTerm :
        f (t.val + 1) =
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩
              ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext) := by
      dsimp [f]
      rw [dite_eq_left hnext]
      exact congrArg (fun g : Set
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t) =>
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
        (renewalIDSection rate rewards C_star C_h ids u t ∩ g))
        (postGate_eq_next rate rewards C_star C_h u t
          ⟨t.val + 1, hnext⟩ rfl)
    have hfutureSum :
        (∑ n ∈ Finset.Ico (t.val + 2) p.T, f n) =
          ∑ q : Fin p.T,
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                  rate rewards C_star C_h u t q.val) := by
      let g : ℕ → ℝ := fun n =>
        if hn : n < p.T then
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t n)
        else 0
      have hrange :
          (∑ q : Fin p.T,
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                  rate rewards C_star C_h u t q.val)) =
            ∑ n ∈ Finset.range p.T, g n := by
        calc
          _ = ∑ q : Fin p.T, g q.val := by
            apply Finset.sum_congr rfl
            intro q _
            simp only [g, dite_eq_left q.isLt]
          _ = ∑ n ∈ Finset.range p.T, g n := Fin.sum_univ_eq_sum_range g p.T
      have hzeroprefix : ∑ n ∈ Finset.range (t.val + 2), g n = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hnt : n < t.val + 2 := Finset.mem_range.mp hn
        have hlt : n < p.T := by omega
        dsimp [g]
        rw [ite_eq_left hlt]
        unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
        rw [dite_eq_left hlt]
        have hfuture : ¬ t.val + 1 < n := by omega
        rw [dite_eq_right hfuture]
        simp
      have hleFuture : t.val + 2 ≤ p.T := by omega
      have hsplitFuture := Finset.sum_range_add_sum_Ico g hleFuture
      have htail :
          (∑ n ∈ Finset.Ico (t.val + 2) p.T, g n) =
            ∑ n ∈ Finset.Ico (t.val + 2) p.T, f n := by
        apply Finset.sum_congr rfl
        intro n hn
        have hnt := Finset.mem_Ico.mp hn
        have hlt : n < p.T := hnt.2
        have hfuture : t.val + 1 < n := by omega
        dsimp [g, f]
        rw [ite_eq_left hlt, dite_eq_left hlt]
        have hgate :
            postCallGate u t ⟨n, hlt⟩ =
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t n := by
          have hneq : n ≠ t.val + 1 := by omega
          unfold ReferenceFirstCollectionRenewalOriginalCalendarMassBudget.postGate
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
          simp only [dite_eq_right hneq, dite_eq_left hlt, dite_eq_left hfuture]
        exact congrArg (fun E : Set
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
              rate rewards C_star C_h u t) =>
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩ E)) hgate.symm
      calc
        _ = ∑ n ∈ Finset.Ico (t.val + 2) p.T, g n := htail.symm
        _ = ∑ n ∈ Finset.range p.T, g n := by
          rw [← hsplitFuture, hzeroprefix]
          simp
        _ = _ := hrange.symm
    rw [hsum, ← hsplit, hprefix, zero_add, hinterval,
      Finset.sum_insert hnot, hnextTerm, hfutureSum]
    simp [hnext]
  · have hlast : t.val + 1 = p.T := by omega
    have hzero :
        ∀ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q) = 0 := by
      intro q
      have hqle : q.val ≤ t.val := by omega
      rw [postGate_eq_empty_of_le rate rewards C_star C_h u t q hqle]
      simp
    have hfutureZero :
        ∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t q.val) = 0 := by
      apply Finset.sum_eq_zero
      intro q _
      unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
      rw [dite_eq_left q.isLt]
      have hfuture : ¬ t.val + 1 < q.val := by omega
      rw [dite_eq_right hfuture]
      simp
    simp [hzero, hnext, hfutureZero]

/-- The actual finite retained first-call union is charged once after
intersecting each original gate with the same fixed-ID section. -/
theorem localized_retainedFirstCall_real_eq_sum (control0 : TimeControl p) :
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      (sourceInputLaw p).real (D ∩ currentGate u t) =
        (sourceInputLaw p).real
          (D ∩ ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) := by
  have hpoint (z : S) :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (D ∩ currentGate u t).indicator (fun _ : S => (1 : ℝ)) z) =
        (D ∩ ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h).indicator (fun _ : S => (1 : ℝ)) z := by
    by_cases hzD : z ∈ D
    · simpa [Set.indicator, hzD] using
        (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall_indicator_sum_eq
          rate rewards C_star C_h z)
    · simp [Set.indicator, hzD]
  calc
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : S, (D ∩ currentGate u t).indicator (fun _ : S => (1 : ℝ)) z ∂(sourceInputLaw p) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro t _
      symm
      exact integral_indicator_one
        (measurableSet_inter_D ids (currentGate u t)
          (measurableSet_currentGate rate rewards C_star C_h control0 u t))
    _ = ∫ z : S,
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          (D ∩ currentGate u t).indicator (fun _ : S => (1 : ℝ)) z ∂(sourceInputLaw p) := by
      symm
      rw [integral_finsetSum Finset.univ (fun u _ =>
        integrable_finsetSum Finset.univ (fun t _ =>
          (integrable_const (1 : ℝ)).indicator
            (measurableSet_inter_D ids (currentGate u t)
              (measurableSet_currentGate rate rewards C_star C_h control0 u t))))]
      apply Finset.sum_congr rfl
      intro u _
      rw [integral_finsetSum Finset.univ (fun t _ =>
        (integrable_const (1 : ℝ)).indicator
          (measurableSet_inter_D ids (currentGate u t)
            (measurableSet_currentGate rate rewards C_star C_h control0 u t)))]
    _ = ∫ z : S,
        (D ∩ ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h).indicator (fun _ : S => (1 : ℝ)) z ∂(sourceInputLaw p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hpoint
    _ = (sourceInputLaw p).real
        (D ∩ ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) :=
      integral_indicator_one (measurableSet_inter_D ids
        (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h)
        (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall_measurable
          rate rewards C_star C_h control0))

/-- Summing over q and then over a renewal cell, the same localized
post-call mass splits into its actual next-date and strict-future charges. -/
theorem localized_postGate_total_eq_next_future :
    (∑ q : Fin p.T, ∑ u : Fin p.T, ∑ t : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)) =
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      ((if hnext : t.val + 1 < p.T then
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩
              ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext)
        else 0) +
        ∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (renewalIDSection rate rewards C_star C_h ids u t ∩
              ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                rate rewards C_star C_h u t q.val)) := by
  calc
    _ = ∑ u : Fin p.T, ∑ q : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
          (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q) := by
      rw [Finset.sum_comm]
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ q : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
          (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q) := by
      apply Finset.sum_congr rfl
      intro u _
      exact Finset.sum_comm
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((if hnext : t.val + 1 < p.T then
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                  rate rewards C_star C_h u t hnext)
          else 0) +
          ∑ q : Fin p.T,
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                  rate rewards C_star C_h u t q.val)) := by
      apply Finset.sum_congr rfl
      intro u _
      apply Finset.sum_congr rfl
      intro t _
      exact localized_postGateMass_sum_eq_next_and_future
        rate rewards C_star C_h ids u t

/-- Integrated fixed-ID joint source-mass budget. It charges the actual
retained first-call union once and preserves terminal zero and strict-future
date semantics on every unnormalized renewal-cell law. -/
theorem localized_sum_sourceDateMass_le_horizon (control0 : TimeControl p) :
    (Finset.univ.sum (fun date : Fin p.T =>
      (sourceInputLaw p).real (D ∩ phase234 date) +
        (sourceInputLaw p).real (D ∩
          ReferenceFirstCollectionOldCalendarExponentialStep.G
            rate rewards C_star C_h date))) +
      (sourceInputLaw p).real
        (D ∩ ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ((if hnext : t.val + 1 < p.T then
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                  rate rewards C_star C_h u t hnext)
          else 0) +
          ∑ q : Fin p.T,
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (renewalIDSection rate rewards C_star C_h ids u t ∩
                ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                  rate rewards C_star C_h u t q.val))) ≤
      (p.T : ℝ) * (sourceInputLaw p).real D := by
  let A : Fin p.T → ℝ := fun q =>
    (sourceInputLaw p).real (D ∩ phase234 q) +
      (sourceInputLaw p).real (D ∩
        ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q)
  let Cmass : Fin p.T → ℝ := fun q =>
    ∑ u : Fin p.T, (sourceInputLaw p).real (D ∩ currentGate u q)
  let Hmass : Fin p.T → ℝ := fun q =>
    ∑ u : Fin p.T, ∑ t : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (renewalIDSection rate rewards C_star C_h ids u t ∩ postCallGate u t q)
  have hdate (q : Fin p.T) : (A q + Cmass q) + Hmass q ≤ (sourceInputLaw p).real D := by
    simpa only [A, Cmass, Hmass, add_assoc] using
      localized_sourceDateMass_le_sectionMass
        rate rewards C_star C_h ids control0 q
  have hsum :
      (∑ q : Fin p.T, ((A q + Cmass q) + Hmass q)) ≤
        ∑ _q : Fin p.T, (sourceInputLaw p).real D := by
    apply Finset.sum_le_sum
    intro q _
    exact hdate q
  have hsplit :
      (∑ q : Fin p.T, ((A q + Cmass q) + Hmass q)) =
        (∑ q : Fin p.T, A q) + (∑ q : Fin p.T, Cmass q) +
          (∑ q : Fin p.T, Hmass q) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcurrent :
      (∑ q : Fin p.T, Cmass q) =
        (sourceInputLaw p).real
          (D ∩ ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) := by
    dsimp [Cmass]
    rw [Finset.sum_comm]
    exact localized_retainedFirstCall_real_eq_sum
      rate rewards C_star C_h ids control0
  have hafter :
      (∑ q : Fin p.T, Hmass q) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ((if hnext : t.val + 1 < p.T then
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
                (renewalIDSection rate rewards C_star C_h ids u t ∩
                  ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                    rate rewards C_star C_h u t hnext)
            else 0) +
            ∑ q : Fin p.T,
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
                (renewalIDSection rate rewards C_star C_h ids u t ∩
                  ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
                    rate rewards C_star C_h u t q.val)) := by
    dsimp [Hmass]
    exact localized_postGate_total_eq_next_future
      rate rewards C_star C_h ids
  calc
    _ = (∑ q : Fin p.T, A q) +
        (∑ q : Fin p.T, Cmass q) + (∑ q : Fin p.T, Hmass q) := by
      rw [← hcurrent, ← hafter]
    _ = ∑ q : Fin p.T, ((A q + Cmass q) + Hmass q) := hsplit.symm
    _ ≤ ∑ _q : Fin p.T, (sourceInputLaw p).real D := hsum
    _ = (p.T : ℝ) * (sourceInputLaw p).real D := by simp

end Bandits.Support.ReferenceFirstCollectionRenewalFixedIDCalendarMassBudget

end
