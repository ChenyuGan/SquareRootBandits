/-
Copyright (c) 2026 Bandits Lean regret formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalWeightedEnergySourceTransport
public import Bandits.Support.ReferenceFirstCollectionPrecallFirstCallMassBudget
public import Bandits.Support.ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget
public import Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep

import Mathlib.Tactic

/-!
# Original-source occupancy through first renewal and retained future dates

The first-call LIVE, OLD, and current retained gates, together with the actual
after-call gates on the first-renewal source cells, form one datewise partition
of subsets of the original physical source. Their unnormalized masses fit a
single probability budget at each date and charge one shared horizon.
-/

public section

noncomputable section

open MeasureTheory
open Bandits.Support.ConstructorDimensions (Parameters)
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open scoped BigOperators Classical

namespace Bandits.Support.ReferenceFirstCollectionRenewalOriginalCalendarMassBudget

variable {p : Parameters}
  (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p

local instance sourceInputMeasurableSpace : MeasurableSpace S := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

private theorem sourceInputLaw_measure_ne_top
    (E : Set S) : μ E ≠ (⊤ : ENNReal) := by
  have hprob : IsProbabilityMeasure μ :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  apply ne_of_lt
  calc
    μ E ≤ μ Set.univ := measure_mono (Set.subset_univ _)
    _ = 1 := hprob.measure_univ
    _ < (⊤ : ENNReal) := ENNReal.one_lt_top

/-- The actual post-call retained gate at the first successor date, and the
existing strict-future gate at every later date. Earlier dates are empty by
the accepted future-gate definition. -/
@[expose] public def postGate (u t q : Fin p.T) : Set (ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t) :=
  if hnext : q.val = t.val + 1 then
    ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
      rate rewards C_star C_h u t (by omega)
  else
    ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
      rate rewards C_star C_h u t q.val

/-- The literal image of the existing renewal-source gate in its unchanged
original physical source coordinates. -/
@[expose] public def postGateSourceImage (u t q : Fin p.T) : Set S :=
  Subtype.val '' postGate rate rewards C_star C_h u t q

/-- Measurability of the first successor or strict-future gate in the
original-source subtype. -/
theorem measurableSet_postGate (control0 : TimeControl p)
    (u t q : Fin p.T) :
    MeasurableSet (postGate rate rewards C_star C_h u t q) := by
  by_cases hnext : q.val = t.val + 1
  · simp only [postGate, dite_eq_left hnext]
    exact ReferenceFirstCollectionRenewalNextDateExponentialStep.measurableSet_retainedNextDate_ambient
      rate rewards C_star C_h u t control0 (by omega)
  · simp only [postGate, dite_eq_right hnext]
    unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
    rw [dite_eq_left q.isLt]
    by_cases hfuture : t.val + 1 < q.val
    · rw [dite_eq_left hfuture]
      have hgate :=
        ReferenceFirstCollectionRenewalFutureExponentialIncrement.measurableSet_Gfuture
          rate rewards C_star C_h u t ⟨q.val, q.isLt⟩ hfuture control0
      have hle :=
        ReferenceFirstCollectionRenewalFutureControlLaw.futurePriorField_le
          rate rewards C_star C_h u t control0 ⟨q.val, q.isLt⟩ (by
            change t.val < q.val
            omega)
      exact hle _ hgate
    · rw [dite_eq_right hfuture]
      exact MeasurableSet.empty

/-- The image gate is measurable in the original source space by the
measurable embedding of this existing source-cell subtype. -/
theorem measurableSet_postGateSourceImage (control0 : TimeControl p)
    (u t q : Fin p.T) :
    MeasurableSet (postGateSourceImage rate rewards C_star C_h u t q) := by
  have hcell :=
    ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t
  have hem := MeasurableEmbedding.subtype_coe hcell
  exact hem.measurableSet_image.mpr
    (measurableSet_postGate rate rewards C_star C_h control0 u t q)

/-- Exact unnormalized transport of a gate mass to its image in the same
original-source renewal cell. This also holds for null cells. -/
theorem postGate_real_eq_sourceImage (u t q : Fin p.T) :
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q) =
      (sourceInputLaw p).real (postGateSourceImage rate rewards C_star C_h u t q) := by
  have hmeasure :
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t (postGate rate rewards C_star C_h u t q) =
        μ (postGateSourceImage rate rewards C_star C_h u t q) := by
    rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw]
    unfold postGateSourceImage
    exact comap_subtype_coe_apply
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t)
      (sourceInputLaw p) (postGate rate rewards C_star C_h u t q)
  exact congrArg ENNReal.toReal hmeasure

/-- Every image gate remains inside the actual selector cell that defines its
source subtype. -/
theorem postGateSourceImage_subset_renewalCallEvent (u t q : Fin p.T) :
    postGateSourceImage rate rewards C_star C_h u t q ⊆
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t := by
  rintro source ⟨z, _, rfl⟩
  exact z.property

/-- Images from distinct actual first-call cells are disjoint, for each date,
because they are subsets of the cells selected by the same first-call
selector. -/
theorem postGateSourceImages_pairwise_disjoint (q : Fin p.T) :
    Pairwise (fun cell₁ cell₂ : Fin p.T × Fin p.T =>
      Disjoint
        (postGateSourceImage rate rewards C_star C_h cell₁.1 cell₁.2 q)
        (postGateSourceImage rate rewards C_star C_h cell₂.1 cell₂.2 q)) := by
  intro cell₁ cell₂ hne
  have hcells :=
    ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEvents_disjoint
      rate rewards C_star C_h cell₁.1 cell₁.2 cell₂.1 cell₂.2 hne
  apply Set.disjoint_left.mpr
  intro source h₁ h₂
  exact (Set.disjoint_left.mp hcells)
    (postGateSourceImage_subset_renewalCallEvent
      rate rewards C_star C_h cell₁.1 cell₁.2 q h₁)
    (postGateSourceImage_subset_renewalCallEvent
      rate rewards C_star C_h cell₂.1 cell₂.2 q h₂)

/-- The finite union of actual after-call images at one date. -/
@[expose] public def postGateSourceImageUnion (q : Fin p.T) : Set S :=
  ⋃ cell : Fin p.T × Fin p.T,
    postGateSourceImage rate rewards C_star C_h cell.1 cell.2 q

/-- The exact mass of the after-call image union is the sum of the same
unnormalized renewal-cell masses. -/
theorem postGateMass_eq_sourceImageUnion (control0 : TimeControl p)
    (q : Fin p.T) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q)) =
      (sourceInputLaw p).real (postGateSourceImageUnion rate rewards C_star C_h q) := by
  let cellMass : Fin p.T × Fin p.T → ℝ := fun cell =>
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h cell.1 cell.2).real
      (postGate rate rewards C_star C_h cell.1 cell.2 q)
  let imageMass : Fin p.T × Fin p.T → ℝ := fun cell =>
    (sourceInputLaw p).real
      (postGateSourceImage rate rewards C_star C_h cell.1 cell.2 q)
  have htransport :
      (∑ cell : Fin p.T × Fin p.T, cellMass cell) =
        ∑ cell : Fin p.T × Fin p.T, imageMass cell := by
    apply Finset.sum_congr rfl
    intro cell _
    exact postGate_real_eq_sourceImage rate rewards C_star C_h
      cell.1 cell.2 q
  calc
    _ = ∑ cell : Fin p.T × Fin p.T, cellMass cell := by
      change (∑ u : Fin p.T, ∑ t : Fin p.T, cellMass (u, t)) = _
      rw [← Fintype.sum_prod_type]
    _ = ∑ cell : Fin p.T × Fin p.T, imageMass cell := htransport
    _ = (sourceInputLaw p).real (postGateSourceImageUnion rate rewards C_star C_h q) := by
      simpa [imageMass, postGateSourceImageUnion] using
        (measureReal_iUnion_fintype
        (postGateSourceImages_pairwise_disjoint rate rewards C_star C_h q)
        (fun cell => measurableSet_postGateSourceImage rate rewards C_star C_h
          control0 cell.1 cell.2 q)
        (fun cell => sourceInputLaw_measure_ne_top
          (postGateSourceImage rate rewards C_star C_h cell.1 cell.2 q))).symm

/-- The original LIVE phase union is strictly before the actual first-call
boundary. This reuses the public source windows and first-live endpoint API. -/
private theorem sourcePhase234_before_firstCallBoundary
    (control0 : TimeControl p) (q : Fin p.T) (z : S)
    (hz : z ∈ (ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4)) :
    q.val < ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
      rate rewards C_star C_h z := by
  rcases hz with hz23 | hz4
  · rcases hz23 with hz2 | hz3
    · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase] at hz2
      have hpos := ReferenceFirstLiveSourcePhasePartition.source_birth_window_pos
        rate rewards C_star C_h q control0 z hz2
      obtain ⟨_, hstart⟩ := hz2
      have hlen :=
        ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
          rate rewards C_star C_h z
      have hend :=
        ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
          rate rewards C_star C_h z
      omega
    · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase] at hz3
      rcases hz3 with ⟨_, hrest⟩
      rcases hrest with ⟨_, hwindow⟩
      rcases hwindow with ⟨hk, _⟩
      have hend :=
        ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
          rate rewards C_star C_h z
      have hlen :=
        ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
          rate rewards C_star C_h z
      omega
  · simp only [ReferenceFirstLiveSourcePhasePartition.sourcePhase] at hz4
    rcases hz4 with ⟨_, hrest⟩
    rcases hrest with ⟨_, hwindow⟩
    rcases hwindow with ⟨hk, _⟩
    have hend :=
      ReferenceFirstCollectionPrecallCalendarIncrementIdentity.firstLive_end_le_firstCallBoundary
        rate rewards C_star C_h z
    have hlen :=
      ReferenceFirstLiveSourcePhasePartition.wholeFirstLiveCells_length
        rate rewards C_star C_h z
    omega

/-- An after-call source image can occur only strictly after the first-call
boundary of its actual renewal cell. -/
theorem postGate_before_firstCallBoundary (u t q : Fin p.T)
    (source : S)
    (hsource : source ∈ postGateSourceImage rate rewards C_star C_h u t q) :
    ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary
      rate rewards C_star C_h source < q.val := by
  rcases hsource with ⟨z, hz, rfl⟩
  have hfirst : z.val ∈
      ReferenceCalendarCollectionCallControlLaw.firstCell
        rate rewards C_star C_h u t := by
    simpa only [ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell,
      ReferenceCalendarCollectionCallControlLaw.firstCell] using z.property.1
  have hboundary :=
    ReferenceFirstCollectionPrecallCalendarSupport.firstCallBoundary_on_firstCell
      rate rewards C_star C_h u t z.val hfirst
  have hafter : t.val < q.val := by
    by_cases hnext : q.val = t.val + 1
    · omega
    · change z ∈ (if h : q.val = t.val + 1 then _ else
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
          rate rewards C_star C_h u t q.val) at hz
      rw [dite_eq_right hnext] at hz
      unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt at hz
      by_cases hq : q.val < p.T
      · rw [dite_eq_left hq] at hz
        by_cases hfuture : t.val + 1 < q.val
        · rw [dite_eq_left hfuture] at hz
          exact by omega
        · rw [dite_eq_right hfuture] at hz
          simp at hz
      · rw [dite_eq_right hq] at hz
        simp at hz
  omega

/-- The original pre-call LIVE and OLD gates and the current retained gate at
this date are disjoint from every after-call source image by chronology. -/
theorem preCallSourceUnion_disjoint_postGateSourceImageUnion
    (control0 : TimeControl p) (q : Fin p.T) :
    Disjoint
      ((((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4) ∪ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) ∪ ⋃ u : Fin p.T, ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q))
      (postGateSourceImageUnion rate rewards C_star C_h q) := by
  apply Set.disjoint_left.mpr
  intro source hpre hpost
  obtain ⟨cell, hcell⟩ := Set.mem_iUnion.mp hpost
  rcases hpre with hpo | hcurrent
  · rcases hpo with hphase | hold
    · have hbefore := sourcePhase234_before_firstCallBoundary
        rate rewards C_star C_h control0 q source hphase
      have hafter := postGate_before_firstCallBoundary
        rate rewards C_star C_h cell.1 cell.2 q source hcell
      omega
    · have hE : source ∈
        ReferenceFirstCollectionOldCalendarExponentialStep.E
          rate rewards C_star C_h q := by
        change source ∈ ReferenceFirstCollectionOldCalendarExponentialStep.E
          rate rewards C_star C_h q ∩ _ ∩ _ at hold
        exact hold.1.1
      have hbefore :=
        (ReferenceFirstCollectionOldCalendarExponentialStep.mem_E_iff_beforeBoundary_and_oldCell
          rate rewards C_star C_h q source).mp hE |>.1
      have hafter := postGate_before_firstCallBoundary
        rate rewards C_star C_h cell.1 cell.2 q source hcell
      omega
  · obtain ⟨u, hu⟩ := Set.mem_iUnion.mp hcurrent
    have hboundary :=
      ReferenceFirstCollectionPrecallFirstCallMassBudget.currentRetainedGate_boundary_eq_date
        rate rewards C_star C_h q u source hu
    have hafter := postGate_before_firstCallBoundary
      rate rewards C_star C_h cell.1 cell.2 q source hcell
    omega

/-- Exact unnormalized additivity for all actual source gates at one date. -/
theorem sourceDateMass_eq_union (control0 : TimeControl p) (q : Fin p.T) :
    ((ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h q control0 + (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q)) +
      (∑ u : Fin p.T, (sourceInputLaw p).real (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q))) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q)) =
    (sourceInputLaw p).real
      (((((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4) ∪ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) ∪ ⋃ u : Fin p.T, ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q) ∪
        postGateSourceImageUnion rate rewards C_star C_h q)) := by
  have hpre :=
    ReferenceFirstCollectionPrecallFirstCallMassBudget.sourcePhase234_oldG_currentRetainedGate_real_add_eq_union
      rate rewards C_star C_h q control0
  have hpost := postGateMass_eq_sourceImageUnion
    rate rewards C_star C_h control0 q
  have hdisj :=
    preCallSourceUnion_disjoint_postGateSourceImageUnion
      rate rewards C_star C_h control0 q
  have hmeasPost :
      MeasurableSet (postGateSourceImageUnion rate rewards C_star C_h q) := by
    apply MeasurableSet.iUnion
    intro cell
    exact measurableSet_postGateSourceImage rate rewards C_star C_h control0
      cell.1 cell.2 q
  rw [hpre, hpost]
  exact (measureReal_union hdisj hmeasPost
    (sourceInputLaw_measure_ne_top
      ((((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4) ∪ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) ∪ ⋃ u : Fin p.T, ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)))
    (sourceInputLaw_measure_ne_top
      (postGateSourceImageUnion rate rewards C_star C_h q))).symm

/-- Sharp joint datewise occupancy: all original pre-call, first-call, and
after-call gates consume at most one unit of the same source probability. -/
theorem sourceDateMass_le_one (control0 : TimeControl p) (q : Fin p.T) :
    ((ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
        rate rewards C_star C_h q control0 + (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q)) +
      (∑ u : Fin p.T, (sourceInputLaw p).real (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q))) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q)) ≤ 1 := by
  rw [sourceDateMass_eq_union rate rewards C_star C_h control0 q]
  have hprob : IsProbabilityMeasure μ :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  calc
    (sourceInputLaw p).real
        (((((ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 2 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 3 ∪ ReferenceFirstLiveSourcePhasePartition.sourcePhase rate rewards C_star C_h q 4) ∪ ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q) ∪ ⋃ u : Fin p.T, ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q) ∪
          postGateSourceImageUnion rate rewards C_star C_h q)) ≤
        (sourceInputLaw p).real Set.univ :=
      measureReal_mono (Set.subset_univ _)
        (sourceInputLaw_measure_ne_top Set.univ)
    _ = 1 := by simp [Measure.real_def, hprob.measure_univ]

private theorem postGate_eq_empty_of_le (u t q : Fin p.T)
    (hle : q.val ≤ t.val) :
    postGate rate rewards C_star C_h u t q = ∅ := by
  have hnext : q.val ≠ t.val + 1 := by omega
  simp only [postGate, dite_eq_right hnext]
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
  rw [dite_eq_left q.isLt]
  have hfuture : ¬ t.val + 1 < q.val := by omega
  rw [dite_eq_right hfuture]

private theorem postGate_eq_future (u t q : Fin p.T)
    (hfuture : t.val + 1 < q.val) :
    postGate rate rewards C_star C_h u t q =
      ReferenceFirstCollectionRenewalFutureExponentialIncrement.Gfuture
        rate rewards C_star C_h u t q hfuture := by
  have hnext : q.val ≠ t.val + 1 := by omega
  simp only [postGate, dite_eq_right hnext]
  unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateAt
  rw [dite_eq_left q.isLt, dite_eq_left hfuture]

private theorem postGate_eq_next (u t q : Fin p.T)
    (hnext : q.val = t.val + 1) :
    postGate rate rewards C_star C_h u t q =
      ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
        rate rewards C_star C_h u t (by omega) := by
  simp only [postGate, dite_eq_left hnext]

/-- Summing the actual first-successor and strict-future gates over calendar
dates gives exactly one retained next-date mass and the literal strict-future
calendar mass. -/
theorem postGateMass_sum_eq (u t : Fin p.T) :
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q)) =
      (if hnext : t.val + 1 < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
          (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
            rate rewards C_star C_h u t hnext)
       else 0) +
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t := by
  classical
  by_cases hnext : t.val + 1 < p.T
  · let f : ℕ → ℝ := fun n =>
      if hn : n < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
          (postGate rate rewards C_star C_h u t ⟨n, hn⟩)
      else 0
    have hsum :
        (∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q)) =
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
      rw [postGate_eq_empty_of_le rate rewards C_star C_h u t
        ⟨n, hlt⟩ hle]
      simp
    have hsplit := Finset.sum_range_add_sum_Ico f (Nat.le_of_lt hnext)
    have hinterval :
        Finset.Ico (t.val + 1) p.T =
          insert (t.val + 1) (Finset.Ico (t.val + 2) p.T) := by
      exact (Finset.insert_Ico_add_one_left_eq_Ico hnext).symm
    have hnot : t.val + 1 ∉ Finset.Ico (t.val + 2) p.T := by
      simp
    have hnextTerm :
        f (t.val + 1) =
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
            (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
              rate rewards C_star C_h u t hnext) := by
      dsimp [f]
      rw [dite_eq_left hnext]
      exact congrArg (fun g : Set (ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource rate rewards C_star C_h u t) => (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real g)
        (postGate_eq_next rate rewards C_star C_h u t ⟨t.val + 1, hnext⟩ rfl)
    have hfutureSum :
        (∑ n ∈ Finset.Ico (t.val + 2) p.T, f n) =
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t := by
      unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates
      apply Finset.sum_congr rfl
      intro n hn
      have hnt := Finset.mem_Ico.mp hn
      have hlt : n < p.T := hnt.2
      have hfuture : t.val + 1 < n := by omega
      dsimp [f]
      rw [dite_eq_left hlt]
      rw [postGate_eq_future rate rewards C_star C_h u t ⟨n, hlt⟩ hfuture]
      simp only [ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMassAt,
        dite_eq_left hlt, dite_eq_left hfuture]
    rw [hsum, ← hsplit, hprefix, zero_add, hinterval,
      Finset.sum_insert hnot, hnextTerm, hfutureSum]
    simp [hnext]
  · have hlast : t.val + 1 = p.T := by omega
    have hzero :
        ∀ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q) = 0 := by
      intro q
      have hqle : q.val ≤ t.val := by omega
      rw [postGate_eq_empty_of_le rate rewards C_star C_h u t q hqle]
      simp
    have hfutureEmpty :
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
          rate rewards C_star C_h u t = 0 := by
      unfold ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
        ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureCalendarDates
      have hempty : Finset.Ico (t.val + 2) p.T = ∅ := by
        ext n
        simp only [Finset.mem_Ico, Finset.notMem_empty, iff_false]
        omega
      simp [hempty]
    simp [hzero, hnext, hfutureEmpty]

/-- Summing the sharp joint datewise occupancy result once over the physical
horizon charges the actual retained first call and the actual after-call
gates, with one shared horizon. -/
theorem sum_sourceDateMass_le_horizon (control0 : TimeControl p) :
    (∑ q : Fin p.T,
      (ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
          rate rewards C_star C_h q control0 + (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q))) +
      (sourceInputLaw p).real
        (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
          rate rewards C_star C_h) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ((if hnext : t.val + 1 < p.T then
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
              (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                rate rewards C_star C_h u t hnext)
          else 0) +
          ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
            rate rewards C_star C_h u t)) ≤ (p.T : ℝ) := by
  let A : Fin p.T → ℝ := fun q =>
    ReferenceFirstCollectionPrecallFirstCallMassBudget.sourceCellMass
      rate rewards C_star C_h q control0 + (sourceInputLaw p).real (ReferenceFirstCollectionOldCalendarExponentialStep.G rate rewards C_star C_h q)
  let C : Fin p.T → ℝ := fun q => ∑ u : Fin p.T, (sourceInputLaw p).real (ReferenceFirstCollectionCurrentRetainedGate.G rate rewards C_star C_h u q)
  let G : Fin p.T → ℝ := fun q => ∑ u : Fin p.T, ∑ t : Fin p.T,
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q)
  have hdate (q : Fin p.T) : (A q + C q) + G q ≤ 1 := by
    simpa only [A, C, G, add_assoc] using
      sourceDateMass_le_one rate rewards C_star C_h control0 q
  have hsum :
      (∑ q : Fin p.T, ((A q + C q) + G q)) ≤
        ∑ _q : Fin p.T, (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro q _
    exact hdate q
  have hsplit :
      (∑ q : Fin p.T, ((A q + C q) + G q)) =
        (∑ q : Fin p.T, A q) + (∑ q : Fin p.T, C q) +
          (∑ q : Fin p.T, G q) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcurrent :
      (∑ q : Fin p.T, C q) =
        (sourceInputLaw p).real
          (ReferenceFirstCollectionActualCallExponentialQueueEstimate.retainedFirstCall
            rate rewards C_star C_h) := by
    dsimp [C]
    rw [Finset.sum_comm]
    exact ReferenceFirstCollectionActualCallExponentialQueueEstimate.sum_retainedGate_measures_eq_retainedFirstCall_measure
      rate rewards C_star C_h control0
  have hafter :
      (∑ q : Fin p.T, G q) =
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ((if hnext : t.val + 1 < p.T then
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real
                (ReferenceFirstCollectionRenewalNextDateExponentialStep.retainedNextDate
                  rate rewards C_star C_h u t hnext)
            else 0) +
            ReferenceFirstCollectionRenewalSupportedFutureWeightedBudget.futureGateMass
              rate rewards C_star C_h u t) := by
    dsimp [G]
    calc
      _ = ∑ u : Fin p.T, ∑ q : Fin p.T, ∑ t : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q) := by
        rw [Finset.sum_comm]
      _ = ∑ u : Fin p.T, ∑ t : Fin p.T, ∑ q : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw rate rewards C_star C_h u t).real (postGate rate rewards C_star C_h u t q) := by
        apply Finset.sum_congr rfl
        intro u _
        exact Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro t _
        exact postGateMass_sum_eq rate rewards C_star C_h u t
  calc
    _ = (∑ q : Fin p.T, A q) + (∑ q : Fin p.T, C q) +
          (∑ q : Fin p.T, G q) := by
      rw [← hcurrent, ← hafter]
    _ ≤ (p.T : ℝ) := by
      rw [← hsplit]
      calc
        (∑ q : Fin p.T, ((A q + C q) + G q)) ≤
            ∑ _q : Fin p.T, (1 : ℝ) := hsum
        _ = (p.T : ℝ) := by simp

end Bandits.Support.ReferenceFirstCollectionRenewalOriginalCalendarMassBudget

end
