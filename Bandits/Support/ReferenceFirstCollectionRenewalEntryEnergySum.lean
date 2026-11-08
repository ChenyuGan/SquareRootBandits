/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergyBridge

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic


/-!
# Original-source first-call renewal entry energy sum

This module sums the actual entry energy over the finite first-call renewal
cells. Each cell law is the unnormalized restriction of the original physical
source law. The only extra mass is the immediate next-date retained gate, and
the literal finite union of those gates is charged once.

The event definitions retain the original call selector, cutoff, date, and
next-date branch, including null cells and the terminal date. The entry energy
is inherited from the original numerical prefix; this module does not reset
the backlog or identify entry energy with the pre-update energy.

Sources: `04_slow_fast_learner.tex:140-188,245-290`,
`06_interruptions.tex:355-426`, and `05_binary_transport.tex:352-431` in
the pinned ZIP4 manuscript.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open Bandits.Support
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)
open scoped Classical MeasureTheory
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalNextDateExponentialStep (Source expBacklogAfter expBacklogBefore measurableSet_retainedNextDate_ambient retainedNextDate setIntegral_expBacklogAfter_le)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalEndpointExponentialMoment (entryEnergy integrable_entryEnergy)
open _root_.Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergyBridge (entryEnergy_eq_expBacklogAfter entryEnergy_eq_expBacklogBefore_of_terminal expBacklogBefore_eq_callXPlus)
open _root_.Bandits.Support.ReferenceFirstCollectionActualCallExponentialQueueEstimate (callXMinus callXPlus callXPlus_integrable integral_callXPlus_le_integral_callXMinus_add_retainedFirstCall_measure retainedFirstCall)

namespace Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergySum

variable {p : ConstructorDimensions.Parameters}
variable (rate : ReferenceActivePhysicalStep.RateInput p)
  (rewards : GridRewardTable p) (C_star C_h : ℝ)
  (control0 : TimeControl p) (a : Fin p.K)

local notation "S" => SourceInput p
local notation "μ" => sourceInputLaw p

local instance sourceInputMeasurableSpace : MeasurableSpace (SourceInput p) := by
  change MeasurableSpace
    (CompletePublicTable.PublishedOutput p ×
      BootstrapPrivateRoundStreams.ExtendedPrivateCoordinates p)
  infer_instance

/-- The original first-call renewal cells, as one finite union in the
original source space. -/
def renewalCallEventUnion : Set S :=
  ⋃ cell : Fin p.T × Fin p.T,
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h cell.1 cell.2

/-- The exact finite type of calendar dates with an actual successor date. -/
def NextDate (p : ConstructorDimensions.Parameters) :=
  {t : Fin p.T // t.val + 1 < p.T}

local instance nextDateFintype (p : ConstructorDimensions.Parameters) :
    Fintype (NextDate p) := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter fun t : Fin p.T => t.val + 1 < p.T)
    (by intro t; simp)

/-- The original-source image of each literal immediate next-date gate,
indexed by its same renewal cutoff and calendar date. -/
def retainedNextDateUnion : Set S :=
  ⋃ cell : Fin p.T × NextDate p,
    (Subtype.val :
      (Source
        rate rewards C_star C_h cell.1 cell.2.1) → S) ''
      (retainedNextDate
        rate rewards C_star C_h cell.1 cell.2.1 cell.2.2)

/-- The exact unnormalized total mass of all immediate retained next-date
gates, with their original renewal-cell laws. -/
def retainedNextDateMass : ℝ :=
  ∑ u : Fin p.T, ∑ t : NextDate p,
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t.1).real
      (retainedNextDate
        rate rewards C_star C_h u t.1 t.2)

/-- Every original renewal event is contained in the matching literal
first-collection call cell. -/
theorem renewalCallEvent_subset_firstCell (u t : Fin p.T) :
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h u t ⊆
    ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
  intro z hz
  change z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t ∧ _ at hz
  change z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t
  simpa only [ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell,
    ReferenceCalendarCollectionCallControlLaw.firstCell] using hz.1

/-- The first-call projection supplies disjointness internally: one source
has only one pair returned by the same original `firstCollectionCall`. -/
private theorem renewalCallEvents_disjoint
    (cell₁ cell₂ : Fin p.T × Fin p.T) (hne : cell₁ ≠ cell₂) :
    Disjoint
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h cell₁.1 cell₁.2)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h cell₂.1 cell₂.2) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have hfirst₁ := renewalCallEvent_subset_firstCell
    rate rewards C_star C_h cell₁.1 cell₁.2 hz₁
  have hfirst₂ := renewalCallEvent_subset_firstCell
    rate rewards C_star C_h cell₂.1 cell₂.2 hz₂
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) =
        some (cell₁.1, cell₁.2) at hfirst₁
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) =
        some (cell₂.1, cell₂.2) at hfirst₂
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at hfirst₁
  | some call =>
      simp only [hcall, Option.map_some, Option.some.injEq] at hfirst₁ hfirst₂
      have hp : (cell₁.1, cell₁.2) = (cell₂.1, cell₂.2) :=
        hfirst₁.symm.trans hfirst₂
      exact hne (Prod.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp))

/-- The literal renewal union is Borel in the original physical source. -/
theorem measurableSet_renewalCallEventUnion :
    MeasurableSet (renewalCallEventUnion rate rewards C_star C_h) := by
  classical
  apply MeasurableSet.iUnion
  intro cell
  exact ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
    rate rewards C_star C_h cell.1 cell.2

/-- The literal source images of all retained next-date gates are Borel. -/
theorem measurableSet_retainedNextDateUnion (control0 : TimeControl p) :
    MeasurableSet (retainedNextDateUnion rate rewards C_star C_h) := by
  classical
  apply MeasurableSet.iUnion
  intro cell
  have hcell :=
    ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h cell.1 cell.2.1
  have hgate :=
    measurableSet_retainedNextDate_ambient
      rate rewards C_star C_h cell.1 cell.2.1 control0 cell.2.2
  exact (MeasurableEmbedding.subtype_coe hcell).measurableSet_image' hgate

/-- Each gate image stays inside the original renewal cell used to form it. -/
private theorem retainedGateImage_subset_renewalCallEvent
    (cell : Fin p.T × NextDate p) :
    (Subtype.val :
      (Source
        rate rewards C_star C_h cell.1 cell.2.1) → S) ''
      (retainedNextDate
        rate rewards C_star C_h cell.1 cell.2.1 cell.2.2) ⊆
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h cell.1 cell.2.1 := by
  rintro x ⟨z, hz, rfl⟩
  exact z.property

/-- The gate images inherit pairwise disjointness from the very same first
call projection, even when one or both cells have zero mass. -/
private theorem retainedGateImages_disjoint
    (cell₁ cell₂ : Fin p.T × NextDate p) (hne : cell₁ ≠ cell₂) :
    Disjoint
      ((Subtype.val :
        (Source
          rate rewards C_star C_h cell₁.1 cell₁.2.1) → S) ''
        (retainedNextDate
          rate rewards C_star C_h cell₁.1 cell₁.2.1 cell₁.2.2))
      ((Subtype.val :
        (Source
          rate rewards C_star C_h cell₂.1 cell₂.2.1) → S) ''
        (retainedNextDate
          rate rewards C_star C_h cell₂.1 cell₂.2.1 cell₂.2.2)) := by
  apply Set.disjoint_left.mpr
  intro x hx₁ hx₂
  rcases hx₁ with ⟨z₁, _hz₁, hx₁⟩
  rcases hx₂ with ⟨z₂, _hz₂, hx₂⟩
  have hval : z₁.val = z₂.val := hx₁.trans hx₂.symm
  have hpair := renewalCallEvents_disjoint
    rate rewards C_star C_h (cell₁.1, cell₁.2.1) (cell₂.1, cell₂.2.1)
    (by
      intro heq
      have hcut : cell₁.1 = cell₂.1 :=
        congrArg (fun x : Fin p.T × Fin p.T => x.1) heq
      have hdate : cell₁.2 = cell₂.2 :=
        Subtype.ext (congrArg (fun x : Fin p.T × Fin p.T => x.2) heq)
      exact hne (Prod.ext hcut hdate))
  have h₁ : z₁.val ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h cell₁.1 cell₁.2.1 := z₁.property
  have h₂ : z₂.val ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h cell₂.1 cell₂.2.1 := z₂.property
  have h₂' : z₁.val ∈
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h cell₂.1 cell₂.2.1 := by
    rw [hval]
    exact h₂
  exact (Set.disjoint_left.mp hpair) h₁ h₂'

/-- Every entry energy has its existing finite-source integrability proof,
with no incoming-envelope premise. -/
theorem integrable_entryEnergy_all
    (u t : Fin p.T) (a : Fin p.K) (control0 : TimeControl p) :
    Integrable
      (entryEnergy
        rate rewards C_star C_h u t a)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t) := by
  exact integrable_entryEnergy rate rewards C_star C_h u t a control0

/-- Transport one original-source cell integral through its exact subtype
law. The pointwise scalar equality comes from the accepted entry bridge. -/
private theorem expBacklogBefore_integral_eq_cellCallXPlus
    (u t : Fin p.T) :
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
      expBacklogBefore
        rate rewards C_star C_h u t a z ∂
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t) =
    ∫ z in ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t,
      callXPlus
        rate rewards C_star C_h a z ∂μ := by
  calc
    _ = (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
        callXPlus
          rate rewards C_star C_h a z.val ∂
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact expBacklogBefore_eq_callXPlus
        rate rewards C_star C_h u t a z
    _ = ∫ z in ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t,
        callXPlus
          rate rewards C_star C_h a z ∂μ := by
      rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw]
      exact integral_subtype_comap
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
          rate rewards C_star C_h u t) _

/-- The full sum of incoming exponentials is the original-source call sum
restricted to the literal finite renewal union. -/
theorem sum_expBacklogBefore_eq_callXPlus_on_renewalUnion
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
        expBacklogBefore
          rate rewards C_star C_h u t a z ∂
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) =
    ∫ z in renewalCallEventUnion rate rewards C_star C_h,
      callXPlus
        rate rewards C_star C_h a z ∂μ := by
  classical
  have hcell_meas (cell : Fin p.T × Fin p.T) :
      MeasurableSet
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h cell.1 cell.2) :=
    ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h cell.1 cell.2
  have hcell_disj : Pairwise (fun cell₁ cell₂ : Fin p.T × Fin p.T =>
      Disjoint
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h cell₁.1 cell₁.2)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h cell₂.1 cell₂.2)) := by
    intro cell₁ cell₂ hne
    exact renewalCallEvents_disjoint rate rewards C_star C_h cell₁ cell₂ hne
  have hplus_int : Integrable
      (callXPlus
        rate rewards C_star C_h a) μ :=
    callXPlus_integrable
      rate rewards C_star C_h control0 a
  have hcell_int (cell : Fin p.T × Fin p.T) :
      IntegrableOn
        (callXPlus
          rate rewards C_star C_h a)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h cell.1 cell.2) μ :=
    hplus_int.integrableOn
  calc
    _ = ∑ cell : Fin p.T × Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h cell.1 cell.2,
          expBacklogBefore
            rate rewards C_star C_h cell.1 cell.2 a z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h cell.1 cell.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ cell : Fin p.T × Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
            rate rewards C_star C_h cell.1 cell.2,
          callXPlus
            rate rewards C_star C_h a z ∂μ := by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact expBacklogBefore_integral_eq_cellCallXPlus
        rate rewards C_star C_h a cell.1 cell.2
    _ = ∫ z in renewalCallEventUnion rate rewards C_star C_h,
          callXPlus
            rate rewards C_star C_h a z ∂μ := by
      simpa only [renewalCallEventUnion] using
        (integral_iUnion_fintype hcell_meas hcell_disj hcell_int).symm

/-- Under the literal subtype inclusion, a gate mass is exactly the mass of
its original-source image; no normalization or cell division occurs. -/
private theorem retainedGateMass_eq_sourceImage
    (u : Fin p.T) (t : NextDate p) :
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
      rate rewards C_star C_h u t.1).real
      (retainedNextDate
        rate rewards C_star C_h u t.1 t.2) =
    (μ).real ((Subtype.val :
      (Source
        rate rewards C_star C_h u t.1) → S) ''
      (retainedNextDate
        rate rewards C_star C_h u t.1 t.2)) := by
  change ENNReal.toReal
      ((ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t.1)
        (retainedNextDate
          rate rewards C_star C_h u t.1 t.2)) =
    ENNReal.toReal (μ ((Subtype.val :
      (Source
        rate rewards C_star C_h u t.1) → S) ''
      (retainedNextDate
        rate rewards C_star C_h u t.1 t.2)))
  apply congrArg ENNReal.toReal
  rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw]
  exact comap_subtype_coe_apply
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t.1) μ _

/-- The source images of distinct next-date gate cells are disjoint because
each image lies in its matching first-call cell. -/
private theorem retainedNextDateImages_pairwiseDisjoint :
    Pairwise (fun cell₁ cell₂ : Fin p.T × NextDate p =>
      Disjoint
      ((Subtype.val :
        (Source
          rate rewards C_star C_h cell₁.1 cell₁.2.1) → S) ''
        (retainedNextDate
          rate rewards C_star C_h cell₁.1 cell₁.2.1 cell₁.2.2))
      ((Subtype.val :
        (Source
          rate rewards C_star C_h cell₂.1 cell₂.2.1) → S) ''
        (retainedNextDate
          rate rewards C_star C_h cell₂.1 cell₂.2.1 cell₂.2.2))) := by
  intro cell₁ cell₂ hne
  exact retainedGateImages_disjoint
    rate rewards C_star C_h cell₁ cell₂ hne

/-- Additivity of the actual retained-gate images gives the exact mass
identity for the displayed literal union. -/
theorem retainedNextDateMass_eq_sourceUnion
    (control0 : TimeControl p) :
    retainedNextDateMass rate rewards C_star C_h =
      (μ).real (retainedNextDateUnion rate rewards C_star C_h) := by
  classical
  have himage_meas (cell : Fin p.T × NextDate p) :
      MeasurableSet
        ((Subtype.val :
          (Source
            rate rewards C_star C_h cell.1 cell.2.1) → S) ''
          (retainedNextDate
            rate rewards C_star C_h cell.1 cell.2.1 cell.2.2)) := by
    have hcell :=
      ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h cell.1 cell.2.1
    have hgate :=
      measurableSet_retainedNextDate_ambient
        rate rewards C_star C_h cell.1 cell.2.1 control0 cell.2.2
    exact (MeasurableEmbedding.subtype_coe hcell).measurableSet_image' hgate
  have hdisj := retainedNextDateImages_pairwiseDisjoint
    rate rewards C_star C_h
  calc
    retainedNextDateMass rate rewards C_star C_h =
        ∑ cell : Fin p.T × NextDate p,
          (μ).real ((Subtype.val :
            (Source
              rate rewards C_star C_h cell.1 cell.2.1) → S) ''
            (retainedNextDate
              rate rewards C_star C_h cell.1 cell.2.1 cell.2.2)) := by
      simp only [retainedNextDateMass]
      rw [← Finset.sum_product']
      apply Finset.sum_congr rfl
      intro cell hcell
      exact (retainedGateMass_eq_sourceImage
        rate rewards C_star C_h cell.1 cell.2)
    _ = (μ).real (⋃ cell : Fin p.T × NextDate p,
          (Subtype.val :
            (Source
              rate rewards C_star C_h cell.1 cell.2.1) → S) ''
            (retainedNextDate
              rate rewards C_star C_h cell.1 cell.2.1 cell.2.2)) := by
      exact (measureReal_iUnion_fintype
        hdisj himage_meas).symm
    _ = (μ).real (retainedNextDateUnion rate rewards C_star C_h) := rfl

/-- The retained next-date union is contained in the original finite union
of renewal cells, because every point in an image is an original source. -/
private theorem retainedNextDateUnion_subset_renewalCallEventUnion :
    retainedNextDateUnion rate rewards C_star C_h ⊆
      renewalCallEventUnion rate rewards C_star C_h := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨cell, hcell⟩
  rcases hcell with ⟨z, hz, rfl⟩
  apply Set.mem_iUnion.mpr
  exact ⟨(cell.1, cell.2.1), z.property⟩

/-- Exact next-date gate mass, then its original-event and probability
bounds. Null cells are retained as zero terms in the finite sums. -/
theorem retainedNextDateMass_bound
    (control0 : TimeControl p) :
    retainedNextDateMass rate rewards C_star C_h =
        (μ).real (retainedNextDateUnion rate rewards C_star C_h) ∧
      (μ).real (retainedNextDateUnion rate rewards C_star C_h) ≤
        (μ).real (renewalCallEventUnion rate rewards C_star C_h) ∧
      (μ).real (renewalCallEventUnion rate rewards C_star C_h) ≤ 1 := by
  refine ⟨retainedNextDateMass_eq_sourceUnion rate rewards C_star C_h control0,
    ?_, ?_⟩
  · exact measureReal_mono
      (retainedNextDateUnion_subset_renewalCallEventUnion
        rate rewards C_star C_h)
  · calc
      (μ).real (renewalCallEventUnion rate rewards C_star C_h) ≤ (μ).real Set.univ :=
        measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp

/-- The gate mass over all ordinary calendar dates is the sum over precisely
the subtype `NextDate`; the terminal date contributes zero. -/
private theorem sum_nextGateMass_eq_retainedNextDateMass :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      (if hq : t.val + 1 < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (retainedNextDate
            rate rewards C_star C_h u t hq)
       else 0)) = retainedNextDateMass rate rewards C_star C_h := by
  classical
  unfold retainedNextDateMass
  apply Finset.sum_congr rfl
  intro u hu
  let P : Fin p.T → Prop := fun t => t.val + 1 < p.T
  let g : Fin p.T → ℝ := fun t =>
    if hq : P t then
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t).real
        (retainedNextDate
          rate rewards C_star C_h u t hq)
    else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype P g
  calc
    (∑ t : Fin p.T,
      (if hq : t.val + 1 < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (retainedNextDate
            rate rewards C_star C_h u t hq)
       else 0)) =
        (∑ t : {t : Fin p.T // P t}, g t) +
          ∑ t : {t : Fin p.T // ¬ P t}, g t := by
      exact hsplit.symm
    _ = ∑ t : NextDate p,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t.1).real
          (retainedNextDate
            rate rewards C_star C_h u t.1 t.2) := by
      have hzero : (∑ t : {t : Fin p.T // ¬ P t}, g t) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        simp [g, P, t.property]
      rw [hzero, add_zero]
      change (∑ t : {t : Fin p.T // P t}, g t) =
        ∑ t : {t : Fin p.T // P t},
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t.1).real
            (retainedNextDate rate rewards C_star C_h u t.1 t.2)
      apply Finset.sum_congr rfl
      intro t ht
      have htP : P t.1 := t.2
      simp [g, htP]

/-- On every next-date branch, the entry exponential is the actual
post-update exponential on the same original renewal source. -/
private theorem entryEnergy_eq_after_on_nextDate
    (u t : Fin p.T) (hq : t.val + 1 < p.T)
    (z : ReferenceFirstCollectionRenewalFutureControlLaw.Source
      rate rewards C_star C_h u t) :
    entryEnergy
      rate rewards C_star C_h u t a z =
    expBacklogAfter
      rate rewards C_star C_h u t hq a z :=
  entryEnergy_eq_expBacklogAfter
    rate rewards C_star C_h u t hq a z

/-- At the terminal date, the entry exponential is exactly the incoming
exponential. No successor action or fabricated `Fin p.T` date is used. -/
private theorem entryEnergy_eq_before_at_terminal
    (u t : Fin p.T) (ht : t.val + 1 = p.T)
    (z : ReferenceFirstCollectionRenewalFutureControlLaw.Source
      rate rewards C_star C_h u t) :
    entryEnergy
      rate rewards C_star C_h u t a z =
    expBacklogBefore
      rate rewards C_star C_h u t a z :=
  entryEnergy_eq_expBacklogBefore_of_terminal
      rate rewards C_star C_h u t ht a z

/-- Cellwise entry-energy integration pays the next-date gate exactly once;
the terminal branch pays no gate mass. -/
private theorem entryEnergy_integral_le_before_add_nextGate
    (control0 : TimeControl p) (a : Fin p.K) (u t : Fin p.T) :
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
      entryEnergy
        rate rewards C_star C_h u t a z ∂
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t) ≤
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
      expBacklogBefore
        rate rewards C_star C_h u t a z ∂
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t) +
      (if hq : t.val + 1 < p.T then
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real
          (retainedNextDate
            rate rewards C_star C_h u t hq)
       else 0) := by
  by_cases hq : t.val + 1 < p.T
  · have hentry :
        (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t =>
          entryEnergy
            rate rewards C_star C_h u t a z) =ᵐ[
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t]
        (fun z => expBacklogAfter
          rate rewards C_star C_h u t hq a z) := by
      filter_upwards [] with z
      exact entryEnergy_eq_after_on_nextDate
        rate rewards C_star C_h a u t hq z
    rw [integral_congr_ae hentry]
    have hstep :=
      setIntegral_expBacklogAfter_le
        rate rewards C_star C_h u t control0 hq a
        (H := Set.univ) MeasurableSet.univ
    simpa only [setIntegral_univ, Set.univ_inter, dite_eq_left hq] using hstep
  · have ht : t.val + 1 = p.T := by
      have htlt := t.isLt
      omega
    have hentry :
        (fun z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t =>
          entryEnergy
            rate rewards C_star C_h u t a z) =ᵐ[
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t]
        (fun z => expBacklogBefore
          rate rewards C_star C_h u t a z) := by
      filter_upwards [] with z
      exact entryEnergy_eq_before_at_terminal
        rate rewards C_star C_h a u t ht z
    rw [integral_congr_ae hentry]
    simp [hq]

/-- Summing cellwise entry energies gives the restricted original-call
integral plus the exact total retained next-date mass. -/
theorem sum_entryEnergy_le_callXPlus_on_renewalUnion_add_nextDateMass
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
        entryEnergy
          rate rewards C_star C_h u t a z ∂
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) ≤
    (∫ z in renewalCallEventUnion rate rewards C_star C_h,
      callXPlus
        rate rewards C_star C_h a z ∂μ) +
      retainedNextDateMass rate rewards C_star C_h := by
  calc
    _ ≤ (∑ u : Fin p.T, ∑ t : Fin p.T,
          ((∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
              rate rewards C_star C_h u t,
            expBacklogBefore
              rate rewards C_star C_h u t a z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t) +
            (if hq : t.val + 1 < p.T then
              (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t).real
                (retainedNextDate
                  rate rewards C_star C_h u t hq)
             else 0))) := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro t ht
      exact entryEnergy_integral_le_before_add_nextGate
        rate rewards C_star C_h control0 a u t
    _ = (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
              rate rewards C_star C_h u t,
            expBacklogBefore
              rate rewards C_star C_h u t a z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t) +
        retainedNextDateMass rate rewards C_star C_h := by
      simp only [Finset.sum_add_distrib]
      rw [sum_nextGateMass_eq_retainedNextDateMass rate rewards C_star C_h]
    _ = (∫ z in renewalCallEventUnion rate rewards C_star C_h,
          callXPlus
            rate rewards C_star C_h a z ∂μ) +
        retainedNextDateMass rate rewards C_star C_h := by
      rw [sum_expBacklogBefore_eq_callXPlus_on_renewalUnion
        rate rewards C_star C_h a control0]

/-- Removing the event restriction is licensed by nonnegativity of the
literal post-update exponential call sum. -/
private theorem callXPlus_nonneg (z : S) :
    0 ≤ callXPlus
      rate rewards C_star C_h a z := by
  unfold callXPlus
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  exact ReferenceFirstCollectionCurrentExponentialQueueStep.XPlus_bounds
    rate rewards C_star C_h u t a z |>.1

/-- The entry sum is bounded by the full original-source post-update call
integral plus the same single next-date gate mass. -/
theorem sum_entryEnergy_le_callXPlus_integral_add_nextDateMass
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
        entryEnergy
          rate rewards C_star C_h u t a z ∂
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) ≤
    (∫ z : S,
      callXPlus
        rate rewards C_star C_h a z ∂μ) +
      retainedNextDateMass rate rewards C_star C_h := by
  calc
    _ ≤ (∫ z in renewalCallEventUnion rate rewards C_star C_h,
          callXPlus
            rate rewards C_star C_h a z ∂μ) +
        retainedNextDateMass rate rewards C_star C_h :=
      sum_entryEnergy_le_callXPlus_on_renewalUnion_add_nextDateMass
        rate rewards C_star C_h a control0
    _ ≤ (∫ z : S,
          callXPlus
            rate rewards C_star C_h a z ∂μ) +
        retainedNextDateMass rate rewards C_star C_h := by
      have hmono :
          (∫ z in renewalCallEventUnion rate rewards C_star C_h,
            callXPlus
              rate rewards C_star C_h a z ∂μ) ≤
          (∫ z : S,
            callXPlus
              rate rewards C_star C_h a z ∂μ) := by
        apply setIntegral_le_integral
        · exact callXPlus_integrable rate rewards C_star C_h control0 a
        · filter_upwards [] with z
          exact callXPlus_nonneg rate rewards C_star C_h a z
      linarith

/-- Named consumer: the original-source first-call renewal overflow-slice
integration bound. It retains the sharp incoming-call estimate and adds the
literal next-date gate union once. -/
theorem firstCollectionRenewalOverflowSliceEntryEnergyBound
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
        entryEnergy
          rate rewards C_star C_h u t a z ∂
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) ≤
    (∫ z : S,
      callXMinus
        rate rewards C_star C_h a z ∂μ) +
      (μ).real (retainedFirstCall
        rate rewards C_star C_h) +
      (μ).real (retainedNextDateUnion rate rewards C_star C_h) := by
  calc
    _ ≤ (∫ z : S,
          callXPlus
            rate rewards C_star C_h a z ∂μ) +
        retainedNextDateMass rate rewards C_star C_h :=
      sum_entryEnergy_le_callXPlus_integral_add_nextDateMass
        rate rewards C_star C_h a control0
    _ ≤ (∫ z : S,
          callXMinus
            rate rewards C_star C_h a z ∂μ) +
        (μ).real (retainedFirstCall
          rate rewards C_star C_h) +
        (μ).real (retainedNextDateUnion rate rewards C_star C_h) := by
      have hcall :=
        integral_callXPlus_le_integral_callXMinus_add_retainedFirstCall_measure
          rate rewards C_star C_h control0 a
      have hmass := retainedNextDateMass_eq_sourceUnion
        rate rewards C_star C_h control0
      rw [hmass]
      linarith

end Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergySum

end
