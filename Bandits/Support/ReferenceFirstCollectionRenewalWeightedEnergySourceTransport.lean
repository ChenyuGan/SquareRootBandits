/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift
public import Bandits.Support.ReferenceFirstCollectionActualCallWeightedEnergy
public import Bandits.Support.ReferenceFirstCollectionRenewalEntryEnergyBridge
public import Bandits.Support.ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Original-source transport of first-renewal quadratic energy

On each actual first-call renewal slice, the incoming energy, the energy after
the same whole-cell update, and the retained incoming backlog agree with the
corresponding original-source first-call observations. The finite disjoint
union transports their exact sums to one restriction of the original source
law. Incoming energy is at the pre-call boundary; whole-post energy is after
the first-call update and remains the outgoing boundary for later accounting.
These equalities identify two views of the same call and do not add the
whole-call cost a second time. The union covers only first-call renewal slices;
it makes no coverage claim about later assignments.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceFirstCollectionRenewalWeightedEnergySourceTransport

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

/-- The finite union of the actual first-call renewal cells in the original
source space. -/
def renewalCallEventUnion : Set S :=
  {z | ∃ u t : Fin p.T, z ∈
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h u t}

/-- Each renewal cell is Borel in the original source. -/
theorem measurableSet_renewalCallEvent (u t : Fin p.T) :
    MeasurableSet
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t) :=
  ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
    rate rewards C_star C_h u t

/-- The event union is Borel. -/
theorem measurableSet_renewalCallEventUnion :
    MeasurableSet (renewalCallEventUnion rate rewards C_star C_h) := by
  classical
  rw [show renewalCallEventUnion rate rewards C_star C_h =
      ⋃ u : Fin p.T, ⋃ t : Fin p.T,
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t by
    ext z
    simp [renewalCallEventUnion]]
  apply MeasurableSet.iUnion
  intro u
  apply MeasurableSet.iUnion
  intro t
  exact measurableSet_renewalCallEvent rate rewards C_star C_h u t

/-- Every source in the transported union has an actual original first-call
selector value, with the same cutoff and date as its renewal cell. -/
theorem renewalCallEventUnion_mem_firstCollectionCall (z : S)
    (hz : z ∈ renewalCallEventUnion rate rewards C_star C_h) :
    ∃ u t : Fin p.T, ∃ theta : ReferenceFirstCollectionRenewalAuxiliaryLaw.Theta p,
      ReferenceFirstCollectionSamplerCall.firstCollectionCall
        rate rewards C_star C_h z = some (u, (t, theta)) := by
  rcases hz with ⟨u, t, hz⟩
  have hcell : z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
      rate rewards C_star C_h u t := hz.1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u, t)
    at hcell
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at hcell
  | some call =>
      simp only [hcall, Option.map_some, Option.some.injEq] at hcell
      rcases call with ⟨u', t', theta⟩
      have hu : u' = u := congrArg Prod.fst hcell
      have ht : t' = t := congrArg Prod.snd hcell
      subst u'
      subst t'
      exact ⟨u, t, theta, rfl⟩

/-- A source belongs to at most one actual renewal cell, by the single
first-call selector already carried by the cell definition. -/
theorem renewalCallEvents_disjoint (u₁ t₁ u₂ t₂ : Fin p.T)
    (hne : (u₁, t₁) ≠ (u₂, t₂)) :
    Disjoint
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u₁ t₁)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u₂ t₂) := by
  apply Set.disjoint_left.mpr
  intro z hz₁ hz₂
  have hfirst₁ : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₁ t₁ := by
    change z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u₁ t₁ ∧ _ at hz₁
    simpa only [ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell,
      ReferenceCalendarCollectionCallControlLaw.firstCell] using hz₁.1
  have hfirst₂ : z ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u₂ t₂ := by
    change z ∈ ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell
        rate rewards C_star C_h u₂ t₂ ∧ _ at hz₂
    simpa only [ReferenceFirstCollectionAuxiliarySeeds.actualCollectionCallCell,
      ReferenceCalendarCollectionCallControlLaw.firstCell] using hz₂.1
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₁, t₁) at hfirst₁
  change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z).map (fun c => (c.1, c.2.1)) = some (u₂, t₂) at hfirst₂
  cases hcall : ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z with
  | none => simp [hcall] at hfirst₁
  | some call =>
      simp only [hcall, Option.map_some, Option.some.injEq] at hfirst₁ hfirst₂
      apply hne
      exact Prod.ext (congrArg Prod.fst (hfirst₁.symm.trans hfirst₂))
        (congrArg Prod.snd (hfirst₁.symm.trans hfirst₂))

private theorem renewalCallEvents_pairwiseDisjoint :
    Pairwise (fun a b : Fin p.T × Fin p.T =>
      Disjoint
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h a.1 a.2)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h b.1 b.2)) := by
  intro a b hab
  exact renewalCallEvents_disjoint rate rewards C_star C_h a.1 a.2 b.1 b.2 hab

/-- The three local observations inherit integrability from the accepted
whole-source APIs. The retained backlog keeps its literal no-overflow gate. -/
theorem renewalSource_integrable_observations (control0 : TimeControl p)
    (u t : Fin p.T) :
    Integrable
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
          rate rewards C_star C_h u t)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) ∧
    Integrable
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) ∧
    Integrable
        ((ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
          rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
            rate rewards C_star C_h u t))
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) := by
  exact ⟨
    ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.integrable_Vminus
      rate rewards C_star C_h u t control0,
    ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.integrable_VwholePlus
      rate rewards C_star C_h u t control0,
    (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.integrable_Bminus
      rate rewards C_star C_h u t control0).indicator
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.measurableSet_E
          rate rewards C_star C_h u t)⟩

/-- On an actual renewal slice, the whole-source queue energies are the same
incoming and same-update energies read by the original first-call module. -/
theorem wholeEnergyObservations_eq_callObservations
    (u t : Fin p.T)
    (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t) :
    ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
        rate rewards C_star C_h u t z =
        ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
          rate rewards C_star C_h z.val ∧
    ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
        rate rewards C_star C_h u t z =
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z.val ∧
    (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
        rate rewards C_star C_h u t).indicator
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
          rate rewards C_star C_h u t) z =
      ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
        rate rewards C_star C_h z.val := by
  let theta := ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallParameter
    rate rewards C_star C_h u t z
  have hcall := ReferenceFirstCollectionRenewalAuxiliaryLaw.firstCollectionCall_eq
    rate rewards C_star C_h u t z
  have hfirst : z.val ∈ ReferenceCalendarCollectionCallControlLaw.firstCell
      rate rewards C_star C_h u t := by
    change (ReferenceFirstCollectionSamplerCall.firstCollectionCall
      rate rewards C_star C_h z.val).map (fun c => (c.1, c.2.1)) = some (u, t)
    rw [hcall]
    rfl
  obtain ⟨L, c, hpast, hcurrent, henabled, hbefore, hafter,
      hthetaMinus, hthetaPlus, hminus, hplus, hcallBacklog⟩ :=
    ReferenceFirstCollectionActualCallWeightedEnergy.callEnergy_actual_run_readouts_of_firstCollectionCall
      rate rewards C_star C_h z.val u t theta hcall
  have hpastBridge :=
    ReferenceFirstCollectionRenewalEntryEnergyBridge.pastCells_eq_original
      rate rewards C_star C_h u t z
  have hcurrentBridge :=
    ReferenceFirstCollectionRenewalEntryEnergyBridge.currentCell_eq_original
      rate rewards C_star C_h u t z
  have hafterBridge :=
    ReferenceFirstCollectionRenewalEntryEnergyBridge.after_eq_wholePostReadout
      rate rewards C_star C_h u t z
  have hL : L =
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
        rate rewards C_star C_h u t z :=
    Option.some.inj (hpast.symm.trans hpastBridge)
  have hc : c =
      ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
        rate rewards C_star C_h u t z :=
    Option.some.inj (hcurrent.symm.trans hcurrentBridge)
  subst L
  subst c
  have hpost :
      (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholePostReadout
        rate rewards C_star C_h u t z).1 =
      (RecordedQueueRun.step
        (ReferenceFirstLaunchNumericalCell.queueParameters rate)
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z))
        (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
          rate rewards C_star C_h u t z)).registers := by
    exact congrArg Prod.fst (Option.some.inj (hafterBridge.symm.trans hafter))
  have hprefix :
      ReferenceFirstCollectionCurrentRetainedGate.prefixReadout?
        rate rewards C_star C_h t z.val =
      some (ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
        (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
            rate rewards C_star C_h u t z))) := by
    change (ReferenceFirstCollectionCurrentRetainedGate.pastCells?
      rate rewards C_star C_h t z.val).map
        (fun L => ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout
          (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate) L)) = _
    rw [hpastBridge]
    rfl
  have hgate : z.val ∈ ReferenceFirstCollectionCurrentRetainedGate.G
        rate rewards C_star C_h u t ↔
      z ∈ ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
        rate rewards C_star C_h u t := by
    simp [ReferenceFirstCollectionCurrentRetainedGate.G,
      ReferenceFirstCollectionCurrentRetainedGate.H, hfirst, hprefix,
      ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming,
      ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.mem_E_iff_noIncomingOverflow]
  have hbacklog :
      ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
          rate rewards C_star C_h u t z.val =
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
          rate rewards C_star C_h u t z := by
    unfold ReferenceFirstCollectionCurrentQueueEnergy.weightedBacklog
      ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
    apply Finset.sum_congr rfl
    intro a ha
    have htheta :
        ReferenceFirstCollectionCurrentQueueEnergy.thetaMinus
            rate rewards C_star C_h u t a z.val =
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.thetaMinus
            rate rewards C_star C_h u t a z := by
      rw [hthetaMinus a]
      unfold ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.thetaMinus
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Aminus
      apply congrArg (fun w : Fin p.K → ℝ => ProductSetLaw.theta p.m w a)
      funext i
      simp [ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming,
        ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters,
        RecordedQueueRun.scoreWeight]
    have hbacklogArm :
        ReferenceFirstCollectionCurrentQueueReadout.bMinus
            rate rewards C_star C_h u t a z.val =
          ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.bMinus
            rate rewards C_star C_h u t a z := by
      rw [ReferenceFirstCollectionCurrentQueueReadout.bMinus,
        Set.indicator_of_mem hfirst, hbefore]
      simp [
        ReferenceFirstCollectionCurrentQueueReadout.normalizedReadoutBacklog,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.bMinus,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Aminus,
        ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming,
        ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout,
        ReferenceFirstCollectionRenewalIncomingQueueMeasurability.stateReadout,
        ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters,
        ReferenceFirstLaunchNumericalCell.queueParameters]
    rw [htheta, hbacklogArm]
  have hminusEq :
      ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
          rate rewards C_star C_h u t z =
        ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
          rate rewards C_star C_h z.val := by
    rw [ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus_eq_energyFromIncoming,
      hminus]
    simp only [ReferenceFirstCollectionRenewalIncomingQueuePrefix.incoming,
      ReferenceFirstCollectionRenewalIncomingQueuePrefix.incomingReadout,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters]
    have hweights :
        (fun i : Fin p.K =>
          ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
            rate i
            (RecordedQueueRun.run
              (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
                rate rewards C_star C_h u t z)).registers) =
        RecordedQueueRun.scoreWeight
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.run
            (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
              rate rewards C_star C_h u t z)) := by
      funext i
      simp [ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters,
        RecordedQueueRun.scoreWeight,
        ReferenceFirstLaunchNumericalCell.queueParameters,
        ScoreWeights.scoreWeight]
    rw [hweights]
    simp [ReferenceFirstLaunchNumericalCell.queueParameters]
  have hplusEq :
      ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z =
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z.val := by
    rw [ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus_eq_energyFromWholePost,
      hpost, hplus]
    simp only [ReferenceFirstCollectionRenewalIncomingQueueBounds.energyFromRegisters,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.thetaFromRegisters,
      ReferenceFirstCollectionRenewalIncomingQueueBounds.backlogFromRegisters]
    have hweights :
        (fun i : Fin p.K =>
          ReferenceFirstCollectionRenewalIncomingQueueBounds.weightFromRegisters
            rate i
            (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
                (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
                  rate rewards C_star C_h u t z))
              (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
                rate rewards C_star C_h u t z)).registers) =
        RecordedQueueRun.scoreWeight
          (ReferenceFirstLaunchNumericalCell.queueParameters rate)
          (RecordedQueueRun.step (ReferenceFirstLaunchNumericalCell.queueParameters rate)
            (RecordedQueueRun.run (ReferenceFirstLaunchNumericalCell.queueParameters rate)
              (ReferenceFirstCollectionRenewalIncomingQueuePrefix.pastCells
                rate rewards C_star C_h u t z))
            (ReferenceFirstCollectionRenewalSourceCurrentPrefix.wholeCell
              rate rewards C_star C_h u t z)) := by
      funext i
      rfl
    rw [hweights]
    simp [ReferenceFirstLaunchNumericalCell.queueParameters]
  have hcostEq :
      (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
          rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
            rate rewards C_star C_h u t) z =
        ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
          rate rewards C_star C_h z.val := by
    by_cases hz : z ∈
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
          rate rewards C_star C_h u t
    · have hg := hgate.mpr hz
      rw [Set.indicator_of_mem hz, ← hbacklog]
      simpa only [Set.indicator_of_mem hg] using hcallBacklog.symm
    · have hg : z.val ∉ ReferenceFirstCollectionCurrentRetainedGate.G
          rate rewards C_star C_h u t := mt hgate.mp hz
      rw [Set.indicator_of_notMem hz]
      have hzero := hcallBacklog
      rw [Set.indicator_of_notMem hg] at hzero
      exact hzero.symm
  exact ⟨hminusEq, hplusEq, hcostEq⟩

private theorem integral_cell_eq_restrict (u t : Fin p.T)
    (f : S → ℝ) (hf : Measurable f) :
    (∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t, f z.val ∂
      ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t) =
      ∫ z in ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t, f z ∂μ := by
  rw [← ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_map_val
    rate rewards C_star C_h u t]
  exact (integral_map measurable_subtype_coe.aemeasurable
    hf.aestronglyMeasurable).symm

private theorem sum_cell_integrals_eq_restricted
    (f : S → ℝ) (hf : Measurable f) (hfi : Integrable f μ)
    (g : ∀ u t : Fin p.T,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t → ℝ)
    (hgf : ∀ u t
      (z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t), g u t z = f z.val) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t, g u t z ∂
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t) =
      ∫ z in renewalCallEventUnion rate rewards C_star C_h, f z ∂μ := by
  classical
  have hunion : renewalCallEventUnion rate rewards C_star C_h =
      ⋃ a : Fin p.T × Fin p.T,
        ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h a.1 a.2 := by
    ext z
    simp only [renewalCallEventUnion, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨u, t, hz⟩
      exact ⟨(u, t), hz⟩
    · rintro ⟨a, hz⟩
      exact ⟨a.1, a.2, hz⟩
  have hcellMeas (a : Fin p.T × Fin p.T) :
      MeasurableSet
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h a.1 a.2) :=
    measurableSet_renewalCallEvent rate rewards C_star C_h a.1 a.2
  have hcellIntegrable (a : Fin p.T × Fin p.T) :
      IntegrableOn f
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h a.1 a.2) μ := hfi.integrableOn
  calc
    _ = ∑ a : Fin p.T × Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h a.1 a.2, g a.1 a.2 z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h a.1 a.2 := by
      rw [← Finset.univ_product_univ, Finset.sum_product]
    _ = ∑ a : Fin p.T × Fin p.T,
        ∫ z in ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h a.1 a.2, f z ∂μ := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_congr_ae (Filter.Eventually.of_forall (hgf a.1 a.2))]
      exact integral_cell_eq_restrict rate rewards C_star C_h a.1 a.2 f hf
    _ = ∫ z in renewalCallEventUnion rate rewards C_star C_h, f z ∂μ := by
      rw [hunion]
      exact (integral_iUnion_fintype hcellMeas
        (renewalCallEvents_pairwiseDisjoint rate rewards C_star C_h)
        hcellIntegrable).symm

/-- Exact finite transport of all incoming whole-renewal energies to the
original source, with the union charged once. -/
theorem integral_sum_Vminus_eq_restricted_callVMinus
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
          rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) =
      ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
          rate rewards C_star C_h z ∂μ := by
  apply sum_cell_integrals_eq_restricted rate rewards C_star C_h
    (ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus rate rewards C_star C_h)
  · exact ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_measurable
      rate rewards C_star C_h control0
  · exact ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
      rate rewards C_star C_h control0
  · intro u t z
    exact (wholeEnergyObservations_eq_callObservations rate rewards C_star C_h u t z).1

/-- Exact finite transport of whole-post energies after the same first-call
updates to the original source. -/
theorem integral_sum_VwholePlus_eq_restricted_callVPlus
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) =
      ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ := by
  apply sum_cell_integrals_eq_restricted rate rewards C_star C_h
    (ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus rate rewards C_star C_h)
  · exact ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_measurable
      rate rewards C_star C_h control0
  · exact ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_integrable
      rate rewards C_star C_h control0
  · intro u t z
    exact (wholeEnergyObservations_eq_callObservations rate rewards C_star C_h u t z).2.1

/-- Exact finite transport of the retained incoming backlog to the original
source. -/
theorem integral_sum_Bminus_eq_restricted_callWeightedBacklog
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
          rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
          rate rewards C_star C_h u t) z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) =
      ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
          rate rewards C_star C_h z ∂μ := by
  apply sum_cell_integrals_eq_restricted rate rewards C_star C_h
    (ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
      rate rewards C_star C_h)
  · exact ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_measurable
      rate rewards C_star C_h control0
  · exact ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_integrable
      rate rewards C_star C_h control0
  · intro u t z
    exact (wholeEnergyObservations_eq_callObservations rate rewards C_star C_h u t z).2.2

/-- Nonnegativity lets incoming energy pass from its exact restriction to the
whole original-source call observation. -/
theorem integral_sum_Vminus_le_callVMinus (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
          rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) ≤
      ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ]
      ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h :=
    Filter.Eventually.of_forall fun z =>
      ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_nonneg
        rate rewards C_star C_h z
  calc
    _ = ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
          rate rewards C_star C_h z ∂μ :=
      integral_sum_Vminus_eq_restricted_callVMinus rate rewards C_star C_h control0
    _ ≤ ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ∂μ :=
      setIntegral_le_integral
        (ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
          rate rewards C_star C_h control0) hnonneg

/-- Nonnegativity lets the same-update outgoing energy pass from its exact
restriction to the whole original-source call observation. -/
theorem integral_sum_VwholePlus_le_callVPlus (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
          rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) ≤
      ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ]
      ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h :=
    Filter.Eventually.of_forall fun z =>
      ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_nonneg
        rate rewards C_star C_h z
  calc
    _ = ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ :=
      integral_sum_VwholePlus_eq_restricted_callVPlus rate rewards C_star C_h control0
    _ ≤ ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ :=
      setIntegral_le_integral
        (ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus_integrable
          rate rewards C_star C_h control0) hnonneg

/-- The retained weighted backlog obeys the corresponding nonnegative
whole-source bound, with its original strict-past gate intact. -/
theorem integral_sum_Bminus_le_callWeightedBacklog (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.E
          rate rewards C_star C_h u t).indicator
          (ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Bminus
            rate rewards C_star C_h u t) z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) ≤
      ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
        rate rewards C_star C_h z ∂μ := by
  have hnonneg : 0 ≤ᵐ[μ]
      ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
        rate rewards C_star C_h :=
    Filter.Eventually.of_forall fun z =>
      ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_nonneg
        rate rewards C_star C_h z
  calc
    _ = ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
          rate rewards C_star C_h z ∂μ :=
      integral_sum_Bminus_eq_restricted_callWeightedBacklog
        rate rewards C_star C_h control0
    _ ≤ ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
        rate rewards C_star C_h z ∂μ :=
      setIntegral_le_integral
        (ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog_integrable
          rate rewards C_star C_h control0) hnonneg

/-- Incoming energy is paid once against the accepted original-source
pre-call terminal potential. -/
theorem integral_sum_Vminus_le_preCallPotential_terminal
    (control0 : TimeControl p) :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t,
        ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.Vminus
          rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t) ≤
      ∫ z, ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential
        rate rewards C_star C_h p.T z ∂μ := by
  let Phi := ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.oldPotential
    rate rewards C_star C_h
  have hphi := ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_regular
    rate rewards C_star C_h p.T (Nat.le_refl _)
  have hcall := ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus_integrable
    rate rewards C_star C_h control0
  have hrestricted : IntegrableOn (Phi p.T)
      (renewalCallEventUnion rate rewards C_star C_h) μ := hphi.2.integrableOn
  have hpoint : ∀ᵐ z ∂(sourceInputLaw p).restrict
      (renewalCallEventUnion rate rewards C_star C_h),
      ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
        rate rewards C_star C_h z ≤ Phi p.T z := by
    filter_upwards [] with z
    exact ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.callVMinus_le_preCallPotential_terminal
      rate rewards C_star C_h z
  have hlocal := integral_mono_ae hcall.integrableOn hrestricted hpoint
  have hnonneg : 0 ≤ᵐ[μ] Phi p.T :=
    Filter.Eventually.of_forall fun z =>
      ReferenceFirstCollectionPrecallWeightedBacklogBound.precallPotential_terminal_nonneg
        rate rewards C_star C_h z
  calc
    _ = ∫ z in renewalCallEventUnion rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVMinus
          rate rewards C_star C_h z ∂μ :=
      integral_sum_Vminus_eq_restricted_callVMinus rate rewards C_star C_h control0
    _ ≤ ∫ z in renewalCallEventUnion rate rewards C_star C_h, Phi p.T z ∂μ := hlocal
    _ ≤ ∫ z, Phi p.T z ∂μ := setIntegral_le_integral hphi.2 hnonneg

end Bandits.Support.ReferenceFirstCollectionRenewalWeightedEnergySourceTransport

end
