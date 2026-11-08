/-
Copyright (c) 2026 The Bandits Lean Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Bandits.Support.ReferenceFirstCollectionRenewalWeightedCalendarAccounting
public import Bandits.Support.ReferenceFirstCollectionRenewalWeightedEnergySourceTransport
public import Bandits.Support.ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Original-source continuation of the first-renewal weighted budget

The actual after-call observations are extended by zero from each unnormalized
renewal source cell and transported back to the same original source. Their
energy budget joins the already charged pre-call and first-call costs without
including the whole-date backlog a second time.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Classical
open Bandits.Support.ConstructorDimensions
open Bandits.Support.BootstrapPrivateRoundStreams (SourceInput sourceInputLaw)
open Bandits.Support.ActualInitializationPhysicalStep (GridRewardTable)
open Bandits.Support.ContinuousLearningRows (TimeControl)

namespace Bandits.Support.ReferenceFirstCollectionRenewalOriginalWeightedContinuation

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

/-- Extend a function on a measurable source subtype by zero, retaining the
literal source value on the subtype. -/
def zeroExtendCell {α : Type*} [MeasurableSpace α] (E : Set α)
    (f : {x // x ∈ E} → ℝ) : α → ℝ :=
  Function.extend Subtype.val f (fun _ => 0)

private theorem zeroExtendCell_eq_indicator {α : Type*} [MeasurableSpace α]
    (E : Set α) (f : {x // x ∈ E} → ℝ) (x : α) :
    zeroExtendCell E f x = E.indicator (zeroExtendCell E f) x := by
  classical
  by_cases hx : x ∈ E
  · simp only [Set.indicator_of_mem hx]
  · have hno : ¬ ∃ y : {x // x ∈ E}, (y : α) = x := by
      rintro ⟨y, hy⟩
      exact hx (hy ▸ y.property)
    simp [zeroExtendCell, Set.indicator_of_notMem hx, Function.extend_apply', hno]

private theorem zeroExtendCell_measurable {α : Type*} [MeasurableSpace α]
    (E : Set α) (hE : MeasurableSet E) (f : {x // x ∈ E} → ℝ)
    (hf : Measurable f) : Measurable (zeroExtendCell E f) :=
  (MeasurableEmbedding.subtype_coe hE).measurable_extend hf measurable_const

private theorem zeroExtendCell_integrable {α : Type*} [MeasurableSpace α]
    (E : Set α) (hE : MeasurableSet E) (f : {x // x ∈ E} → ℝ)
    (mu0 : Measure α)
    (hf : Integrable f (mu0.comap (Subtype.val : {x // x ∈ E} → α))) :
    Integrable (zeroExtendCell E f) mu0 := by
  have hcomp : Integrable
      (fun x : {x // x ∈ E} => zeroExtendCell E f x.val)
      (mu0.comap (Subtype.val : {x // x ∈ E} → α)) := by
    have heq : (fun x : {x // x ∈ E} => zeroExtendCell E f x.val) = f := by
      funext x
      exact Subtype.val_injective.extend_apply f (fun _ => 0) x
    rw [heq]
    exact hf
  have hOn : IntegrableOn (zeroExtendCell E f) E mu0 :=
    (integrableOn_iff_comap_subtypeVal hE).2 hcomp
  have heq : zeroExtendCell E f = E.indicator (zeroExtendCell E f) := by
    funext x
    exact zeroExtendCell_eq_indicator E f x
  rw [heq]
  exact (integrable_indicator_iff hE).2 hOn

private theorem integral_zeroExtendCell {α : Type*} [MeasurableSpace α]
    (E : Set α) (hE : MeasurableSet E) (f : {x // x ∈ E} → ℝ)
    (mu0 : Measure α) (hf : Measurable (zeroExtendCell E f)) :
    (∫ x, zeroExtendCell E f x ∂mu0) =
      ∫ x : {x // x ∈ E}, f x ∂mu0.comap (Subtype.val : {x // x ∈ E} → α) := by
  have heq : zeroExtendCell E f = E.indicator (zeroExtendCell E f) := by
    funext x
    exact zeroExtendCell_eq_indicator E f x
  rw [heq, integral_indicator hE, ← map_comap_subtype_coe hE]
  calc
    _ = ∫ x : {x // x ∈ E}, zeroExtendCell E f x.val
        ∂mu0.comap (Subtype.val : {x // x ∈ E} → α) := by
      exact integral_map measurable_subtype_coe.aemeasurable
        hf.aestronglyMeasurable
    _ = ∫ x : {x // x ∈ E}, f x
        ∂mu0.comap (Subtype.val : {x // x ∈ E} → α) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        Subtype.val_injective.extend_apply f (fun _ => 0) x

private theorem integral_doubleZeroExtend
    (f : ∀ u t : Fin p.T,
      ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t → ℝ)
    (hf : ∀ u t, Measurable (f u t))
    (hfi : ∀ u t, Integrable (f u t)
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
        rate rewards C_star C_h u t)) :
    (∫ z : S, ∑ u : Fin p.T, ∑ t : Fin p.T,
      zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) (f u t) z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t, f u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t := by
  have hcellMeas (u t : Fin p.T) :
      Measurable (zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) (f u t)) :=
    zeroExtendCell_measurable _
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t) (f u t) (hf u t)
  have hcellInt (u t : Fin p.T) :
      Integrable (zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t) (f u t)) μ := by
    exact zeroExtendCell_integrable _
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
        rate rewards C_star C_h u t) (f u t) μ
      (hfi u t)
  calc
    _ = ∑ u : Fin p.T, ∫ z : S, ∑ t : Fin p.T,
        zeroExtendCell
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
            rate rewards C_star C_h u t) (f u t) z ∂μ := by
      exact integral_finsetSum Finset.univ (fun u hu =>
        integrable_finsetSum Finset.univ fun t ht => hcellInt u t)
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : S, zeroExtendCell
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
            rate rewards C_star C_h u t) (f u t) z ∂μ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact integral_finsetSum Finset.univ (fun t ht => hcellInt u t)
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t, f u t z ∂
            ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro t ht
      have hcell := integral_zeroExtendCell
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
          rate rewards C_star C_h u t)
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
          rate rewards C_star C_h u t)
        (f u t) μ (hcellMeas u t)
      simpa only [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw] using hcell

/-- The original-source zero extension of the actual after-call backlog on
each first-call renewal cell, summed over all cells. -/
def originalAfterCallBacklog (z : S) : ℝ :=
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    zeroExtendCell
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t)
      (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t) z

/-- The original-source zero extension of the actual terminal-energy
observation, summed over all first-call renewal cells. -/
def originalTerminalEnergy (z : S) : ℝ :=
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    zeroExtendCell
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t)
      (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
        rate rewards C_star C_h u t) z

/-- The original-source zero extension of the actual support-loss
observation, summed over all first-call renewal cells. -/
def originalSupportLoss (z : S) : ℝ :=
  ∑ u : Fin p.T, ∑ t : Fin p.T,
    zeroExtendCell
      (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
        rate rewards C_star C_h u t)
      (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
        rate rewards C_star C_h u t) z

/-- The retained live, old, and actual call backlog cost already charged by
the pre-call/first-call join. -/
def originalPreCallWeightedCost (z : S) : ℝ :=
  (∑ t : Fin p.T,
      (ReferenceFirstLiveOriginalCalendarWeightedBacklogBound.retainedWeightedBacklogCost
          rate rewards C_star C_h t z +
        ReferenceFirstCollectionOldConditionalWeightedEnergyDrift.costOld
          rate rewards C_star C_h t z)) +
    ReferenceFirstCollectionActualCallWeightedEnergy.callWeightedBacklog
      rate rewards C_star C_h z

theorem originalAfterCallBacklog_integrable
    (control0 : TimeControl p) : Integrable (originalAfterCallBacklog rate rewards C_star C_h) μ := by
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable _
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
      rate rewards C_star C_h u t) (sourceInputLaw p)
    (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog_integrable
      rate rewards C_star C_h u t control0)

theorem originalAfterCallBacklog_integral
    (control0 : TimeControl p) :
    (∫ z : S, originalAfterCallBacklog rate rewards C_star C_h z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
  simpa only [originalAfterCallBacklog] using
    integral_doubleZeroExtend rate rewards C_star C_h
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t)
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog_measurable
        rate rewards C_star C_h u t control0)
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog_integrable
        rate rewards C_star C_h u t control0)

theorem originalTerminalEnergy_integrable
    (control0 : TimeControl p) : Integrable (originalTerminalEnergy rate rewards C_star C_h) μ := by
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable _
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
      rate rewards C_star C_h u t) (sourceInputLaw p)
    (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy_integrable
      rate rewards C_star C_h u t control0)

theorem originalTerminalEnergy_integral
    (control0 : TimeControl p) :
    (∫ z : S, originalTerminalEnergy rate rewards C_star C_h z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
  simpa only [originalTerminalEnergy] using
    integral_doubleZeroExtend rate rewards C_star C_h
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
        rate rewards C_star C_h u t)
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy_measurable
        rate rewards C_star C_h u t control0)
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy_integrable
        rate rewards C_star C_h u t control0)

theorem originalSupportLoss_integrable
    (control0 : TimeControl p) : Integrable (originalSupportLoss rate rewards C_star C_h) μ := by
  apply integrable_finsetSum Finset.univ
  intro u hu
  apply integrable_finsetSum Finset.univ
  intro t ht
  exact zeroExtendCell_integrable _
    (ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h u t)
    (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
      rate rewards C_star C_h u t) (sourceInputLaw p)
    (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_integrable
      rate rewards C_star C_h u t control0)

theorem originalSupportLoss_integral
    (control0 : TimeControl p) :
    (∫ z : S, originalSupportLoss rate rewards C_star C_h z ∂μ) =
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t := by
  simpa only [originalSupportLoss] using
    integral_doubleZeroExtend rate rewards C_star C_h
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
        rate rewards C_star C_h u t)
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_measurable
        rate rewards C_star C_h u t control0)
      (fun u t => ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_integrable
        rate rewards C_star C_h u t control0)

/-- The total after-call gate mass is bounded by the horizon using the actual
source inclusion and pairwise-disjoint first-call renewal cells. -/
theorem afterCallGateMass_sum_le_horizon :
    (∑ u : Fin p.T, ∑ t : Fin p.T,
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
        rate rewards C_star C_h u t) ≤ (p.T : ℝ) := by
  let : IsProbabilityMeasure (sourceInputLaw p) :=
    BootstrapPrivateRoundStreams.sourceInputLaw_probability p
  let E : Fin p.T × Fin p.T → Set S := fun a =>
    ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h a.1 a.2
  have hUnion :
      ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
          rate rewards C_star C_h = ⋃ a : Fin p.T × Fin p.T, E a := by
    ext z
    simp only [ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion,
      Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨u, t, hz⟩
      exact ⟨(u, t), hz⟩
    · rintro ⟨a, hz⟩
      exact ⟨a.1, a.2, hz⟩
  have hPair : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    exact ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEvents_disjoint
      rate rewards C_star C_h a.1 a.2 b.1 b.2 hab
  have hMeas (a : Fin p.T × Fin p.T) : MeasurableSet (E a) :=
    ReferenceFirstCollectionRenewalAuxiliaryLaw.measurableSet_renewalCallEvent
      rate rewards C_star C_h a.1 a.2
  have hCellMass :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
          rate rewards C_star C_h u t).real Set.univ) =
        (sourceInputLaw p).real (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
          rate rewards C_star C_h) := by
    calc
      _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
          (sourceInputLaw p).real
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
              rate rewards C_star C_h u t) := by
        apply Finset.sum_congr rfl
        intro u hu
        apply Finset.sum_congr rfl
        intro t ht
        change ENNReal.toReal
            ((ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
              rate rewards C_star C_h u t) Set.univ) =
          ENNReal.toReal ((sourceInputLaw p)
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
              rate rewards C_star C_h u t))
        rw [ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw_univ]
      _ = ∑ a : Fin p.T × Fin p.T, (sourceInputLaw p).real (E a) := by
        rw [← Finset.univ_product_univ, Finset.sum_product]
      _ = (sourceInputLaw p).real
          (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
            rate rewards C_star C_h) := by
        have hmeasure :
            (sourceInputLaw p).real (⋃ a : Fin p.T × Fin p.T, E a) =
              ∑ a : Fin p.T × Fin p.T, (sourceInputLaw p).real (E a) := by
          exact measureReal_iUnion_fintype hPair hMeas
        rw [hUnion]
        exact hmeasure.symm
  have hUnionMass :
      (sourceInputLaw p).real (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
        rate rewards C_star C_h) ≤ 1 := by
    calc
      _ ≤ (sourceInputLaw p).real Set.univ :=
        measureReal_mono (Set.subset_univ _) (by finiteness)
      _ = 1 := by simp
  have hEach (u t : Fin p.T) :
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
          rate rewards C_star C_h u t ≤
        (p.T : ℝ) *
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real Set.univ := by
    calc
      _ ≤ ((p.T - (t.val + 1) : ℕ) : ℝ) *
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real Set.univ :=
        ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass_le_horizon
          rate rewards C_star C_h u t
      _ ≤ (p.T : ℝ) *
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real Set.univ :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast Nat.sub_le p.T (t.val + 1)) measureReal_nonneg
  calc
    _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
        (p.T : ℝ) *
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real Set.univ := by
      apply Finset.sum_le_sum
      intro u hu
      apply Finset.sum_le_sum
      intro t ht
      exact hEach u t
    _ = (p.T : ℝ) *
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t).real Set.univ := by
      simp only [← Finset.mul_sum]
    _ = (p.T : ℝ) * (sourceInputLaw p).real
        (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
          rate rewards C_star C_h) := by rw [hCellMass]
    _ ≤ (p.T : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hUnionMass (Nat.cast_nonneg p.T)
    _ = (p.T : ℝ) := by ring

/-- Summing the actual strictly-after-call budgets gives the exact restriction
of the same outgoing first-call energy to the first-call renewal event union. -/
theorem afterCall_weighted_calendar_accounting_sum
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t) +
      ∫ z in ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.renewalCallEventUnion
        rate rewards C_star C_h,
        ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ := by
  let B : Fin p.T → Fin p.T → ℝ := fun u t =>
    ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
        rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t
  let Q : Fin p.T → Fin p.T → ℝ := fun u t =>
    ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
        rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t
  let L : Fin p.T → Fin p.T → ℝ := fun u t =>
    ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
        rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t
  let G : Fin p.T → Fin p.T → ℝ :=
    ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
      rate rewards C_star C_h
  let W : Fin p.T → Fin p.T → ℝ := fun u t =>
    ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
      rate rewards C_star C_h u t,
      ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
        rate rewards C_star C_h u t z ∂
          ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
            rate rewards C_star C_h u t
  have hsum :
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ((11 / 2 : ℝ) * B u t + Q u t + L u t)) ≤
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * G u t + W u t) := by
    apply Finset.sum_le_sum
    intro u hu
    apply Finset.sum_le_sum
    intro t ht
    simpa only [B, Q, L, G, W] using
      ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCall_weighted_calendar_accounting
        rate rewards C_star C_h u t control0
  calc
    _ = ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((11 / 2 : ℝ) *
            ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
              rate rewards C_star C_h u t,
              ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
                rate rewards C_star C_h u t z ∂
                  ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                    rate rewards C_star C_h u t +
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t +
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ ∑ u : Fin p.T, ∑ t : Fin p.T,
        ((CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
              rate rewards C_star C_h u t +
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
            ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
              rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t) := by
      simpa only [B, Q, L, G, W] using hsum
    _ = (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
          (∑ u : Fin p.T, ∑ t : Fin p.T,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
              rate rewards C_star C_h u t) +
        ∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
            ReferenceFirstCollectionRenewalWholeSourceWeightedEnergyDrift.VwholePlus
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.integral_sum_VwholePlus_eq_restricted_callVPlus
        rate rewards C_star C_h control0]

/-- The whole-source version follows by retaining the exact restriction above
and using nonnegativity of the actual outgoing call energy. -/
theorem afterCall_weighted_calendar_accounting_sum_wholeSource
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
            rate rewards C_star C_h u t,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallBacklog
              rate rewards C_star C_h u t z ∂
                ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                  rate rewards C_star C_h u t) +
      (∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t) +
      ∑ u : Fin p.T, ∑ t : Fin p.T,
        ∫ z : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
          rate rewards C_star C_h u t,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t z ∂
              ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalSourceLaw
                rate rewards C_star C_h u t ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        (∑ u : Fin p.T, ∑ t : Fin p.T,
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
            rate rewards C_star C_h u t) +
      ∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
        rate rewards C_star C_h z ∂μ := by
  have h := afterCall_weighted_calendar_accounting_sum rate rewards C_star C_h control0
  rw [← ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.integral_sum_VwholePlus_eq_restricted_callVPlus
    rate rewards C_star C_h control0] at h
  exact h.trans (add_le_add le_rfl
    (ReferenceFirstCollectionRenewalWeightedEnergySourceTransport.integral_sum_VwholePlus_le_callVPlus
      rate rewards C_star C_h control0))

/-- The original-source after-call readouts join the pre-call and first-call
weighted energy on their actual total after-call mass. -/
theorem original_preCall_afterCall_weighted_energy_join
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ((∫ z : S, originalPreCallWeightedCost rate rewards C_star C_h z ∂μ) +
          ∫ z : S, originalAfterCallBacklog rate rewards C_star C_h z ∂μ) +
      (∫ z : S, originalTerminalEnergy rate rewards C_star C_h z ∂μ) +
      ∫ z : S, originalSupportLoss rate rewards C_star C_h z ∂μ ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ((p.T : ℝ) +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
              rate rewards C_star C_h u t) := by
  have hpre :=
    ReferenceFirstCollectionPrecallActualCallWeightedEnergyJoin.integral_preCall_firstCall_weighted_energy_join
      rate rewards C_star C_h control0
  have hafter := afterCall_weighted_calendar_accounting_sum_wholeSource
    rate rewards C_star C_h control0
  rw [← originalAfterCallBacklog_integral rate rewards C_star C_h control0,
    ← originalTerminalEnergy_integral rate rewards C_star C_h control0,
    ← originalSupportLoss_integral rate rewards C_star C_h control0] at hafter
  have hpre' :
      (∫ z, ReferenceFirstCollectionActualCallWeightedEnergy.callVPlus
          rate rewards C_star C_h z ∂μ) +
        (11 / 2 : ℝ) *
          ∫ z, originalPreCallWeightedCost rate rewards C_star C_h z ∂μ ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
    simpa only [originalPreCallWeightedCost] using hpre
  have hadd := add_le_add hafter hpre'
  have hcancel :
      (11 / 2 : ℝ) *
          ((∫ z : S, originalPreCallWeightedCost rate rewards C_star C_h z ∂μ) +
            ∫ z : S, originalAfterCallBacklog rate rewards C_star C_h z ∂μ) +
        ∫ z : S, originalTerminalEnergy rate rewards C_star C_h z ∂μ +
        ∫ z : S, originalSupportLoss rate rewards C_star C_h z ∂μ ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                rate rewards C_star C_h u t) +
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
    linarith only [hadd]
  calc
    _ ≤
        (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
            (∑ u : Fin p.T, ∑ t : Fin p.T,
              ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
                rate rewards C_star C_h u t) +
          (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := hcancel
    _ = _ := by ring

/-- The same combined bound has a coarse two-horizon form after the actual
after-call mass has been shown to be at most `T`. -/
theorem original_preCall_afterCall_weighted_energy_join_horizon
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ((∫ z : S, originalPreCallWeightedCost rate rewards C_star C_h z ∂μ) +
          ∫ z : S, originalAfterCallBacklog rate rewards C_star C_h z ∂μ) +
      (∫ z : S, originalTerminalEnergy rate rewards C_star C_h z ∂μ) +
      ∫ z : S, originalSupportLoss rate rewards C_star C_h z ∂μ ≤
      2 * (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) * (p.T : ℝ) := by
  have hj := original_preCall_afterCall_weighted_energy_join rate rewards C_star C_h control0
  have hm := afterCallGateMass_sum_le_horizon rate rewards C_star C_h
  have hc := ReferenceFirstCollectionRenewalWeightedCalendarAccounting.calendarCost_nonneg
    (p := p)
  calc
    _ ≤ (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ((p.T : ℝ) + (p.T : ℝ)) :=
      hj.trans (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl (p.T : ℝ)) hm) hc)
    _ = _ := by ring

/-- The original-source after-call terminal energy is nonnegative. -/
theorem originalTerminalEnergy_integral_nonneg
    :
    0 ≤ ∫ z : S, originalTerminalEnergy rate rewards C_star C_h z ∂μ := by
  apply integral_nonneg
  intro z
  unfold originalTerminalEnergy
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  by_cases hz : z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h u t
  · have hread :
        zeroExtendCell
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
              rate rewards C_star C_h u t)
            (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
              rate rewards C_star C_h u t) z =
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
            rate rewards C_star C_h u t ⟨z, hz⟩ := by
      change Function.extend Subtype.val
        (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
          rate rewards C_star C_h u t) (fun _ => 0) z = _
      calc
        _ = Function.extend Subtype.val
            (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
              rate rewards C_star C_h u t) (fun _ => 0)
              (⟨z, hz⟩ : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
                rate rewards C_star C_h u t).val := by rfl
        _ = _ := Subtype.val_injective.extend_apply _ _ _
    rw [hread]
    exact ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy_nonneg
      rate rewards C_star C_h u t ⟨z, hz⟩
  · have hno : ¬ ∃ y : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t, y.val = z := by
      rintro ⟨y, hy⟩
      exact hz (hy ▸ y.property)
    change 0 ≤ Function.extend Subtype.val
      (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.terminalEnergy
        rate rewards C_star C_h u t) (fun _ => 0) z
    simp [Function.extend_apply', hno]

/-- The original-source after-call support loss is nonnegative. -/
theorem originalSupportLoss_integral_nonneg
    :
    0 ≤ ∫ z : S, originalSupportLoss rate rewards C_star C_h z ∂μ := by
  apply integral_nonneg
  intro z
  unfold originalSupportLoss
  apply Finset.sum_nonneg
  intro u hu
  apply Finset.sum_nonneg
  intro t ht
  by_cases hz : z ∈ ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
      rate rewards C_star C_h u t
  · have hread :
        zeroExtendCell
            (ReferenceFirstCollectionRenewalAuxiliaryLaw.renewalCallEvent
              rate rewards C_star C_h u t)
            (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
              rate rewards C_star C_h u t) z =
          ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
            rate rewards C_star C_h u t ⟨z, hz⟩ := by
      change Function.extend Subtype.val
        (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
          rate rewards C_star C_h u t) (fun _ => 0) z = _
      calc
        _ = Function.extend Subtype.val
            (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
              rate rewards C_star C_h u t) (fun _ => 0)
              (⟨z, hz⟩ : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
                rate rewards C_star C_h u t).val := by rfl
        _ = _ := Subtype.val_injective.extend_apply _ _ _
    rw [hread]
    exact ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss_nonneg
      rate rewards C_star C_h u t ⟨z, hz⟩
  · have hno : ¬ ∃ y : ReferenceFirstCollectionRenewalAuxiliaryLaw.RenewalCallSource
        rate rewards C_star C_h u t, y.val = z := by
      rintro ⟨y, hy⟩
      exact hz (hy ▸ y.property)
    change 0 ≤ Function.extend Subtype.val
      (ReferenceFirstCollectionRenewalWeightedCalendarAccounting.supportLoss
        rate rewards C_star C_h u t) (fun _ => 0) z
    simp [Function.extend_apply', hno]

/-- Dropping the now-proved nonnegative terminal and support-loss integrals
gives the separate original-source backlog corollary. -/
theorem original_preCall_afterCall_weighted_backlog_join
    (control0 : TimeControl p) :
    (11 / 2 : ℝ) *
        ((∫ z : S, originalPreCallWeightedCost rate rewards C_star C_h z ∂μ) +
          ∫ z : S, originalAfterCallBacklog rate rewards C_star C_h z ∂μ) ≤
      (CanonicalRecordingRates.R p + (33 / 2 : ℝ) * (p.m : ℝ)) *
        ((p.T : ℝ) +
          ∑ u : Fin p.T, ∑ t : Fin p.T,
            ReferenceFirstCollectionRenewalWeightedCalendarAccounting.afterCallGateMass
              rate rewards C_star C_h u t) := by
  have h := original_preCall_afterCall_weighted_energy_join rate rewards C_star C_h control0
  have hterm := originalTerminalEnergy_integral_nonneg rate rewards C_star C_h
  have hloss := originalSupportLoss_integral_nonneg rate rewards C_star C_h
  linarith only [h, hterm, hloss]

end Bandits.Support.ReferenceFirstCollectionRenewalOriginalWeightedContinuation

end
